///////////////////////////////////////////////////////////////
//  Copyright 2020 John Maddock. Distributed under the Boost
//  Software License, Version 1.0. (See accompanying file
//  LICENSE_1_0.txt or copy at https://www.boost.org/LICENSE_1_0.txt

#ifndef BOOST_MATH_NDOUBLE_HPP
#define BOOST_MATH_NDOUBLE_HPP

#include <array>
#include <vector>
#include <numeric>

#include <boost/mpl/list.hpp>
#include <boost/mp11/utility.hpp>

#include <boost/multiprecision/traits/std_integer_traits.hpp>
#include <boost/multiprecision/number.hpp>
#include <boost/container_hash/hash.hpp>

#include <boost/geometry/extensions/generic_robust_predicates/strategies/cartesian/detail/expansion_arithmetic.hpp>

namespace boost {
namespace multiprecision {
namespace backends {

/*
This header defines one type - ndouble - which declares the minimal
interface to qualify as a backend for class number.  In addition you'll find
optional interfaces declared commented out - you can enable these or not as
needed.

The process of writing a new backend for class number then reduces to a search
and replace to change the name of this class to something meaningful, followed
by "filling in the blanks" of each of the methods.

NOTE: all of the methods shown below are simple declarations, be sure to make them
inline, constexpr and/or noexcept as appropriate - as these annotations propogate
upwards to operations on number<>'s.

If the backend is to be itself a template, thn you will have rather more editing to
do to add all the "template<...>" prefixes to the functions.

*/
template <int Length>
using always_ze_policy = boost::mp11::mp_bool<true>;


template <int n>
struct ndouble
{
   static_assert( n >= 2 );
public:
   std::array<double, n> m_components;
   typename std::array<double, n>::iterator m_end;

   using const_it = typename std::array<double, n>::const_iterator;
   //
   // Each backend need to declare 3 type lists which declare the types
   // with which this can interoperate.  These lists must at least contain
   // the widest type in each category - so "long long" must be the final
   // type in the signed_types list for example.  Any narrower types if not
   // present in the list will get promoted to the next wider type that is
   // in the list whenever mixed arithmetic involving that type is encountered.
   //
   typedef std::tuple</*signed char, short, int, long,*/ long long>                                     signed_types;
   typedef std::tuple</* unsigned char, unsigned short, unsigned, unsigned long,*/ unsigned long long>  unsigned_types;
   typedef std::tuple</*float,*/ double, long double>                                                   float_types;
   //
   // This typedef is only required if this is a floating point type, it is the type
   // which holds the exponent:
   //
   typedef int                                                         exponent_type;

   // We must have a default constructor:
   inline ndouble()
   {
        m_components[0];
        m_end = m_components.begin() + 1;
   }
   inline ndouble(const ndouble& o) : m_components(o.m_components),
                                      m_end(m_components.begin() + std::distance<const_it>(o.m_components.begin(), o.m_end)){
                                      }
   inline ndouble(ndouble&& o) : m_components(std::move(o.m_components)),
                                 m_end(m_components.begin() + std::distance(o.m_components.begin(), o.m_end)) {
                                 }

   // Optional constructors, we can make this type slightly more efficient
   // by providing constructors from any type we can handle natively.
   // These will also cause number<> to be implicitly constructible
   // from these types unless we make such constructors explicit.
   //
   // ndouble(int o);  // If there's an efficient initialisation from int for example.

   //
   // In the absense of converting constructors, operator= takes the strain.
   // In addition to the usual suspects, there must be one operator= for each type
   // listed in signed_types, unsigned_types, and float_types plus a string constructor.
   //
   inline ndouble& operator=(const ndouble& o)
   {
       m_components = o.m_components;
       auto length = std::distance<const_it>(o.m_components.begin(), o.m_end);
       m_end = m_components.begin() + length;
       return *this;
   }
   inline ndouble& operator=(ndouble&& o)
   {
       auto length = std::distance(o.m_components.begin(), o.m_end);
       m_components = std::move(o.m_components);
       m_end = m_components.begin() + length;
       return *this;
   }
   inline ndouble& operator=(unsigned long long i)
   {
       uint_fast64_t splitter = (static_cast<uint_fast64_t>(1) << static_cast<uint_fast64_t>(32));
       double a = i % splitter;
       double b = (i / splitter) * splitter;
       double x = a + b;
       double y = boost::geometry::detail::generic_robust_predicates::fast_two_sum_tail(a, b, x);
       m_components[1] = x;
       m_components[0] = y;
       m_end = m_components.begin() + 2;
       return *this;
   }
   inline ndouble& operator=(long long i)
   {
       int_fast64_t splitter = (static_cast<int_fast64_t>(1) << static_cast<int_fast64_t>(32));
       double a = i % splitter;
       double b = (i / splitter) * splitter;
       double x = a + b;
       double y = boost::geometry::detail::generic_robust_predicates::fast_two_sum_tail(a, b, x);
       m_components[1] = x;
       m_components[0] = y;
       m_end = m_components.begin() + 2;
       return *this;
   }

    inline ndouble& operator=(long double i)
    {
       auto split = boost::geometry::detail::generic_robust_predicates::split(i);
       double x = static_cast<double>(split[0]);
       double y = static_cast<double>(split[1]);
       m_components[1] = x;
       m_components[0] = y;
       m_end = m_components.begin() + 2;
       return *this;       
    }
    inline ndouble& operator=(double i)
    {
       m_components[0] = i;
       m_end = m_components.begin() + 1;
       return *this;       
    }
   inline ndouble& operator=(const char* s)
   {
       *this = boost::lexical_cast<long double>(s); //loses more precision than necessary?
       return *this;
   }

   inline void swap(ndouble& o)
   {
       std::swap(m_components, o.m_components);
   }
   std::string str(std::streamsize digits, std::ios_base::fmtflags f) const
   {
      std::stringstream ss;
      ss.flags(f);
      if (digits)
         ss.precision(digits);
      else
         ss.precision(std::numeric_limits<double>::digits10 + 3);
      auto approx = std::accumulate<typename std::array<double, n>::const_iterator>(m_components.begin(), m_end, 0.);
      ss << approx /*<< "\t"*/;
      //for(auto it = m_components.begin(); it != m_end; ++it)
      //    ss << " " << *it << ", ";
      //ss << m_components[0] << ", " << m_components[1] << ", " << m_components[2] << ", " << m_components[3];
      std::string s = ss.str();
      return s;
   }

   inline void negate()
   {
       for(auto c_it = m_components.begin(); c_it != m_end; ++c_it)
           *c_it = -*c_it;
   }
   int         compare(ndouble o) const
   {
       o.negate();
       std::array<double, 1> diff;
       auto diff_end = boost::geometry::detail::generic_robust_predicates::
           fast_expansion_sum_not_inplace
                                         <
                                            true,
                                            true,
                                            const_it,
                                            const_it
                                         >
                                         (m_components.begin(),
                                          m_end,
                                          o.m_components.begin(),
                                          o.m_end,
                                          diff.begin(),
                                          diff.end());
       auto diff_sig = *(diff_end - 1);
       if(diff_sig > 0) return 1;
       else if(diff_sig < 0) return -1;
       else return 0;
   }
   //
   // Comparison with arithmetic types, default just constructs a temporary:
   //
   template <class A>
   typename std::enable_if<boost::multiprecision::detail::is_arithmetic<A>::value, int>::type compare(A i) const
   {
      ndouble t;
      t = i;  //  Note: construct directly from i if supported.
      return compare(t);
   }
};

//
// Required non-members:
//
template <int n>
void eval_add(ndouble<n>& a, const ndouble<n>& b)
{
    using namespace boost::geometry::detail::generic_robust_predicates;

    std::array<double, 2 * n> exact;
    auto end = expansion_plus
        <
            n,
            n,
            false,
            always_ze_policy,
            default_fast_expansion_sum_policy,
            false,
            typename std::array<double, n>::const_iterator,
            typename std::array<double, n>::const_iterator
        >
                             (a.m_components.begin(), a.m_end,
                              b.m_components.begin(), b.m_end,
                              exact.begin(), exact.end());
    end = compress(exact.begin(), end);
    auto length = std::min(std::distance(exact.begin(), end), (long)n);
    for(int i = 0; i < length; ++i)
        a.m_components[i] = *(end - length + i);
    a.m_end = a.m_components.begin() + length;
}

template <int n>
void eval_subtract(ndouble<n>& a, const ndouble<n>& b)
{
    using namespace boost::geometry::detail::generic_robust_predicates;
    std::array<double, 2 * n> exact;
    auto end = expansion_minus
        <
            n,
            n,
            false,
            false,
            always_ze_policy,
            default_fast_expansion_sum_policy,
            false,
            typename ndouble<n>::const_it,
            typename ndouble<n>::const_it
        >
                              (a.m_components.begin(), a.m_end,
                               b.m_components.begin(), b.m_end,
                               exact.begin(), exact.end());
    end = compress(exact.begin(), end);
    auto length = std::min(std::distance(exact.begin(), end), (long)n);
    for(int i = 0; i < length; ++i)
        a.m_components[i] = *(end - length + i);
    a.m_end = a.m_components.begin() + length;
}

template <int n>
void eval_multiply(ndouble<n>& a, const ndouble<n>& b)
{
   using namespace boost::geometry::detail::generic_robust_predicates;
    std::array<double, 2 * n * n> exact;
    auto end = expansion_times
        <
            n,
            n,
            false,
            always_ze_policy,
            default_fast_expansion_sum_policy,
            false,
            typename std::array<double, n>::const_iterator,
            typename std::array<double, n>::const_iterator
        >(a.m_components.begin(), a.m_end,
          b.m_components.begin(), b.m_end,
          exact.begin(), exact.end());
    end = compress(exact.begin(), end);
    auto length = std::min(std::distance(exact.begin(), end), (long)n);
    for(int i = 0; i < length; ++i)
        a.m_components[i] = *(end - length + i);
    a.m_end = a.m_components.begin() + length;
}

template <int n>
void eval_divide(ndouble<n>& a, const ndouble<n>& b)
{
    using namespace boost::geometry::detail::generic_robust_predicates;
    int bsig = std::distance<typename ndouble<n>::const_it>(b.m_components.begin(), b.m_end) - 1;
    while(b.m_components[bsig] == 0. && bsig > 0)
    {
        bsig--;
    }
    if(bsig == -1)
    {
        a.m_components[0] = INFINITY;
        a.m_end = a.m_components.begin() + 1;
        return;
    }
    std::array<double, n> q;
    std::array<double, 2 * n> f;
    std::array<double, n> r;
    std::array<double, 3 * n> rf;
    std::copy(a.m_components.begin(), a.m_end, r.begin());
    auto r_end = r.begin() + std::distance(a.m_components.begin(), a.m_end);
    q[0] = *(a.m_end - 1) / b.m_components[bsig];
    auto qend = q.begin() + 1;
    auto Q = q[0];
    for(int i = n - 2; i >= 0; --i)
    {
        auto end = expansion_times
            <
                n,
                1,
                false,
                always_ze_policy,
                default_fast_expansion_sum_policy,
                false
            >(b.m_components.begin(),
              b.m_components.begin() + bsig + 1,
              Q,
              f.begin(),
              f.end());
        end = compress(f.begin(), end);
        end = expansion_minus<n, 2*n, false, false>(
                r.begin(),
                r_end,
                f.begin(),
                end,
                rf.begin(),
                rf.end());
        end = compress(rf.begin(), end);
        auto length = std::min(std::distance(rf.begin(), end), (long)n);
        for(int j = 0; j < length; ++j)
        {
            r[j] = rf[j];
        }
        r_end = r.begin() + length;
        Q = *(r_end - 1) / b.m_components[bsig];
        assert(qend != q.end());
        qend = grow_expansion<true>(q.begin(), qend, Q, q.begin(), qend + 1);
    }
    auto end = compress(q.begin(), qend);
    auto length = std::min(std::distance(q.begin(), end),(long) n);
    for(int i = 0; i < length; ++i)
        a.m_components[i] = *(end - length + i);
    a.m_end = a.m_components.begin() + length;
}

//
// Conversions: must include at least unsigned long long, long long and long double.
// Everything else is entirely optional:
//
template <int n>
void eval_convert_to(unsigned long long* result, const ndouble<n>& backend)
{
    *result = std::accumulate(backend.begin(), backend.end(), 0);
}

template <int n>
void eval_convert_to(long long* result, const ndouble<n>& backend)
{
    *result = std::accumulate(backend.begin(), backend.end(), 0);
}

template <int n>
void eval_convert_to(long double* result, const ndouble<n>& backend)
{
    *result = std::accumulate(backend.begin(), backend.end(), static_cast<long double>(0));
}

//void eval_convert_to(unsigned long* result, const ndouble& backend);
//void eval_convert_to(unsigned* result, const ndouble& backend);
//void eval_convert_to(unsigned short* result, const ndouble& backend);
//void eval_convert_to(unsigned char* result, const ndouble& backend);

//void eval_convert_to(char* result, const ndouble& backend);

//void eval_convert_to(long* result, const ndouble& backend);
//void eval_convert_to(int* result, const ndouble& backend);
//void eval_convert_to(short* result, const ndouble& backend);
//void eval_convert_to(signed char* result, const ndouble& backend);

//void eval_convert_to(double* result, const ndouble& backend);
//void eval_convert_to(float* result, const ndouble& backend);

//
// Operations which are required *only* if we have a floating point type:
//
template <int n>
void eval_frexp(ndouble<n>& result, const ndouble<n>& arg, typename ndouble<n>::exponent_type* p_exponent)
{
    std::frexp(arg.back(), p_exponent);
    result = arg;
    for(auto c_it = result.m_components.begin(); c_it != result.m_end; ++c_it)
        *c_it /= std::pow(2., p_exponent);
}

template <int n>
void eval_frexp(ndouble<n>& result, const ndouble<n>& arg, int* p_exponent)  // throws a runtime_error if the exponent is too large for an int
{
    eval_frexp(result, arg, p_exponent);
}

template <int n>
void eval_ldexp(ndouble<n>& result, const ndouble<n>& arg, typename ndouble<n>::exponent_type exponent)
{
    result = arg;
    for(auto c_it = result.m_components.beign(); c_it != result.m_end; ++c_it)
        *c_it = std::ldexp(*c_it, exponent);
}

template <int n>
void eval_ldexp(ndouble<n>& result, const ndouble<n>& arg, int exponent)
{
    eval_ldexp(result, arg, exponent);
}

template <int n>
void eval_floor(ndouble<n>& result, const ndouble<n>& arg)
{
    result = arg;
    for(auto c_it = result.m_components.begin(); c_it != result.m_end; ++c_it)
        *c_it = std::floor(*c_it);
}

template <int n>
void eval_ceil(ndouble<n>& result, const ndouble<n>& arg)
{
    result = arg;
    bool zero = false;
    for(auto c_it = result.m_end - 1;; --c_it)
    {
        if(zero) *c_it = 0.;
        else if(std::ceil(*c_it) != *c_it)
        {
            *c_it = std::ceil(*c_it);
            zero = true;
        }
        if(c_it == result.m_components.begin()) break;
    }
}

template <int n>
void eval_sqrt(ndouble<n>& result, const ndouble<n>& arg)
{
    auto approx = std::accumulate
        <
            typename ndouble<n>::const_it
        >
                                 (arg.m_components.begin(),
                                  arg.m_end,
                                  0.);
    result = std::sqrt(approx);
    for(int i = 0; i < 3*n; ++i)
    {
        ndouble<n> v = arg;
        eval_divide(v, result);
        eval_add(result, v);
        for(auto c_it = result.m_components.begin(); c_it != result.m_end; ++c_it)
            *c_it *= 0.5;
    }
}

//
// Hashing support, not strictly required, but it is used in our tests:
//
template <int n>
std::size_t hash_value(const ndouble<n>& arg)
{
    return ::boost::hash_value(arg.m_components);
}

//
// We're now into strictly optional requirements, everything that follows is
// nice to have, but can be synthesised from the operators above if required.
// Typically these operations are here to improve performance and reduce the
// number of temporaries created.
//
// assign_components: required number types with 2 seperate components (rationals and complex numbers).
// Type skeleton_component_type is whatever the corresponding backend type for the components is:
//
//void assign_conponents(ndouble& result, skeleton_component_type const& a, skeleton_component_type const& b);
//
// Again for arithmetic types, overload for whatever arithmetic types are directly supported:
//
//void assign_conponents(ndouble& result, double a, double b);
//
// Optional comparison operators:
//
#if 0

bool eval_is_zero(const ndouble& arg);
int eval_get_sign(const ndouble& arg);

bool eval_eq(const ndouble& a, const ndouble& b);
bool eval_eq(const ndouble& a, unsigned long long b);
bool eval_eq(const ndouble& a, unsigned long b);
bool eval_eq(const ndouble& a, unsigned b);
bool eval_eq(const ndouble& a, unsigned short b);
bool eval_eq(const ndouble& a, unsigned char b);
bool eval_eq(const ndouble& a, long long b);
bool eval_eq(const ndouble& a, long b);
bool eval_eq(const ndouble& a, int b);
bool eval_eq(const ndouble& a, short b);
bool eval_eq(const ndouble& a, signed char b);
bool eval_eq(const ndouble& a, char b);
bool eval_eq(const ndouble& a, long double b);
bool eval_eq(const ndouble& a, double b);
bool eval_eq(const ndouble& a, float b);

bool eval_eq(unsigned long long a, const ndouble& b);
bool eval_eq(unsigned long a, const ndouble& b);
bool eval_eq(unsigned a, const ndouble& b);
bool eval_eq(unsigned short a, const ndouble& b);
bool eval_eq(unsigned char a, const ndouble& b);
bool eval_eq(long long a, const ndouble& b);
bool eval_eq(long a, const ndouble& b);
bool eval_eq(int a, const ndouble& b);
bool eval_eq(short a, const ndouble& b);
bool eval_eq(signed char a, const ndouble& b);
bool eval_eq(char a, const ndouble& b);
bool eval_eq(long double a, const ndouble& b);
bool eval_eq(double a, const ndouble& b);
bool eval_eq(float a, const ndouble& b);

bool eval_lt(const ndouble& a, const ndouble& b);
bool eval_lt(const ndouble& a, unsigned long long b);
bool eval_lt(const ndouble& a, unsigned long b);
bool eval_lt(const ndouble& a, unsigned b);
bool eval_lt(const ndouble& a, unsigned short b);
bool eval_lt(const ndouble& a, unsigned char b);
bool eval_lt(const ndouble& a, long long b);
bool eval_lt(const ndouble& a, long b);
bool eval_lt(const ndouble& a, int b);
bool eval_lt(const ndouble& a, short b);
bool eval_lt(const ndouble& a, signed char b);
bool eval_lt(const ndouble& a, char b);
bool eval_lt(const ndouble& a, long double b);
bool eval_lt(const ndouble& a, double b);
bool eval_lt(const ndouble& a, float b);

bool eval_lt(unsigned long long a, const ndouble& b);
bool eval_lt(unsigned long a, const ndouble& b);
bool eval_lt(unsigned a, const ndouble& b);
bool eval_lt(unsigned short a, const ndouble& b);
bool eval_lt(unsigned char a, const ndouble& b);
bool eval_lt(long long a, const ndouble& b);
bool eval_lt(long a, const ndouble& b);
bool eval_lt(int a, const ndouble& b);
bool eval_lt(short a, const ndouble& b);
bool eval_lt(signed char a, const ndouble& b);
bool eval_lt(char a, const ndouble& b);
bool eval_lt(long double a, const ndouble& b);
bool eval_lt(double a, const ndouble& b);
bool eval_lt(float a, const ndouble& b);

bool eval_gt(const ndouble& a, const ndouble& b);
bool eval_gt(const ndouble& a, unsigned long long b);
bool eval_gt(const ndouble& a, unsigned long b);
bool eval_gt(const ndouble& a, unsigned b);
bool eval_gt(const ndouble& a, unsigned short b);
bool eval_gt(const ndouble& a, unsigned char b);
bool eval_gt(const ndouble& a, long long b);
bool eval_gt(const ndouble& a, long b);
bool eval_gt(const ndouble& a, int b);
bool eval_gt(const ndouble& a, short b);
bool eval_gt(const ndouble& a, signed char b);
bool eval_gt(const ndouble& a, char b);
bool eval_gt(const ndouble& a, long double b);
bool eval_gt(const ndouble& a, double b);
bool eval_gt(const ndouble& a, float b);

bool eval_gt(unsigned long long a, const ndouble& b);
bool eval_gt(unsigned long a, const ndouble& b);
bool eval_gt(unsigned a, const ndouble& b);
bool eval_gt(unsigned short a, const ndouble& b);
bool eval_gt(unsigned char a, const ndouble& b);
bool eval_gt(long long a, const ndouble& b);
bool eval_gt(long a, const ndouble& b);
bool eval_gt(int a, const ndouble& b);
bool eval_gt(short a, const ndouble& b);
bool eval_gt(signed char a, const ndouble& b);
bool eval_gt(char a, const ndouble& b);
bool eval_gt(long double a, const ndouble& b);
bool eval_gt(double a, const ndouble& b);
bool eval_gt(float a, const ndouble& b);
#endif

//
// Arithmetic operations, starting with addition:
//
#if 0
void eval_add(ndouble& result, unsigned long long arg);
void eval_add(ndouble& result, unsigned long arg);
void eval_add(ndouble& result, unsigned arg);
void eval_add(ndouble& result, unsigned short arg);
void eval_add(ndouble& result, unsigned char arg);
void eval_add(ndouble& result, char arg);
void eval_add(ndouble& result, long long arg);
void eval_add(ndouble& result, long arg);
void eval_add(ndouble& result, int arg);
void eval_add(ndouble& result, short arg);
void eval_add(ndouble& result, signed char arg);
void eval_add(ndouble& result, long double arg);
void eval_add(ndouble& result, double arg);
void eval_add(ndouble& result, float arg);

void eval_add(ndouble& result, const ndouble& a, const ndouble& b);
void eval_add(ndouble& result, const ndouble& a, unsigned long long b);
void eval_add(ndouble& result, const ndouble& a, unsigned long b);
void eval_add(ndouble& result, const ndouble& a, unsigned b);
void eval_add(ndouble& result, const ndouble& a, unsigned short b);
void eval_add(ndouble& result, const ndouble& a, unsigned char b);
void eval_add(ndouble& result, const ndouble& a, long long b);
void eval_add(ndouble& result, const ndouble& a, long b);
void eval_add(ndouble& result, const ndouble& a, int b);
void eval_add(ndouble& result, const ndouble& a, short b);
void eval_add(ndouble& result, const ndouble& a, signed char b);
void eval_add(ndouble& result, const ndouble& a, char b);
void eval_add(ndouble& result, const ndouble& a, long double b);
void eval_add(ndouble& result, const ndouble& a, double b);
void eval_add(ndouble& result, const ndouble& a, float b);

void eval_add(ndouble& result, unsigned long long b, const ndouble& a);
void eval_add(ndouble& result, unsigned long b, const ndouble& a);
void eval_add(ndouble& result, unsigned b, const ndouble& a);
void eval_add(ndouble& result, unsigned short b, const ndouble& a);
void eval_add(ndouble& result, unsigned char b, const ndouble& a);
void eval_add(ndouble& result, long long b, const ndouble& a);
void eval_add(ndouble& result, long b, const ndouble& a);
void eval_add(ndouble& result, int b, const ndouble& a);
void eval_add(ndouble& result, short b, const ndouble& a);
void eval_add(ndouble& result, signed char b, const ndouble& a);
void eval_add(ndouble& result, char b, const ndouble& a);
void eval_add(ndouble& result, long double b, const ndouble& a);
void eval_add(ndouble& result, double b, const ndouble& a);
void eval_add(ndouble& result, float b, const ndouble& a);
#endif

//
// Subtraction:
//
#if 0
void eval_subtract(ndouble& result, unsigned long long arg);
void eval_subtract(ndouble& result, unsigned long arg);
void eval_subtract(ndouble& result, unsigned arg);
void eval_subtract(ndouble& result, unsigned short arg);
void eval_subtract(ndouble& result, unsigned char arg);
void eval_subtract(ndouble& result, char arg);
void eval_subtract(ndouble& result, long long arg);
void eval_subtract(ndouble& result, long arg);
void eval_subtract(ndouble& result, int arg);
void eval_subtract(ndouble& result, short arg);
void eval_subtract(ndouble& result, signed char arg);
void eval_subtract(ndouble& result, long double arg);
void eval_subtract(ndouble& result, double arg);
void eval_subtract(ndouble& result, float arg);

void eval_subtract(ndouble& result, const ndouble& a, const ndouble& b);
void eval_subtract(ndouble& result, const ndouble& a, unsigned long long b);
void eval_subtract(ndouble& result, const ndouble& a, unsigned long b);
void eval_subtract(ndouble& result, const ndouble& a, unsigned b);
void eval_subtract(ndouble& result, const ndouble& a, unsigned short b);
void eval_subtract(ndouble& result, const ndouble& a, unsigned char b);
void eval_subtract(ndouble& result, const ndouble& a, long long b);
void eval_subtract(ndouble& result, const ndouble& a, long b);
void eval_subtract(ndouble& result, const ndouble& a, int b);
void eval_subtract(ndouble& result, const ndouble& a, short b);
void eval_subtract(ndouble& result, const ndouble& a, signed char b);
void eval_subtract(ndouble& result, const ndouble& a, char b);
void eval_subtract(ndouble& result, const ndouble& a, long double b);
void eval_subtract(ndouble& result, const ndouble& a, double b);
void eval_subtract(ndouble& result, const ndouble& a, float b);

void eval_subtract(ndouble& result, unsigned long long b, const ndouble& a);
void eval_subtract(ndouble& result, unsigned long b, const ndouble& a);
void eval_subtract(ndouble& result, unsigned b, const ndouble& a);
void eval_subtract(ndouble& result, unsigned short b, const ndouble& a);
void eval_subtract(ndouble& result, unsigned char b, const ndouble& a);
void eval_subtract(ndouble& result, long long b, const ndouble& a);
void eval_subtract(ndouble& result, long b, const ndouble& a);
void eval_subtract(ndouble& result, int b, const ndouble& a);
void eval_subtract(ndouble& result, short b, const ndouble& a);
void eval_subtract(ndouble& result, signed char b, const ndouble& a);
void eval_subtract(ndouble& result, char b, const ndouble& a);
void eval_subtract(ndouble& result, long double b, const ndouble& a);
void eval_subtract(ndouble& result, double b, const ndouble& a);
void eval_subtract(ndouble& result, float b, const ndouble& a);
#endif

//
// Multiplication:
//
#if 0
void eval_multiply(ndouble& result, unsigned long long arg);
void eval_multiply(ndouble& result, unsigned long arg);
void eval_multiply(ndouble& result, unsigned arg);
void eval_multiply(ndouble& result, unsigned short arg);
void eval_multiply(ndouble& result, unsigned char arg);
void eval_multiply(ndouble& result, char arg);
void eval_multiply(ndouble& result, long long arg);
void eval_multiply(ndouble& result, long arg);
void eval_multiply(ndouble& result, int arg);
void eval_multiply(ndouble& result, short arg);
void eval_multiply(ndouble& result, signed char arg);
void eval_multiply(ndouble& result, long double arg);
void eval_multiply(ndouble& result, double arg);
void eval_multiply(ndouble& result, float arg);

void eval_multiply(ndouble& result, const ndouble& a, const ndouble& b);
void eval_multiply(ndouble& result, const ndouble& a, unsigned long long b);
void eval_multiply(ndouble& result, const ndouble& a, unsigned long b);
void eval_multiply(ndouble& result, const ndouble& a, unsigned b);
void eval_multiply(ndouble& result, const ndouble& a, unsigned short b);
void eval_multiply(ndouble& result, const ndouble& a, unsigned char b);
void eval_multiply(ndouble& result, const ndouble& a, long long b);
void eval_multiply(ndouble& result, const ndouble& a, long b);
void eval_multiply(ndouble& result, const ndouble& a, int b);
void eval_multiply(ndouble& result, const ndouble& a, short b);
void eval_multiply(ndouble& result, const ndouble& a, signed char b);
void eval_multiply(ndouble& result, const ndouble& a, char b);
void eval_multiply(ndouble& result, const ndouble& a, long double b);
void eval_multiply(ndouble& result, const ndouble& a, double b);
void eval_multiply(ndouble& result, const ndouble& a, float b);

void eval_multiply(ndouble& result, unsigned long long b, const ndouble& a);
void eval_multiply(ndouble& result, unsigned long b, const ndouble& a);
void eval_multiply(ndouble& result, unsigned b, const ndouble& a);
void eval_multiply(ndouble& result, unsigned short b, const ndouble& a);
void eval_multiply(ndouble& result, unsigned char b, const ndouble& a);
void eval_multiply(ndouble& result, long long b, const ndouble& a);
void eval_multiply(ndouble& result, long b, const ndouble& a);
void eval_multiply(ndouble& result, int b, const ndouble& a);
void eval_multiply(ndouble& result, short b, const ndouble& a);
void eval_multiply(ndouble& result, signed char b, const ndouble& a);
void eval_multiply(ndouble& result, char b, const ndouble& a);
void eval_multiply(ndouble& result, long double b, const ndouble& a);
void eval_multiply(ndouble& result, double b, const ndouble& a);
void eval_multiply(ndouble& result, float b, const ndouble& a);
#endif

//
// Division:
//
#if 0
void eval_divide(ndouble& result, unsigned long long arg);
void eval_divide(ndouble& result, unsigned long arg);
void eval_divide(ndouble& result, unsigned arg);
void eval_divide(ndouble& result, unsigned short arg);
void eval_divide(ndouble& result, unsigned char arg);
void eval_divide(ndouble& result, char arg);
void eval_divide(ndouble& result, long long arg);
void eval_divide(ndouble& result, long arg);
void eval_divide(ndouble& result, int arg);
void eval_divide(ndouble& result, short arg);
void eval_divide(ndouble& result, signed char arg);
void eval_divide(ndouble& result, long double arg);
void eval_divide(ndouble& result, double arg);
void eval_divide(ndouble& result, float arg);

void eval_divide(ndouble& result, const ndouble& a, const ndouble& b);
void eval_divide(ndouble& result, const ndouble& a, unsigned long long b);
void eval_divide(ndouble& result, const ndouble& a, unsigned long b);
void eval_divide(ndouble& result, const ndouble& a, unsigned b);
void eval_divide(ndouble& result, const ndouble& a, unsigned short b);
void eval_divide(ndouble& result, const ndouble& a, unsigned char b);
void eval_divide(ndouble& result, const ndouble& a, long long b);
void eval_divide(ndouble& result, const ndouble& a, long b);
void eval_divide(ndouble& result, const ndouble& a, int b);
void eval_divide(ndouble& result, const ndouble& a, short b);
void eval_divide(ndouble& result, const ndouble& a, signed char b);
void eval_divide(ndouble& result, const ndouble& a, char b);
void eval_divide(ndouble& result, const ndouble& a, long double b);
void eval_divide(ndouble& result, const ndouble& a, double b);
void eval_divide(ndouble& result, const ndouble& a, float b);

void eval_divide(ndouble& result, unsigned long long b, const ndouble& a);
void eval_divide(ndouble& result, unsigned long b, const ndouble& a);
void eval_divide(ndouble& result, unsigned b, const ndouble& a);
void eval_divide(ndouble& result, unsigned short b, const ndouble& a);
void eval_divide(ndouble& result, unsigned char b, const ndouble& a);
void eval_divide(ndouble& result, long long b, const ndouble& a);
void eval_divide(ndouble& result, long b, const ndouble& a);
void eval_divide(ndouble& result, int b, const ndouble& a);
void eval_divide(ndouble& result, short b, const ndouble& a);
void eval_divide(ndouble& result, signed char b, const ndouble& a);
void eval_divide(ndouble& result, char b, const ndouble& a);
void eval_divide(ndouble& result, long double b, const ndouble& a);
void eval_divide(ndouble& result, double b, const ndouble& a);
void eval_divide(ndouble& result, float b, const ndouble& a);
#endif
//
// Multiply and add/subtract as one:
//
#if 0
void eval_multiply_add(ndouble& result, const ndouble& a, const ndouble& b);
void eval_multiply_add(ndouble& result, const ndouble& a, unsigned long long b);
void eval_multiply_add(ndouble& result, const ndouble& a, unsigned long b);
void eval_multiply_add(ndouble& result, const ndouble& a, unsigned b);
void eval_multiply_add(ndouble& result, const ndouble& a, unsigned short b);
void eval_multiply_add(ndouble& result, const ndouble& a, unsigned char b);
void eval_multiply_add(ndouble& result, const ndouble& a, long long b);
void eval_multiply_add(ndouble& result, const ndouble& a, long b);
void eval_multiply_add(ndouble& result, const ndouble& a, int b);
void eval_multiply_add(ndouble& result, const ndouble& a, short b);
void eval_multiply_add(ndouble& result, const ndouble& a, signed char b);
void eval_multiply_add(ndouble& result, const ndouble& a, char b);
void eval_multiply_add(ndouble& result, const ndouble& a, long double b);
void eval_multiply_add(ndouble& result, const ndouble& a, double b);
void eval_multiply_add(ndouble& result, const ndouble& a, float b);

void eval_multiply_add(ndouble& result, unsigned long long b, const ndouble& a);
void eval_multiply_add(ndouble& result, unsigned long b, const ndouble& a);
void eval_multiply_add(ndouble& result, unsigned b, const ndouble& a);
void eval_multiply_add(ndouble& result, unsigned short b, const ndouble& a);
void eval_multiply_add(ndouble& result, unsigned char b, const ndouble& a);
void eval_multiply_add(ndouble& result, long long b, const ndouble& a);
void eval_multiply_add(ndouble& result, long b, const ndouble& a);
void eval_multiply_add(ndouble& result, int b, const ndouble& a);
void eval_multiply_add(ndouble& result, short b, const ndouble& a);
void eval_multiply_add(ndouble& result, signed char b, const ndouble& a);
void eval_multiply_add(ndouble& result, char b, const ndouble& a);
void eval_multiply_add(ndouble& result, long double b, const ndouble& a);
void eval_multiply_add(ndouble& result, double b, const ndouble& a);
void eval_multiply_add(ndouble& result, float b, const ndouble& a);

void eval_multiply_subtract(ndouble& result, const ndouble& a, const ndouble& b);
void eval_multiply_subtract(ndouble& result, const ndouble& a, unsigned long long b);
void eval_multiply_subtract(ndouble& result, const ndouble& a, unsigned long b);
void eval_multiply_subtract(ndouble& result, const ndouble& a, unsigned b);
void eval_multiply_subtract(ndouble& result, const ndouble& a, unsigned short b);
void eval_multiply_subtract(ndouble& result, const ndouble& a, unsigned char b);
void eval_multiply_subtract(ndouble& result, const ndouble& a, long long b);
void eval_multiply_subtract(ndouble& result, const ndouble& a, long b);
void eval_multiply_subtract(ndouble& result, const ndouble& a, int b);
void eval_multiply_subtract(ndouble& result, const ndouble& a, short b);
void eval_multiply_subtract(ndouble& result, const ndouble& a, signed char b);
void eval_multiply_subtract(ndouble& result, const ndouble& a, char b);
void eval_multiply_subtract(ndouble& result, const ndouble& a, long double b);
void eval_multiply_subtract(ndouble& result, const ndouble& a, double b);
void eval_multiply_subtract(ndouble& result, const ndouble& a, float b);

void eval_multiply_subtract(ndouble& result, unsigned long long b, const ndouble& a);
void eval_multiply_subtract(ndouble& result, unsigned long b, const ndouble& a);
void eval_multiply_subtract(ndouble& result, unsigned b, const ndouble& a);
void eval_multiply_subtract(ndouble& result, unsigned short b, const ndouble& a);
void eval_multiply_subtract(ndouble& result, unsigned char b, const ndouble& a);
void eval_multiply_subtract(ndouble& result, long long b, const ndouble& a);
void eval_multiply_subtract(ndouble& result, long b, const ndouble& a);
void eval_multiply_subtract(ndouble& result, int b, const ndouble& a);
void eval_multiply_subtract(ndouble& result, short b, const ndouble& a);
void eval_multiply_subtract(ndouble& result, signed char b, const ndouble& a);
void eval_multiply_subtract(ndouble& result, char b, const ndouble& a);
void eval_multiply_subtract(ndouble& result, long double b, const ndouble& a);
void eval_multiply_subtract(ndouble& result, double b, const ndouble& a);
void eval_multiply_subtract(ndouble& result, float b, const ndouble& a);
#endif
//
// Increment and decrement:
//
//void eval_increment(ndouble& arg);
//void eval_decrement(ndouble& arg);
//
// abs/fabs:
//
// void eval_abs(ndouble& result, const ndouble& arg);
// void eval_fabs(ndouble& result, const ndouble& arg);
//

} // namespace backends

//
// Import the backend into this namespace:
//
using boost::multiprecision::backends::ndouble;
//
// Typedef whatever number's make use of this backend:
//
template <int n>
using ndouble_number = number<ndouble<n>, et_off>;
//
// Define a category for this number type, one of:
// 
//    number_kind_integer
//    number_kind_floating_point
//    number_kind_rational
//    number_kind_fixed_point
//    number_kind_complex
//
template<int n>
struct number_category<ndouble<n>> : public std::integral_constant<int, number_kind_floating_point>
{};

//
// These 2 traits classes are required for complex types only:
//
/*
template <expression_template_option ExpressionTemplates>
struct component_type<number<ndouble, ExpressionTemplates> >
{
   typedef number<skeleton_real_type, ExpressionTemplates> type;
};

template <expression_template_option ExpressionTemplates>
struct complex_result_from_scalar<number<skeleton_real_type, ExpressionTemplates> >
{
   typedef number<ndouble, ExpressionTemplates> type;
};
*/

/**************************************************************

OVERLOADABLE FUNCTIONS - FLOATING POINT TYPES ONLY

****************************************************************/

#if 0

template <boost::multiprecision::expression_template_option ExpressionTemplates>
int sign(const number<ndouble, ExpressionTemplates>& arg);
template <boost::multiprecision::expression_template_option ExpressionTemplates>
int signbit(const number<ndouble, ExpressionTemplates>& arg);
template <boost::multiprecision::expression_template_option ExpressionTemplates>
number<ndouble, ExpressionTemplates> changesign(const number<ndouble, ExpressionTemplates>& arg);
template <boost::multiprecision::expression_template_option ExpressionTemplates>
number<ndouble, ExpressionTemplates> copysign(const number<ndouble, ExpressionTemplates>& a, const number<ndouble, ExpressionTemplates>& b);

template <boost::multiprecision::expression_template_option ExpressionTemplates>
number<ndouble, ExpressionTemplates> cbrt(const number<ndouble, ExpressionTemplates>& arg);
template <boost::multiprecision::expression_template_option ExpressionTemplates>
number<ndouble, ExpressionTemplates> erf(const number<ndouble, ExpressionTemplates>& arg);
template <boost::multiprecision::expression_template_option ExpressionTemplates>
number<ndouble, ExpressionTemplates> erfc(const number<ndouble, ExpressionTemplates>& arg);
template <boost::multiprecision::expression_template_option ExpressionTemplates>
number<ndouble, ExpressionTemplates> expm1(const number<ndouble, ExpressionTemplates>& arg);
template <boost::multiprecision::expression_template_option ExpressionTemplates>
number<ndouble, ExpressionTemplates> log1p(const number<ndouble, ExpressionTemplates>& arg);
template <boost::multiprecision::expression_template_option ExpressionTemplates>
number<ndouble, ExpressionTemplates> tgamma(const number<ndouble, ExpressionTemplates>& arg);
template <boost::multiprecision::expression_template_option ExpressionTemplates>
number<ndouble, ExpressionTemplates> lgamma(const number<ndouble, ExpressionTemplates>& arg);

template <boost::multiprecision::expression_template_option ExpressionTemplates>
long lrint(const number<ndouble, ExpressionTemplates>& arg);
template <boost::multiprecision::expression_template_option ExpressionTemplates>
long long llrint(const number<ndouble, ExpressionTemplates>& arg);

template <boost::multiprecision::expression_template_option ExpressionTemplates>
number<ndouble, ExpressionTemplates> nextafter(const number<ndouble, ExpressionTemplates>& a, const number<ndouble, ExpressionTemplates>& b);
template <boost::multiprecision::expression_template_option ExpressionTemplates>
number<ndouble, ExpressionTemplates> nexttoward(const number<ndouble, ExpressionTemplates>& a, const number<ndouble, ExpressionTemplates>& b);

#endif

}} // namespace boost::multiprecision

/**********************************************************************************

FLOATING POINT ONLY
Nice to have stuff for better integration with Boost.Math.

***********************************************************************************/

namespace boost {
namespace math {
namespace tools {

#if 0

template <>
int digits<boost::multiprecision::number<boost::multiprecision::skeleton_number> >();

template <>
boost::multiprecision::mpfr_float max_value<boost::multiprecision::skeleton_number>();

template <>
boost::multiprecision::mpfr_float min_value<boost::multiprecision::skeleton_number>();

#endif

} // namespace tools

namespace constants {
namespace detail {

#if 0
template <boost::multiprecision::expression_template_option ExpressionTemplates>
struct constant_pi<boost::multiprecision::number<boost::multiprecision::ndouble, ExpressionTemplates> >
{
   typedef boost::multiprecision::number<boost::multiprecision::ndouble, ExpressionTemplates> result_type;
   //
   // Fixed N-digit precision, return reference to internal/cached object:
   //
   template <int N>
   static inline const result_type& get(const boost::integral_constant<int, N>&);
   //
   // Variable precision, returns fresh result each time (unless precision is unchanged from last call):
   //
   static inline const result_type  get(const boost::integral_constant<int, 0>&);
};
//
// Plus any other constants supported natively by this type....
//
#endif

} // namespace detail
} // namespace constants

}} // namespace boost::math


namespace std {

template <boost::multiprecision::expression_template_option ExpressionTemplates, int n>
class numeric_limits<boost::multiprecision::number<boost::multiprecision::ndouble<n>, ExpressionTemplates> >
{
   typedef boost::multiprecision::number<boost::multiprecision::ndouble<n>, ExpressionTemplates> number_type;

 public:
   static constexpr bool is_specialized = true;
   static constexpr number_type min()
   {
       return std::numeric_limits<double>::min();
   }
   static constexpr number_type max()
   {
       return std::numeric_limits<double>::max(); //this is not really true
   }
   static constexpr number_type lowest()
   {
       return std::numeric_limits<double>::lowest(); //this isn't true either
   }
   static constexpr int                digits       = DBL_MANT_DIG * n;
   static constexpr int                digits10     = DBL_DIG * n;
   static constexpr int                max_digits10 = DBL_DECIMAL_DIG * n;
   static constexpr bool               is_signed    = true;
   static constexpr bool               is_integer   = false;
   static constexpr bool               is_exact     = n == -1;
   static constexpr int                radix        = 2;
   static constexpr number_type                        epsilon()
   {
        if(n == -1) return 0; //not really true
        else return std::pow(DBL_EPSILON, n); 
        //it could be argued that this should be min denorm instead
   }
   static constexpr number_type                        round_error()
   {
       if(n == -1) return 0;
       else return 1.;
   }
   static constexpr int                min_exponent      = DBL_MIN_EXP;
   static constexpr int                min_exponent10    = DBL_MIN_10_EXP;
   static constexpr int                max_exponent      = DBL_MAX_EXP;
   static constexpr int                max_exponent10    = DBL_MAX_10_EXP;
   static constexpr bool               has_infinity      = true;
   static constexpr bool               has_quiet_NaN     = false;
   static constexpr bool               has_signaling_NaN = false;
   static constexpr float_denorm_style has_denorm        = denorm_absent;
   static constexpr bool               has_denorm_loss   = false;
   static constexpr number_type                        infinity()
   {
       return std::numeric_limits<double>::infinity();
   }
   static constexpr number_type                        quiet_NaN()
   {
       return std::numeric_limits<double>::quiet_NaN();
   }
   static constexpr number_type                        signaling_NaN()
   {
       return std::numeric_limits<double>::signaling_NaN();
   }
   static constexpr number_type                        denorm_min()
   {
       return std::numeric_limits<double>::denorm_min();
   }
   static constexpr bool               is_iec559       = false;
   static constexpr bool               is_bounded      = true;
   static constexpr bool               is_modulo       = false;
   static constexpr bool               traps           = false;
   static constexpr bool               tinyness_before = false;
   static constexpr float_round_style  round_style     = round_toward_zero;
};

template <boost::multiprecision::expression_template_option ExpressionTemplates, int n>
constexpr int numeric_limits<boost::multiprecision::number<boost::multiprecision::ndouble<n>, ExpressionTemplates> >::digits;
template <boost::multiprecision::expression_template_option ExpressionTemplates, int n>
constexpr int numeric_limits<boost::multiprecision::number<boost::multiprecision::ndouble<n>, ExpressionTemplates> >::digits10;
template <boost::multiprecision::expression_template_option ExpressionTemplates, int n>
constexpr int numeric_limits<boost::multiprecision::number<boost::multiprecision::ndouble<n>, ExpressionTemplates> >::max_digits10;
template <boost::multiprecision::expression_template_option ExpressionTemplates, int n>
constexpr bool numeric_limits<boost::multiprecision::number<boost::multiprecision::ndouble<n>, ExpressionTemplates> >::is_signed;
template <boost::multiprecision::expression_template_option ExpressionTemplates, int n>
constexpr bool numeric_limits<boost::multiprecision::number<boost::multiprecision::ndouble<n>, ExpressionTemplates> >::is_integer;
template <boost::multiprecision::expression_template_option ExpressionTemplates, int n>
constexpr bool numeric_limits<boost::multiprecision::number<boost::multiprecision::ndouble<n>, ExpressionTemplates> >::is_exact;
template <boost::multiprecision::expression_template_option ExpressionTemplates, int n>
constexpr int numeric_limits<boost::multiprecision::number<boost::multiprecision::ndouble<n>, ExpressionTemplates> >::radix;
template <boost::multiprecision::expression_template_option ExpressionTemplates, int n>
constexpr int numeric_limits<boost::multiprecision::number<boost::multiprecision::ndouble<n>, ExpressionTemplates> >::min_exponent;
template <boost::multiprecision::expression_template_option ExpressionTemplates, int n>
constexpr int numeric_limits<boost::multiprecision::number<boost::multiprecision::ndouble<n>, ExpressionTemplates> >::min_exponent10;
template <boost::multiprecision::expression_template_option ExpressionTemplates, int n>
constexpr int numeric_limits<boost::multiprecision::number<boost::multiprecision::ndouble<n>, ExpressionTemplates> >::max_exponent;
template <boost::multiprecision::expression_template_option ExpressionTemplates, int n>
constexpr int numeric_limits<boost::multiprecision::number<boost::multiprecision::ndouble<n>, ExpressionTemplates> >::max_exponent10;
template <boost::multiprecision::expression_template_option ExpressionTemplates, int n>
constexpr bool numeric_limits<boost::multiprecision::number<boost::multiprecision::ndouble<n>, ExpressionTemplates> >::has_infinity;
template <boost::multiprecision::expression_template_option ExpressionTemplates, int n>
constexpr bool numeric_limits<boost::multiprecision::number<boost::multiprecision::ndouble<n>, ExpressionTemplates> >::has_quiet_NaN;
template <boost::multiprecision::expression_template_option ExpressionTemplates, int n>
constexpr bool numeric_limits<boost::multiprecision::number<boost::multiprecision::ndouble<n>, ExpressionTemplates> >::has_signaling_NaN;
template <boost::multiprecision::expression_template_option ExpressionTemplates, int n>
constexpr float_denorm_style numeric_limits<boost::multiprecision::number<boost::multiprecision::ndouble<n>, ExpressionTemplates> >::has_denorm;
template <boost::multiprecision::expression_template_option ExpressionTemplates, int n>
constexpr bool numeric_limits<boost::multiprecision::number<boost::multiprecision::ndouble<n>, ExpressionTemplates> >::has_denorm_loss;
template <boost::multiprecision::expression_template_option ExpressionTemplates, int n>
constexpr bool numeric_limits<boost::multiprecision::number<boost::multiprecision::ndouble<n>, ExpressionTemplates> >::is_iec559;
template <boost::multiprecision::expression_template_option ExpressionTemplates, int n>
constexpr bool numeric_limits<boost::multiprecision::number<boost::multiprecision::ndouble<n>, ExpressionTemplates> >::is_bounded;
template <boost::multiprecision::expression_template_option ExpressionTemplates, int n>
constexpr bool numeric_limits<boost::multiprecision::number<boost::multiprecision::ndouble<n>, ExpressionTemplates> >::is_modulo;
template <boost::multiprecision::expression_template_option ExpressionTemplates, int n>
constexpr bool numeric_limits<boost::multiprecision::number<boost::multiprecision::ndouble<n>, ExpressionTemplates> >::traps;
template <boost::multiprecision::expression_template_option ExpressionTemplates, int n>
constexpr bool numeric_limits<boost::multiprecision::number<boost::multiprecision::ndouble<n>, ExpressionTemplates> >::tinyness_before;
template <boost::multiprecision::expression_template_option ExpressionTemplates, int n>
constexpr float_round_style numeric_limits<boost::multiprecision::number<boost::multiprecision::ndouble<n>, ExpressionTemplates> >::round_style;

} // namespace std

#endif
