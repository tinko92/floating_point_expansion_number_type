#include <iostream>

#include "ndouble.hpp"

template <int n>
void basic_arithmetic()
{
    boost::multiprecision::ndouble_number<n> a(8.), b(3.);
    std::cout << "components: " << n << "\n";
    std::cout << "a+b: " << a+b << "\n";
    std::cout << "a-b: " << a-b << "\n";
    std::cout << "a*b: " << a*b << "\n";
    std::cout << "a/b: " << a/b << "\n";
    std::cout << "(a/b) * b - a: " << (a/b)*b - a << "\n";
    std::cout << "a^0.5: " << boost::multiprecision::sqrt(a) << "\n";
    std::cout << "(a^0.5)^2 - a: " << boost::multiprecision::sqrt(a) * boost::multiprecision::sqrt(a) - a << "\n\n";
}

int main() {
    basic_arithmetic<2>();
    basic_arithmetic<3>();
    basic_arithmetic<4>();
    basic_arithmetic<5>();
    basic_arithmetic<6>();
    basic_arithmetic<7>();
    basic_arithmetic<8>();
}
