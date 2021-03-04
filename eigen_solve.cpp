#include <iostream>
#include <random>
#include <chrono>
#include <boost/multiprecision/mpfr.hpp>
#include <boost/multiprecision/cpp_complex.hpp>
#include <boost/multiprecision/eigen.hpp>
#include <Eigen/Dense>
#include <random>
#include "ndouble.hpp"

int main()
{
    using namespace Eigen;
    using namespace boost::multiprecision;
    using number_type = boost::multiprecision::ndouble_number<8>;
    //using number_type = number<mpfr_float_backend<25, allocate_stack> >;

    using Mat = Matrix<number_type, 2, 2>;

    Mat A, b;
    A << number_type(2), number_type(-1), number_type(-1), number_type(3);
    b << 1, 2, 3, 1;
    std::cout << "Here is the matrix A:\n" << A << std::endl;
    std::cout << "Here is the right hand side b:\n" << b << std::endl;
    Mat x = A.fullPivLu().solve(b);
    std::cout << "The solution is:\n" << x << std::endl;
    number_type::value_type relative_error = (A*x - b).norm() / b.norm();
    std::cout << "The relative error is: " << relative_error << std::endl;

    return 0;
}
