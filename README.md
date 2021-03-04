# Illustration of possible floating-point expansion backend for Boost.Multiprecision

This is intended as a quick proof of concept for a possible, floating-point expansion backend for Boost.Multiprecision. The eval\_divide and eval\_sqrt functions should be considered placeholders.

The demos can be run via

```
g++ eigen_solve.cpp -std=c++17 -I./multiprecision/include -I./geometry/include -I/usr/include/eigen3/ -lmpfr && ./a.out
g++ main.cpp -std=c++17 -I./multiprecision/include -I./geometry/include && ./a.out
