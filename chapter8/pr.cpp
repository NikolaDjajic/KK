#include <iostream>

extern "C" {
    double square(double);
}

int main() {
    std::cout << "Square of number 4.0 is " << square(4.0) << std::endl;
}