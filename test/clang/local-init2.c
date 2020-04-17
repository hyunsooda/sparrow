<<<<<<< HEAD
#include <stdio.h>

=======
>>>>>>> [Clang] Remove standard header files in test cases
typedef struct A {
    int y;
}A;
typedef struct B {
    int a;
    int b;
    A k[2];
}B;
int main() {
    B b = {1,};
}
