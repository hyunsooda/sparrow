#include <stdio.h>

typedef char* str;
typedef int (*FuncPtr)(int, int);

enum DayOfWeek {    // Pending
    Sunday = 15,
    Monday,
    Tuesday,
    Wednesday,
    Thursday,
    Friday,
    Saturday
};
// TODO: check global variable with init list after solving local init
struct Foo {
    int a;
    int b;
    int c;
    char d;
    float e;
    double g;
    int* p;
    double* m;
    str sp;
    FuncPtr fptr;
    float arr[5];
    enum DayOfWeek day;
};

struct Bar {
    int o;
    struct Foo foo;
    int p;
};

struct Baz {
    struct Bar bar;
    int q;
};

struct KL {
    int arr[2];
    struct Baz baz;
    char* some_ptr;
};

struct normal {
    int a;
    int c;
};

struct Foo f = {123,456};
struct Bar bar1 = {{123}};
struct Bar bar2 = {123};
struct Bar bar3 = {{123,456}};
int arr[5] = {1,2,3};
struct Baz baz = {1};
struct Foo f2 = {1,2,3,4,5.f,6.,(int*)0};
struct normal a = {1,2,3,4,5};
struct KL kl = {1,2,3,4,5};

int main() {
    int i=0;
}
