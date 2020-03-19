#include <stdio.h>
#include <stdlib.h>

typedef struct __pthread_list {
  struct __pthread_list *__prev;
  struct __pthread_list *__next;
} __pthread_list;

int main() {
    __pthread_list *pl = malloc(100);
    free(pl);
    pl = NULL;
    pl = malloc(100);
}
