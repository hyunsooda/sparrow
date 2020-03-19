#include <stdio.h>
#include <stdlib.h>

typedef struct _Node {
  struct _Node *prev;
  struct _Node *next;
} Node;

int main() {
    Node *pl = (Node*)malloc(sizeof(Node));
    pl->prev = NULL;
    pl->next = NULL;
    free(pl);
}
