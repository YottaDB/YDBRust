#include "libyottadb.h"

#define MAXVPARMS 36

// TODO: this struct will be updated in the YDB 1.32 release!
typedef struct gparam_list_struct {
    intptr_t  n;
    void *arg[MAXVPARMS];
} gparam_list;
