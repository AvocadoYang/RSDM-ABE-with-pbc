#include <pbc/pbc.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

pairing_t pairing;
clock_t start, end;

struct MSK {
    element_t a;
    element_t b;
    element_t alpha;
    element_t kappa;
};


