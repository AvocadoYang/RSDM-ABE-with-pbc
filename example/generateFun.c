#include <pbc/pbc.h>
#include <stdio.h>
#include <stdlib.h>


void generateFromG1(element_t, pairing_t);
void generateFromGt(element_t, pairing_t);
void generateFromZr(element_t, pairing_t);

void generateFromG1(element_t element, pairing_t pairing)
{
    element_init_G1(element, pairing);
    element_random(element);
    return;
};
void generateFromZr(element_t element, pairing_t pairing)
{
    element_init_Zr(element, pairing);
    element_random(element);
    return;
};
void generateFromGt(element_t element, pairing_t pairing){
    element_init_GT(element, pairing);
    element_random(element);
    return;
}