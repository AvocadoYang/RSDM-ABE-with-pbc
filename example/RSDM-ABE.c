#include <pbc/pbc.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "./generateFun.c"

pairing_t pairing;
clock_t start, end;
SETUP setup(int, int);

typedef element_t SK;

typedef struct msk {
    element_t a;
    element_t b;
    element_t alpha;
    element_t kappa;
} MSK;

typedef struct pp
{
    element_t g;
    element_t h;
    element_t w;
    element_t *Hx;
    element_t *hx;
    element_t r1; // g^b
    element_t r2; // g^(b^2)
    element_t r3; // h^b
    element_t omega;
} PP;

typedef struct setup {
    PP pp;
    MSK msk;
} SETUP;

typedef struct keys {
    SK userSK;
} KEY;


SETUP setup(int k, int m){
    SETUP set;
    //MSK 
    generateFromZr(set.msk.a, pairing); // a;
    generateFromZr(set.msk.b, pairing); // b;
    generateFromZr(set.msk.alpha, pairing); // alpha;
    generateFromZr(set.msk.kappa, pairing); // kappa;
    //[PP]
    //PP_Attribute
    generateFromG1(set.pp.g, pairing); // g
    generateFromG1(set.pp.w, pairing); // w init
    element_pow_zn(set.pp.w, set.pp.g, set.msk.a); //w = g^a
    set.pp.hx = (element_t*) malloc(k *sizeof(element_t));
    for(int i = 0; i < k; i++){
        generateFromG1(set.pp.hx[i], pairing);
    }
    set.pp.Hx = (element_t*) malloc(m*sizeof(element_t));
    element_t x;
    element_init_G1(x, pairing);
    // generateFromG1(x, pairing);
    mpz_t exp;
    for(int i = 0; i < m ; i++){
        mpz_init_set_si(exp, i);
        element_pow_mpz(x, set.msk.kappa, exp);
        element_init_G1(set.pp.Hx[i], pairing);
        element_pow_zn(set.pp.Hx[i], set.pp.g, x);
    };
    
    // Revock
    generateFromG1(set.pp.h, pairing);
    mpz_t square;
    mpz_init_set_si(square, 2);
    element_t pow_b_2;
    element_init_G1(pow_b_2, pairing);
    element_pow_mpz(pow_b_2, set.msk.b, square);

    generateFromG1(set.pp.r1, pairing); // r1 init
    element_pow_zn(set.pp.r1, set.pp.g, set.msk.b);
    generateFromG1(set.pp.r2, pairing); // r2 init
    element_pow_zn(set.pp.r2, set.pp.g, pow_b_2); //g^(b^2)
    generateFromG1(set.pp.r3, pairing); // r3 init
    element_pow_zn(set.pp.r3, set.pp.h, set.msk.b);

    // Message
    element_t temp;
    generateFromGt(temp, pairing);
    element_pairing(temp, set.pp.g, set.pp.g); // temp = e(g, g)
    generateFromGt(set.pp.omega, pairing);
    element_pow_zn(set.pp.omega, temp, set.msk.alpha);
    return set;
}


int main(int argc, char *argv[]){
    char param[1024];
    size_t count = fread(param, 1, 1024, stdin);
    if (!count)
        return 1;
    pairing_init_set_buf(pairing, param, count);
    int maxSizeOfPredicate, numberOfAttName;
    SETUP set =  setup(50, 50);
    return 0;
}