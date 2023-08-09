#include <pbc/pbc.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "./generateFun.c"
#define ATTRIBUTE_NAME 50
#define ATTRIBUTE_VALUE 50
#define IdCount 20
#define COLUMN 10 
#define REVOKE 15
#define PREDICATE 10
pairing_t pairing;
clock_t start, end;

typedef struct msk {
    element_t a;
    element_t b;
    element_t alpha;
    element_t kappa;
    element_t *attribute;
    element_t *userId;
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
    //attributeKey
    element_t t;
    element_t K_1;
    element_t K_2;
    element_t *K_x;
    element_t *D_x;
    //revokKey
    element_t y;
    element_t D_0;
    element_t D_1;
    element_t D_2;
} KEY;

typedef struct access_structure{
    int **asArr;
    element_t *f_rox;
    element_t *y_n;
    element_t *r_l;
    element_t s;
    element_t s1;
    element_t *v;
    element_t *lamda;
} AS;

typedef struct revoke_list{
    element_t *s_r;
    element_t s2;
    element_t *rCount;
} RL;

typedef struct access_policy{
    AS LSSS;
    RL revoke;
} AP;

typedef struct ct {
    element_t C;
    element_t Cbar;
    element_t C_0;
    element_t *C_i;
    element_t *E_i;
    element_t *E_ij;
    element_t *C_k1;
    element_t *C_k2;
    mpz_t m;
} CT;

SETUP setup(int, int);
KEY attributeKeyGen(int, int, int, SETUP);
KEY revokKeyGen(int, SETUP, KEY);

SETUP setup(int k, int m){
    SETUP set;
    //[MSK] 
    generateFromZr(set.msk.a, pairing); // a;
    generateFromZr(set.msk.b, pairing); // b;
    generateFromZr(set.msk.alpha, pairing); // alpha;
    generateFromZr(set.msk.kappa, pairing); // kappa;
    set.msk.attribute = (element_t*) malloc(m*sizeof(element_t));
    for(int i = 0; i < m; i++){
        generateFromZr(set.msk.attribute[i], pairing);
    };
    set.msk.userId = (element_t *) malloc(IdCount*sizeof(element_t));
    for(int i = 0; i < IdCount; i++){
        generateFromZr(set.msk.userId[i], pairing);
    }
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

KEY attributeKeyGen(int k, int m, int personId, SETUP set){
    KEY keys;
    if (personId >= IdCount){
        return keys; 
    }
    //attributeKey
    generateFromZr(keys.t, pairing);
    // //K1
    element_t g_alpha;
    element_t w_t;
    generateFromG1(w_t, pairing);
    generateFromG1(keys.K_1, pairing);
    element_pow_zn(g_alpha, set.pp.g, set.msk.alpha); //????
    element_pow_zn(w_t, set.pp.w, keys.t); 
    element_mul(keys.K_1 , g_alpha, w_t);
    // //K1 end

    // K2 start
    generateFromG1(keys.K_2, pairing);
    element_pow_zn(keys.K_2, set.pp.g, keys.t); //K'
    // K2 end

    //K_x start
    keys.K_x = (element_t*) malloc(k*sizeof(element_t));
    for(int i = 0; i < k; i++){
        generateFromG1(keys.K_x[i], pairing);
        element_pow_zn(keys.K_x[i], set.pp.hx[i], keys.t);
    };
    // K_x end

    // //D_x start
    keys.D_x = (element_t *)malloc(m * sizeof(element_t));
    for(int i = 0; i < m; i++){
        element_t g_zx;
        element_t mul_tmp;
        generateFromG1(g_zx, pairing);
        generateFromG1(mul_tmp, pairing);
        element_pow_zn(g_zx, set.pp.g, set.msk.attribute[i]);
        element_mul(mul_tmp, g_zx, set.pp.Hx[0]);
        generateFromG1(keys.D_x[i], pairing);
        element_pow_zn(keys.D_x[i], mul_tmp, keys.t);
    };
    // //D_x end
    return keys;
};

KEY revokKeyGen(int personId, SETUP set, KEY keys){
    // revokeKey
    generateFromZr(keys.y, pairing);
    // D_0 start
    element_t b2;
    element_t b2y;
    element_t g_b2y;
    element_t g_alpha;
    generateFromZr(b2, pairing);
    element_mul_si(b2, set.msk.b, 2);
    generateFromZr(b2y, pairing);
    element_mul(b2y, b2, keys.y);
    generateFromG1(g_b2y, pairing);
    element_pow_zn(g_b2y, set.pp.g, b2y);
    generateFromG1(keys.D_0, pairing);
    generateFromG1(g_alpha, pairing);
    element_pow_zn(g_alpha, set.pp.g, set.msk.alpha);
    element_mul(keys.D_0, g_alpha, g_b2y);
    // // D_0 end

    // // D_1 start
    element_t bId;
    element_t g_bId;
    element_t g_bIdh;
    generateFromZr(bId, pairing);
    element_mul(bId, set.msk.b, set.msk.userId[personId]);
    generateFromG1(g_bId, pairing);
    element_pow_zn(g_bId, set.pp.g, bId);
    generateFromG1(g_bIdh, pairing);
    element_mul(g_bIdh, g_bId, set.pp.h);
    generateFromG1(keys.D_1, pairing);
    element_pow_zn(keys.D_1, g_bIdh, keys.y);
    // // D_1 end

    // //D_2 start
    element_t negativeY;
    generateFromZr(negativeY, pairing);
    element_neg(negativeY, keys.y);
    generateFromG1(keys.D_2, pairing);
    element_pow_zn(keys.D_2, set.pp.g, negativeY);
    // // D_2 end
    return keys;
};


AP accessPolicyGen(int l, int r, SETUP set){
    AP access_policy;
    // choose s' & s'' then compute s, set up the vectoer <s, y_1, y_2, ..., y_n>
    generateFromZr(access_policy.LSSS.s1, pairing); //s'

    // compute s'' start
    access_policy.revoke.s_r = (element_t*) malloc(REVOKE*sizeof(element_t));
    for(int i = 0; i < REVOKE; i++){
        generateFromZr(access_policy.revoke.s_r[i], pairing);
    };
    generateFromZr(access_policy.revoke.s2, pairing); // s''
    element_set0(access_policy.revoke.s2);
    for(int i = 0; i < REVOKE; i++){
        element_add(access_policy.revoke.s2, access_policy.revoke.s2, access_policy.revoke.s_r[i]);
    }
    // compute s'' end

    // <s, y_1, y_2, ..., y_n> start
    generateFromZr(access_policy.LSSS.s, pairing);
    element_add(access_policy.LSSS.s, access_policy.LSSS.s1, access_policy.revoke.s2);//s = s'+s''
    
    access_policy.LSSS.v = (element_t*) malloc(10*sizeof(element_t));
    generateFromZr(access_policy.LSSS.v[0], pairing);
    element_set(access_policy.LSSS.v[0], access_policy.LSSS.s);
    for (int i = 1; i < 10; i++)
    {
        generateFromZr(access_policy.LSSS.v[i], pairing); // <s, y_1, y_2, ..., y_n>
    };
    // <s, y_1, y_2, ..., y_n> end

    //lamda_i start
        //make access structure
    int accessStruct[l][COLUMN];
    for(int i = 0; i < l; i++)
    {
        for (int j = 0; j < COLUMN; j++)
        {
            accessStruct[i][j] = (rand() % 3) - 1;
        }
    }
    for(int i=0; i < l; i++){
        for(int j = 0; j < 10; j++){
            printf("%d \t", *(*(accessStruct+i)+j));
        }
        printf("\n");
    }
        // make access structure end
    access_policy.LSSS.lamda = (element_t*) malloc(l*sizeof(element_t));
    element_t vectorTemp;
    generateFromZr(vectorTemp, pairing);
    for(int i = 0; i< l; i++){
    generateFromZr(access_policy.LSSS.lamda[i], pairing);
    element_set0(access_policy.LSSS.lamda[i]);
    for (int j = 0; j < COLUMN; j++){
            element_mul_si(vectorTemp, access_policy.LSSS.v[j], *(*(accessStruct + i) + j));
            element_add(access_policy.LSSS.lamda[i], access_policy.LSSS.lamda[i], vectorTemp);
    };
    };
    //lamda_i end

    // pick r_1, r_2, ..., r_l start
        access_policy.LSSS.r_l = (element_t*) malloc(PREDICATE*sizeof(element_t));
        for(int i = 0; i < PREDICATE; i++){
            generateFromZr(access_policy.LSSS.r_l[i], pairing);
        }
    // pick r_1, r_2, ..., r_l end
    
    //compute f(k) start
    
    //compute f(k) end 


    return access_policy;
}

int main(int argc, char *argv[]){
    char param[1024];
    size_t count = fread(param, 1, 1024, stdin);
    if (!count)
        return 1;
    pairing_init_set_buf(pairing, param, count);
    int maxSizeOfPredicate, numberOfAttName;
    SETUP set = setup(ATTRIBUTE_NAME, ATTRIBUTE_VALUE);
    KEY keys = attributeKeyGen(ATTRIBUTE_NAME, ATTRIBUTE_VALUE, 3, set);
    keys = revokKeyGen(3, set, keys);
    AP access_policy = accessPolicyGen(PREDICATE, REVOKE, set);

    printf("Hello");
    return 0;
}