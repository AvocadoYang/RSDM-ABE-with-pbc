#include <pbc/pbc.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "./generateFun.c"
#define ATTRIBUTE_NAME 50
#define ATTRIBUTE_VALUE 50
#define PREDICATECONTAIN 15
#define IdCount 20
#define COLUMN 10 
#define REVOKE 15
#define PREDICATE 10
#define ATTRIBUTENUM 20
#define MIN_VALUE 1
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

typedef struct attrSet {
    element_t *attribute;
} ASET;

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


typedef struct pt{
    element_t msg;
}PT;

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
AP accessPolicyGen(int, int, SETUP);
CT encrypt(int, int, PT, AP, SETUP);
PT attrDecrypt(SETUP, CT, AP, int, KEY, ASET, int);
PT revokeDecrypt(PT ,SETUP, CT, AP, int, KEY, ASET, int);
ASET getAttribute(int attNum, SETUP);

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
    };// attribute_Variable
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
    access_policy.LSSS.f_rox = (element_t*) malloc(COLUMN*sizeof(element_t));
    for (int i = 0; i < PREDICATE; i++){
        element_t temp;
        generateFromZr(temp, pairing);
        element_set0(temp);
        for (int randomElement = 0; randomElement < PREDICATECONTAIN; randomElement++){
            int randomNumber = rand() % 50;
            element_add(temp, temp, set.msk.attribute[randomNumber]);
        }
        generateFromZr(access_policy.LSSS.f_rox[i], pairing);
        element_set(access_policy.LSSS.f_rox[i], temp);
    };
    //compute f(k) end

    return access_policy;
}

PT getmessage(){
    PT MSGS;
    char MSG[] = "Message";
    element_init_GT(MSGS.msg, pairing);
    element_from_hash(MSGS.msg, MSG, sizeof(MSG));
    return MSGS;
}

CT encrypt(int l, int r, PT msg, AP access_policy, SETUP set){
    CT ct;
    // compute C start
    element_t Omega_s;
    generateFromGt(Omega_s, pairing);
    element_init_GT(ct.C, pairing);
    element_pow_zn(Omega_s, set.pp.omega, access_policy.LSSS.s);
    element_add(ct.C, Omega_s, msg.msg); // C
    // compute C end

    // compute C' start
    element_init_G1(ct.C_0, pairing);
    element_pow_zn(ct.C_0, set.pp.g, access_policy.LSSS.s1); // C'
    // compute C' end

    // compute C_i start
    ct.C_i = (element_t*) malloc(l*sizeof(element_t));
    element_t w_lamda;
    element_t h_s;
    element_t g_fx_ri;
    element_t negS;
    element_t negT;
    element_init_G1(negS, pairing);
    element_neg(negS, access_policy.LSSS.s1);
    element_init_G1(w_lamda, pairing);
    element_init_G1(h_s, pairing);
    element_init_G1(g_fx_ri, pairing);
    element_init_G1(negT, pairing);
    for(int i = 0; i < l; i++){
        element_init_G1(ct.C_i[i], pairing);
        element_neg(negT, access_policy.LSSS.r_l[i]);
        element_pow_zn(w_lamda, set.pp.w, access_policy.LSSS.lamda[i]);
        element_pow_zn(h_s, set.pp.hx[i], negS);
        element_pow_zn(g_fx_ri, set.pp.g, access_policy.LSSS.f_rox[i]);
        element_pow_zn(g_fx_ri, g_fx_ri, negT);
        element_mul(ct.C_i[i], w_lamda, h_s);
        element_mul(ct.C_i[i], ct.C_i[i], g_fx_ri);
    };
    element_clear(w_lamda);
    element_clear(h_s);
    element_clear(g_fx_ri);
    // compute C_i end

    // compute E'_i and E_ij start
    ct.E_i = (element_t*) malloc(l*sizeof(element_t));
    for(int i = 0; i < l; i++){
        element_init_G1(ct.E_i[i], pairing);
        element_pow_zn(ct.E_i[i], set.pp.g, access_policy.LSSS.r_l[i]);
    };
    ct.E_ij = (element_t *)malloc((l-1)*sizeof(element_t));
    for(int i = 0; i < l-1; i++){
        element_init_G1(ct.E_ij[i], pairing);
        element_pow_zn(ct.E_ij[i], set.pp.Hx[i], access_policy.LSSS.r_l[i]);
    };
    // compute E'_i and E_ij end

    // compute C_0 start
    element_init_G1(ct.C_0, pairing);
    element_pow_zn(ct.C_0, set.pp.g, access_policy.revoke.s2);
    // compute C_0 end

    // compute C_k1 and C_k2 start
    element_t bs_k;
    element_t b2;
    element_t b2ID_k;
    element_t h_b;
    element_t g_b2ID_k;
    element_init_Zr(bs_k, pairing);
    element_init_Zr(b2, pairing);
    element_init_Zr(b2ID_k, pairing);
    element_square(b2, set.msk.b);
    element_init_G1(h_b, pairing);
    element_init_G1(g_b2ID_k, pairing);

    ct.C_k1 = (element_t*) malloc(r*sizeof(element_t));
    ct.C_k2 = (element_t*) malloc(r*sizeof(element_t));
    int selectedNumbers[REVOKE];                   // 儲存選擇的數字的陣列
    int availableNumbers[IdCount - MIN_VALUE + 1]; // 儲存可選擇的數字的陣列
    int numAvailable = IdCount - MIN_VALUE ;    // 可選擇的數字總數
    srand(time(NULL)); // 初始化亂數種子
        // 初始化可選擇的數字陣列
    for (int i = 0; i < numAvailable; i++){
        availableNumbers[i] = i + MIN_VALUE;
    }
    // 從可選擇的數字中隨機選擇15個並存入selectedNumbers陣列
    for (int i = 0; i < REVOKE; i++){
        int randomIndex = rand() % numAvailable; // 隨機選擇索引
        selectedNumbers[i] = availableNumbers[randomIndex]; // 將選擇的數字存入selectedNumbers
        // 將已選擇的數字從可選擇的數字陣列中移除
        availableNumbers[randomIndex] = availableNumbers[numAvailable - 1];
        numAvailable--; // 可選擇的數字總數減少
    }
    for(int s_k = 0; s_k < REVOKE; s_k++){
        //C_k,1
        int idIndex = selectedNumbers[s_k];
        element_init_G1(ct.C_k1[s_k], pairing);
        element_mul(bs_k, set.msk.b, access_policy.revoke.s_r[s_k]);
        element_pow_zn(ct.C_k1[s_k], set.pp.g, bs_k); // g^bs''_k
        //C_k,2
        element_init_G1(ct.C_k2[s_k], pairing);
        element_mul(b2ID_k, b2, set.msk.userId[s_k]);
        element_pow_zn(g_b2ID_k, set.pp.g, b2ID_k);
        element_pow_zn(h_b, set.pp.h, set.msk.b);
        element_mul(ct.C_k2[s_k], g_b2ID_k, h_b);
        element_pow_zn(ct.C_k2[s_k], ct.C_k2[s_k], access_policy.revoke.s_r[s_k]);
    }
    // compute C_k1 and C_k2 end
        return ct;
}

ASET getAttribute(int attSetNum, SETUP set){
    ASET userAttributeSet;
    userAttributeSet.attribute = (element_t*) malloc(ATTRIBUTENUM*sizeof(element_t));
    for (int i = 0; i < ATTRIBUTENUM; i++){
        element_init_Zr(userAttributeSet.attribute[i], pairing);
        element_set(userAttributeSet.attribute[i], set.msk.attribute[i]);
    }
    return userAttributeSet;
};

PT attrDecrypt(SETUP set, CT ct, AP access_policy, int user_id, KEY keys, ASET userAttrSet, int l)
{
    PT decMsg;
    element_t decry1;
    element_t decry2;
    // attribute decrypt start
    element_t *w_x;
    element_t fx_kz;
    element_t ri_fx_kz;
    element_init_Zr(fx_kz, pairing);
    element_init_Zr(ri_fx_kz, pairing);
    w_x = (element_t *)malloc(l * sizeof(element_t));
    for(int i = 0; i < l; i++){
        for (int j = 0; j < ATTRIBUTENUM; j++){
            element_div(fx_kz, access_policy.LSSS.f_rox[i], userAttrSet.attribute[j]);
        }
        element_mul(ri_fx_kz, access_policy.LSSS.r_l[i], fx_kz);
        element_init_G1(w_x[i], pairing);
        element_pow_zn(w_x[i], set.pp.g, ri_fx_kz);
    }
    element_clear(fx_kz);
    element_clear(ri_fx_kz);

    element_t *decryBilinear; // e(w^{lamda_i}, g^t);
    element_t pairing1;
    element_t pairing2;
    element_t pairing3;
    element_t lsssResult;
    element_init_GT(pairing1, pairing);
    element_init_GT(pairing2, pairing);
    element_init_GT(pairing3, pairing);
    element_init_GT(lsssResult, pairing);
    element_set0(lsssResult);
    decryBilinear = (element_t*) malloc(l*sizeof(element_t));
    for(int i = 0; i <l; i++){
        element_pairing(pairing1, ct.C_i[i], keys.K_2);
        element_pairing(pairing2, ct.C_0, keys.K_x[i]);
        element_pairing(pairing3, w_x[i], keys.D_x[i]);
        element_init_GT(decryBilinear[i], pairing);
        element_mul(decryBilinear[i], pairing1, pairing2);
        element_mul(decryBilinear[i], decryBilinear[i], pairing3);
    };
    for(int i = 0; i <l; i++){
        element_add(lsssResult, lsssResult, decryBilinear[i]);
    };
    element_pairing(pairing1, ct.C_0, keys.K_1);
    element_init_GT(decry1, pairing);
    element_init_GT(decry1, pairing);
    element_div(decry1, pairing1, lsssResult);
    element_clear(lsssResult);
    // attribute decrypt end

    element_pairing(pairing1, ct.C_0, keys.D_0);
    element_t *idSubid;
    element_t iterateCk1;
    element_t iterateCk2;
    element_t Ck1_idsubid;
    element_t Ck2_idsubid;
    element_init_G1(Ck1_idsubid, pairing);
    element_init_G1(Ck2_idsubid, pairing);
    element_init_G1(iterateCk1, pairing);
    element_init_G1(iterateCk2, pairing);
    element_set0(iterateCk1);
    element_set0(iterateCk2);
    idSubid = (element_t *)malloc(REVOKE * sizeof(element_t));
    for (int i = 0; i < REVOKE; i++){
        element_init_Zr(idSubid[i], pairing);
        element_sub(idSubid[i], set.msk.userId[IdCount-2], set.msk.userId[i]);
        element_invert(idSubid[i], idSubid[i]);
    }
    for (int i = 0; i < REVOKE; i++){
        element_pow_zn(Ck1_idsubid, ct.C_k1[i], idSubid[i]);
        element_pow_zn(Ck2_idsubid, ct.C_k2[i], idSubid[i]);
        element_add(iterateCk1, iterateCk1, Ck1_idsubid);
        element_add(iterateCk2, iterateCk2, Ck2_idsubid);
    }
    element_pairing(pairing2, keys.D_1, iterateCk1);
    element_pairing(pairing3, keys.D_2, iterateCk2);
    element_init_GT(decry2, pairing);
    element_div(decry2, pairing1, pairing2);
    element_div(decry2, decry2, pairing3);
    element_init_GT(decMsg.msg, pairing);
    element_mul(decMsg.msg, decry1, decry2);
    element_div(decMsg.msg, ct.C, decMsg.msg);
    return decMsg;
};

PT revokeDecrypt(PT plantext, SETUP set, CT ct, AP access_policy, int user_id, KEY keys, ASET userAttrSet, int l){
    element_t pairing1;
    element_t pairing2;
    element_t pairing3;
    element_init_GT(pairing1, pairing);
    element_init_GT(pairing2, pairing);
    element_init_GT(pairing3, pairing);
    element_pairing(pairing1, ct.C_0, keys.D_0);
    element_t *idSubid;
    element_t iterateCk1;
    element_t iterateCk2;
    element_t Ck1_idsubid;
    element_t Ck2_idsubid;
    element_init_G1(Ck1_idsubid, pairing);
    element_init_G1(Ck2_idsubid, pairing);
    element_init_G1(iterateCk1, pairing);
    element_init_G1(iterateCk2, pairing);
    element_set0(iterateCk1);
    element_set0(iterateCk2);
    idSubid = (element_t*) malloc(REVOKE*sizeof(element_t));
    for(int i=0; i < REVOKE; i++){
        element_init_Zr(idSubid[i], pairing);
        element_sub(idSubid[i], set.msk.userId[IdCount-1], set.msk.userId[i]);
        element_invert(idSubid[i], idSubid[i]);
    }
    for(int i = 0; i < REVOKE; i++){
        element_pow_zn(Ck1_idsubid, ct.C_k1[i], idSubid[i]);
        element_pow_zn(Ck2_idsubid, ct.C_k2[i], idSubid[i]);
        element_add(iterateCk1, iterateCk1, Ck1_idsubid);
        element_add(iterateCk2, iterateCk2, Ck2_idsubid);
    }
    element_pairing(pairing2, keys.D_1, iterateCk1);
    element_pairing(pairing3, keys.D_2, iterateCk2);
    
    return plantext;
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
    PT MSG = getmessage();
    CT ct = encrypt(PREDICATE, REVOKE, MSG, access_policy, set);
    ASET userAttrSet = getAttribute(ATTRIBUTENUM, set);
    PT plantext = attrDecrypt(set, ct, access_policy, 20, keys, userAttrSet, PREDICATE);
    int result = element_cmp(MSG.msg, plantext.msg);
    printf("%d \n", result);
    printf("process over");
    return 0;
}