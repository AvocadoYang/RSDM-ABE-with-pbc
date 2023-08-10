#include <pbc/pbc.h>
#include <stdio.h>
#include <time.h>

pairing_t pairing;
clock_t start, end;

typedef element_t PK;
typedef element_t SK;

typedef struct msk {
  element_t s;
} MSK;

typedef struct pp {
  element_t p;
  element_t pub;
} PP;

typedef struct set {
  MSK msk;
  PP pp;
} SETUP;

typedef struct keys {
  PK pk;
  SK sk;
} KEY;

typedef struct ct {
  element_t c1;
  element_t c2;
} CT;

typedef struct pt {
  element_t msg;
} PT;

SETUP setup() {
  SETUP set;
  element_init_G1(set.pp.p, pairing);
  element_random(set.pp.p);
  element_init_Zr(set.msk.s, pairing);
  element_random(set.msk.s);
  element_init_G1(set.pp.pub, pairing);
  element_mul_zn(set.pp.pub, set.pp.p, set.msk.s);
  return set;
}

KEY extract(PP pp, MSK msk) {
  KEY key;
  char ID[] = "IDS";
  element_init_G1(key.pk, pairing);
  element_init_G1(key.sk, pairing);
  element_from_hash(key.pk, ID, sizeof(ID));
  element_mul_zn(key.sk, key.pk, msk.s);
  return key;
}

CT encryption(PP pp, PK pk, element_t msg) {

  CT ciphertext;
  element_t r, gid;
  element_init_Zr(r, pairing);
  element_random(r);
  element_init_G1(ciphertext.c1, pairing);
  element_mul_zn(ciphertext.c1, pp.p, r);

  element_init_GT(gid, pairing);
  element_pairing(gid, pk, pp.pub);
  element_pow_zn(gid, gid, r);
  element_init_GT(ciphertext.c2, pairing);
  element_add(ciphertext.c2, msg, gid);

  return ciphertext;
}

PT decryption(SK sk, CT ct) {
  PT plaintext;
  element_t e_sk_U;
  element_init_GT(e_sk_U, pairing);
  element_pairing(e_sk_U, sk, ct.c1);
  element_init_GT(plaintext.msg, pairing);
  element_sub(plaintext.msg, ct.c2, e_sk_U);
  return plaintext;
}

int main(int argc, char const *argv[]) {

  char param[1024];
  size_t count = fread(param, 1, 1024, stdin);
  if (!count)
    return 1;
  pairing_init_set_buf(pairing, param, count);

  start = clock();
  SETUP set = setup();
  end = clock();
#ifdef 2
  printf("setup exec time: %f\n", (double)(end - start) / CLOCKS_PER_SEC);
#endif
#ifdef DEBUG
  element_printf("Ppub = %B\np = %B\ns = %B\n", set.pp.pub, set.pp.p,
                set.msk.s);
#endif
  start = clock();
  KEY key = extract(set.pp, set.msk);
  end = clock();
#ifdef TIME
  printf("key extract exec time: %f\n", (double)(end - start) / CLOCKS_PER_SEC);
#endif
#ifdef DEBUG
  element_printf("PK = %B\nSK = %B\n", key.pk, key.sk);
#endif
  element_t msg;
  char MSG[] = "Message";
  element_init_GT(msg, pairing);
  element_from_hash(msg, MSG, sizeof(MSG));

  start = clock();
  CT ct = encryption(set.pp, key.pk, msg);
  end = clock();
#ifdef TIME
  printf("encryption exec time: %f\n", (double)(end - start) / CLOCKS_PER_SEC);
#endif
  start = clock();
  PT result = decryption(key.sk, ct);
  end = clock();
#ifdef TIME
  printf("decryption exec time: %f\n", (double)(end - start) / CLOCKS_PER_SEC);
#endif
#ifdef DEBUG
  element_printf("ct1 = %B\nct2 = %B\nPT = %B\n", ct.c1, ct.c2, result.msg);
#endif
  printf("%d\n", element_cmp(result.msg, msg));
  return 0;
}
