#include <gmp.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

typedef long long unsigned int number;

typedef struct ct {
  mpz_t c1;
  mpz_t c2;
} CT;

typedef struct msg {
  mpz_t m;
} MSG;

typedef struct pk {
  mpz_t p;
  mpz_t q;
  mpz_t h;
} PK;

typedef mpz_t SK;

typedef struct key {
  PK pk;
  SK sk;
} KEY;

KEY keygen() {
  KEY key;
  mpz_inits(key.pk.h, key.pk.p, key.pk.q, key.sk, NULL);
#if defined(DEBUG)
  number p, q, x;
  scanf("%llu %llu %llu", &p, &q, &x);
  mpz_init_set_ui(key.pk.p, p);
  mpz_init_set_ui(key.pk.q, q);
  mpz_init_set_ui(key.sk, x);
#elif defined(DEFAULT)
  mpz_init_set_ui(key.pk.p, 107);
  mpz_init_set_ui(key.pk.q, 2);
  mpz_init_set_ui(key.sk, 67);
#else
  gmp_randstate_t state;
  gmp_randinit_mt(state);
  gmp_randseed_ui(state, time(NULL));
  // suppose p > q and generate x which is also sk < p
  while (1) {
    mpz_urandomb(key.pk.p, state, 128);
    mpz_urandomb(key.pk.q, state, 128);
    mpz_urandomb(key.sk, state, 32);
    mpz_nextprime(key.pk.p, key.pk.p);
    mpz_nextprime(key.pk.q, key.pk.q);
    mpz_nextprime(key.sk, key.sk);
    if (mpz_cmp(key.pk.p, key.pk.q) > 0 && mpz_cmp(key.pk.p, key.sk) > 0)
      break;
  }
#endif
  // compute h = q^x mod p
  mpz_powm(key.pk.h, key.pk.q, key.sk, key.pk.p);
  return key;
}

/* input the message */
MSG getmessage() {
  MSG msg;
#if defined(DEBUG)
  number _msg;
  scanf("%llu", &_msg);
  mpz_init_set_ui(msg.m, _msg);
#elif defined(DEFAULT)
  mpz_init_set_si(msg.m, 35);
#else
  gmp_randstate_t state;
  gmp_randinit_mt(state);
  gmp_randseed_ui(state, time(NULL));
  mpz_init(msg.m);
  mpz_urandomb(msg.m, state, 32);
#endif
  return msg;
}

CT encryption(PK pk, MSG msg) {
  CT ct;
  mpz_t y, s;
#if defined(DEBUG)
  number _y;
  scanf("%llu", &_y);
  mpz_init_set_ui(y, _y);
#elif defined(DEFAULT)
  mpz_init_set_ui(y, 61);
#else
  gmp_randstate_t state;
  gmp_randinit_mt(state);
  gmp_randseed_ui(state, time(NULL));
  // suppose p > q and generate x which is also sk < p
  while (1) {
    mpz_init(y);
    mpz_urandomb(y, state, 32);
    mpz_nextprime(y, y);
    if (mpz_cmp(pk.p, y) > 0)
      break;
  }
#endif
  mpz_inits(s, ct.c1, ct.c2, NULL);
  mpz_powm(s, pk.h, y, pk.p);
  mpz_powm(ct.c1, pk.q, y, pk.p);
  mpz_mul(ct.c2, msg.m, s);
  return ct;
}

MSG decryption(PK pk, SK sk, CT ct) {
  MSG msg;
  mpz_t s;
  mpz_inits(s, msg.m, NULL);
  mpz_powm(s, ct.c1, sk, pk.p);
  mpz_tdiv_q(msg.m, ct.c2, s);
  return msg;
}

int main() {
  KEY key = keygen();
  printf("h = %s\np = %s\nq = %s\nsk = %s\n", mpz_get_str(NULL, 0, key.pk.h),
         mpz_get_str(NULL, 0, key.pk.p), mpz_get_str(NULL, 0, key.pk.q),
         mpz_get_str(NULL, 0, key.sk));
  MSG msg = getmessage();
  CT ct = encryption(key.pk, msg);
  printf("c1 = %s\nc2 = %s\n", mpz_get_str(NULL, 0, ct.c1),
         mpz_get_str(NULL, 0, ct.c2));
  MSG result = decryption(key.pk, key.sk, ct);
  printf("message = %s, result = %s\n", mpz_get_str(NULL, 0, msg.m),
         mpz_get_str(NULL, 0, result.m));
  return 0;
}