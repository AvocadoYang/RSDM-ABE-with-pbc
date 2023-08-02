#include <gmp.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

typedef long long unsigned int number;

typedef struct ct {
  mpz_t m;
} CT;

typedef struct msg {
  mpz_t m;
} MSG;

typedef struct msk {
  mpz_t p;
  mpz_t q;
  mpz_t d;
} MSK;

typedef struct pk {
  mpz_t n;
  mpz_t e;
} PK;

typedef struct keys {
  PK pk;
  MSK sk;
} KEY;

/* Key Generater Select Prime Numbers p, q, and compute n = pq */
/* Then Select e that < n, and which gcd(e, (p-1)(q-1)) = 1 */
/* example tuple: (p, q, n) = (61, 53, 17), (13, 19, 17), (531, 461, 107) */
KEY keygen() {
  KEY key;

#if defined(DEBUG)
  number p, q, e;
  scanf("%llu %llu %llu", &p, &q, &e);
  mpz_init_set_ui(key.sk.p, p);
  mpz_init_set_ui(key.sk.q, q);
  mpz_init_set_ui(key.pk.e, e);
#elif defined(DEFAULT)
  mpz_init_set_ui(key.sk.p, 61);
  mpz_init_set_ui(key.sk.q, 53);
  mpz_init_set_ui(key.pk.e, 17);
#else
  while (1) {
    gmp_randstate_t state;
    gmp_randinit_mt(state);
    gmp_randseed_ui(state, time(NULL));
    mpz_inits(key.sk.p, key.sk.q, key.pk.e);
    mpz_urandomb(key.sk.p, state, 128);
    mpz_urandomb(key.sk.q, state, 128);
    mpz_urandomb(key.pk.e, state, 32);
    mpz_nextprime(key.sk.p, key.sk.p);
    mpz_nextprime(key.sk.q, key.sk.q);
    mpz_nextprime(key.pk.e, key.pk.e);
    if (mpz_cmp(key.pk.e, key.sk.q) < 0 && mpz_cmp(key.pk.e, key.sk.p) < 0)
      break;
  }

#endif
  mpz_inits(key.pk.n, key.sk.d, NULL);
  mpz_mul(key.pk.n, key.sk.p, key.sk.q);

  mpz_t _p_1, _q_1, lambda;
  mpz_inits(_p_1, _q_1, lambda, NULL);

  mpz_sub_ui(_p_1, key.sk.p, 1);
  mpz_sub_ui(_q_1, key.sk.q, 1);
  mpz_lcm(lambda, _p_1, _q_1);
  mpz_invert(key.sk.d, key.pk.e, lambda);

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

/* RSA encryption */
/* CT = M^e mod n */
CT encryption(const PK pk, MSG msg) {
  CT ciphertext;
  mpz_init(ciphertext.m);
  mpz_powm(ciphertext.m, msg.m, pk.e, pk.n);
  return ciphertext;
}

/* RSA decryption */
/* M = CT^d mod n */
MSG decryption(const MSK sk, const PK pk, const CT ciphertext) {
  MSG plantext;
  mpz_init(plantext.m);
  mpz_powm(plantext.m, ciphertext.m, sk.d, pk.n);
  return plantext;
}

int main(int argc, char const *argv[]) {
  KEY key = keygen();

  printf("Initializing with p = %s, q = %s, d = %s, e = %s, n = %s\n",
         mpz_get_str(NULL, 0, key.sk.p), mpz_get_str(NULL, 0, key.sk.q),
         mpz_get_str(NULL, 0, key.sk.d), mpz_get_str(NULL, 0, key.pk.e),
         mpz_get_str(NULL, 0, key.pk.n));

  MSG msg = getmessage();
  CT ct = encryption(key.pk, msg);
  MSG pt = decryption(key.sk, key.pk, ct);

  printf("Output with Message = %s, CipherText = %s, Decrypt PlainText = %s\n",
         mpz_get_str(NULL, 0, msg.m), mpz_get_str(NULL, 0, ct.m),
         mpz_get_str(NULL, 0, pt.m));

  return 0;
}