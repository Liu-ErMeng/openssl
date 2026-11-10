#define OPENSSL_SUPPRESS_DEPRECATED
#include <stdio.h>
#include <openssl/bn.h>
#include <openssl/core_names.h>
#include <openssl/ec.h>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/params.h>

extern const EC_METHOD *ossl_ec_GFp_nistp384_method(void);

#define REQUIRE(expr)                                                       \
    do {                                                                    \
        if (!(expr)) {                                                      \
            fprintf(stderr, "Failed: %s\n", #expr);                        \
            ERR_print_errors_fp(stderr);                                    \
            goto end;                                                       \
        }                                                                   \
    } while (0)

int main(void)
{
    int ret = 1, failures = 0, i, len, ok;
    BN_CTX *ctx = BN_CTX_new();
    EC_GROUP *group = EC_GROUP_new_by_curve_name(NID_secp384r1);
    EC_POINT *minus = NULL, *sixteen = NULL, *expected = NULL, *out = NULL;
    BIGNUM *a = BN_new(), *b = BN_new(), *r = BN_new(), *s = BN_new();
    BIGNUM *m = BN_new(), *inverse = BN_new();
    const EC_POINT *generator, *points[2];
    const BIGNUM *scalars[2], *order;
    ECDSA_SIG *signature = NULL;
    EVP_PKEY *key = NULL;
    EVP_PKEY_CTX *import = NULL, *verify = NULL;
    unsigned char public_key[97], digest[48], *der = NULL, *cursor;
    char curve[] = "secp384r1";
    OSSL_PARAM params[3];

    REQUIRE(ctx != NULL && group != NULL && a != NULL && b != NULL);
    REQUIRE(r != NULL && s != NULL && m != NULL && inverse != NULL);
    REQUIRE(EC_GROUP_method_of(group) == ossl_ec_GFp_nistp384_method());
    generator = EC_GROUP_get0_generator(group);
    order = EC_GROUP_get0_order(group);
    REQUIRE(generator != NULL && order != NULL);
    minus = EC_POINT_dup(generator, group);
    sixteen = EC_POINT_dup(generator, group);
    out = EC_POINT_new(group);
    REQUIRE(minus != NULL && sixteen != NULL && out != NULL);
    REQUIRE(EC_POINT_invert(group, minus, ctx));
    for (i = 0; i < 4; i++)
        REQUIRE(EC_POINT_dbl(group, sixteen, sixteen, ctx));
    expected = EC_POINT_dup(sixteen, group);
    REQUIRE(expected != NULL && EC_POINT_invert(group, expected, ctx));
    REQUIRE(BN_set_word(a, 32) && BN_set_word(b, 16));
    points[0] = minus;
    points[1] = generator;
    scalars[0] = a;
    scalars[1] = b;
    REQUIRE(EC_POINTs_mul(group, out, NULL, 2, points, scalars, ctx));
    ok = EC_POINT_is_on_curve(group, out, ctx) == 1
        && EC_POINT_cmp(group, out, expected, ctx) == 0;
    printf("EC_POINTs_mul cancellation: %s\n", ok ? "PASS" : "FAIL");
    failures += !ok;

    REQUIRE(EC_POINT_mul(group, out, a, minus, b, ctx));
    ok = EC_POINT_is_on_curve(group, out, ctx) == 1
        && EC_POINT_cmp(group, out, sixteen, ctx) == 0;
    printf("EC_POINT_mul generator cancellation: %s\n", ok ? "PASS" : "FAIL");
    failures += !ok;

    REQUIRE(EC_POINT_get_affine_coordinates(group, sixteen, r, NULL, ctx));
    REQUIRE(BN_nnmod(r, r, order, ctx));
    REQUIRE(BN_mod_inverse(inverse, b, order, ctx) != NULL);
    REQUIRE(BN_mod_mul(s, r, inverse, order, ctx));
    REQUIRE(BN_mod_lshift1(m, r, order, ctx));
    REQUIRE(BN_bn2binpad(m, digest, sizeof(digest)) == sizeof(digest));
    signature = ECDSA_SIG_new();
    REQUIRE(signature != NULL);
    REQUIRE(ECDSA_SIG_set0(signature, r, s));
    r = s = NULL;
    len = i2d_ECDSA_SIG(signature, NULL);
    REQUIRE(len > 0);
    der = OPENSSL_malloc(len);
    REQUIRE(der != NULL);
    cursor = der;
    REQUIRE(i2d_ECDSA_SIG(signature, &cursor) == len);

    REQUIRE(EC_POINT_point2oct(group, minus, POINT_CONVERSION_UNCOMPRESSED,
                public_key, sizeof(public_key), ctx) == sizeof(public_key));
    params[0] = OSSL_PARAM_construct_utf8_string(OSSL_PKEY_PARAM_GROUP_NAME, curve, 0);
    params[1] = OSSL_PARAM_construct_octet_string(OSSL_PKEY_PARAM_PUB_KEY,
        public_key, sizeof(public_key));
    params[2] = OSSL_PARAM_construct_end();
    import = EVP_PKEY_CTX_new_from_name(NULL, "EC", NULL);
    REQUIRE(import != NULL && EVP_PKEY_fromdata_init(import) > 0);
    REQUIRE(EVP_PKEY_fromdata(import, &key, EVP_PKEY_PUBLIC_KEY, params) > 0);
    verify = EVP_PKEY_CTX_new_from_pkey(NULL, key, NULL);
    REQUIRE(verify != NULL && EVP_PKEY_public_check(verify) > 0);
    REQUIRE(EVP_PKEY_verify_init(verify) > 0);
    REQUIRE(EVP_PKEY_CTX_set_signature_md(verify, EVP_sha384()) > 0);
    REQUIRE(EVP_PKEY_verify(verify, der, len, digest, sizeof(digest)) == 1);
    digest[47] ^= 1;
    REQUIRE(EVP_PKEY_verify(verify, der, len, digest, sizeof(digest)) == 0);
    printf("EVP_PKEY_verify valid/modified digest: PASS\n");
    ret = failures != 0;
end:
    OPENSSL_free(der);
    EVP_PKEY_CTX_free(verify);
    EVP_PKEY_CTX_free(import);
    EVP_PKEY_free(key);
    ECDSA_SIG_free(signature);
    BN_free(a);
    BN_free(b);
    BN_free(r);
    BN_free(s);
    BN_free(m);
    BN_free(inverse);
    EC_POINT_free(minus);
    EC_POINT_free(sixteen);
    EC_POINT_free(expected);
    EC_POINT_free(out);
    EC_GROUP_free(group);
    BN_CTX_free(ctx);
    return ret;
}
