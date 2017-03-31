/*
 * D-Bus Type Enumerator
 */

#include <assert.h>
#include <errno.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
/* s*$&! gmp depends on include order; order after std-headers */
#include <gmp.h>
#include "dbus-typenum.h"

#define _public_ __attribute__((__visibility__("default")))

typedef struct DBusTypenumState DBusTypenumState;

enum {
        DBUS_TYPENUM_BASIC_b,
        DBUS_TYPENUM_BASIC_y,
        DBUS_TYPENUM_BASIC_n,
        DBUS_TYPENUM_BASIC_q,
        DBUS_TYPENUM_BASIC_i,
        DBUS_TYPENUM_BASIC_u,
        DBUS_TYPENUM_BASIC_x,
        DBUS_TYPENUM_BASIC_t,
        DBUS_TYPENUM_BASIC_h,
        DBUS_TYPENUM_BASIC_d,
        DBUS_TYPENUM_BASIC_s,
        DBUS_TYPENUM_BASIC_o,
        DBUS_TYPENUM_BASIC_g,
        _DBUS_TYPENUM_BASIC_N,
};

enum {
        DBUS_TYPENUM_COMPOUND_a,
        DBUS_TYPENUM_COMPOUND_r,
        DBUS_TYPENUM_COMPOUND_e,
        _DBUS_TYPENUM_COMPOUND_N,
        DBUS_TYPENUM_COMPOUND_m = _DBUS_TYPENUM_COMPOUND_N,
        _DBUS_TYPENUM_COMPOUND_N_MAYBE,
};

struct DBusTypenumState {
        DBusTypenumState *parent;
        unsigned int rule;
        mpz_t seed;
};

struct DBusTypenum {
        unsigned int n_compound;
        DBusTypenumState *tip;
        DBusTypenumState *unused;
        mpz_t seed;
        mpz_t root;
        mpz_t root_squared;
        mpz_t index;
};

/*
 * (Inverse) Pair
 * ==============
 *
 * These functions implement a 'pair-function' and its inverse. It is quite
 * similar to the '(inverse) Cantor pairing function', but way easier to
 * calculate. The Cantor-pairing-function would have worked as well, though.
 */

static void dbus_typenum_pi(DBusTypenum *gen, mpz_t seed, mpz_t pi1, mpz_t pi2) {
        int res;

        /*
         * Pairing function that takes @pi1 and @pi2 and returns the pair as
         * @seed. We use @gen as temporary variables, to avoid dynamic
         * allocation on each call.
         */

        /* CAREFUL: pi1/pi2/seed may *overlap*! */

        res = mpz_cmp(pi1, pi2);
        if (res < 0) {
                mpz_pow_ui(gen->index, pi2, 2);
                mpz_add(seed, gen->index, pi1);
        } else {
                mpz_pow_ui(gen->index, pi1, 2);
                mpz_add(gen->index, gen->index, pi1);
                mpz_add(seed, gen->index, pi2);
        }
}

static void dbus_typenum_inverse_pi(DBusTypenum *gen, mpz_t pi1, mpz_t pi2, mpz_t seed) {
        int res;

        /*
         * Inverse pairing function that takes @seed as input and returns the
         * inverse-pair as @pi1 and @pi2. We use storage on @gen as temporary
         * variables, to avoid dynamic allocation on each call.
         */

        /* CAREFUL: pi1/pi2/seed may *overlap*! */

        mpz_sqrt(gen->root, seed);
        mpz_pow_ui(gen->root_squared, gen->root, 2);
        mpz_sub(gen->index, seed, gen->root_squared);

        res = mpz_cmp(gen->index, gen->root);
        if (res < 0) {
                mpz_sub(pi1, seed, gen->root_squared);
                mpz_set(pi2, gen->root);
        } else {
                mpz_sub(gen->index, seed, gen->root_squared);
                mpz_sub(pi2, gen->index, gen->root);
                mpz_set(pi1, gen->root);
        }
}

/*
 * State
 * =====
 *
 * To implement a context-free grammar, we chose a deterministic push-down
 * automata (PDA). It is very simple: We have a push-down stack of
 * DBusTypenumState objects. The top object is accessible via gen->tip. You can
 * push and pop states, according to your needs. We cache old states for later
 * reuse, which avoids reallocation of GnuMP objects.
 */

static DBusTypenumState *dbus_typenum_state_new(void) {
        DBusTypenumState *state;

        state = calloc(1, sizeof(*state));
        assert(state);

        mpz_init(state->seed);

        return state;
}

static DBusTypenumState *dbus_typenum_state_free(DBusTypenumState *state) {
        if (!state)
                return NULL;

        mpz_clear(state->seed);
        free(state);

        return NULL;
}

static DBusTypenumState *dbus_typenum_push(DBusTypenum *gen) {
        DBusTypenumState *state;

        if (gen->unused) {
                state = gen->unused;
                gen->unused = state->parent;
        } else {
                state = dbus_typenum_state_new();
        }

        state->parent = gen->tip;
        gen->tip = state;
        return state;
}

static DBusTypenumState *dbus_typenum_pop(DBusTypenum *gen) {
        DBusTypenumState *state;

        if (gen->tip) {
                state = gen->tip;
                gen->tip = state->parent;
                state->parent = gen->unused;
                gen->unused = state;
        }

        return gen->tip;
}

/*
 * Rules
 * =====
 *
 * These rules implement a context-free grammar that represents the D-Bus type
 * language. The rules are as follows:
 *   (terminals are lower-case, non-terminals are upper-case)
 *
 *     TYPE ::= basic
 *              | 'v'
 *              | '(' ')'
 *              | 'm' TYPE
 *              | 'a' TYPE
 *              | '(' TUPLE ')'
 *              | '{' PAIR '}'
 *     TUPLE ::= TYPE | TYPE TUPLE
 *     PAIR ::= basic TYPE
 *
 *     basic ::= integer | float | string
 *     integer ::= 'b' | 'y' | 'n' | 'q' | 'i' | 'u' | 'x' | 't' | 'h'
 *     float ::= 'd'
 *     string ::= 's' | 'o' | 'g'
 *
 * Rather than implementing a parser, we implement a dbus_typenum here. On each
 * rule, we decide based on its seed which possible evaluation to take. We then
 * modify the seed based on the decision we placed and pass the seed to the
 * sub-rule that we chose.
 *
 * To guarantee that we get a proper bijection between the natural numbers (our
 * seed), and the GVariant type-space, we must make sure to never throw away
 * information from the seed, but also exactly take away the information that
 * was required for our decision. In most cases this is straightforward, but
 * some parts (eg., TUPLE evaluation) need to split the seed. We use an inverse
 * pair function for that (a variation of Cantor's pair-function). You are
 * recommended to read up 'diagonalisation' and '(inverse) pair-functions'
 * before trying to understand the implementation.
 */

enum {
        DBUS_TYPENUM_RULE_DONE,
        DBUS_TYPENUM_RULE_TYPE,
        DBUS_TYPENUM_RULE_TUPLE,
        DBUS_TYPENUM_RULE_TUPLE_CLOSE,
        DBUS_TYPENUM_RULE_PAIR,
        DBUS_TYPENUM_RULE_PAIR_CLOSE,
        _DBUS_TYPENUM_RULE_N,
};

static char dbus_typenum_map_basic(unsigned long val) {
        switch (val) {
        case DBUS_TYPENUM_BASIC_b:
                return 'b';
        case DBUS_TYPENUM_BASIC_y:
                return 'y';
        case DBUS_TYPENUM_BASIC_n:
                return 'n';
        case DBUS_TYPENUM_BASIC_q:
                return 'q';
        case DBUS_TYPENUM_BASIC_i:
                return 'i';
        case DBUS_TYPENUM_BASIC_u:
                return 'u';
        case DBUS_TYPENUM_BASIC_x:
                return 'x';
        case DBUS_TYPENUM_BASIC_t:
                return 't';
        case DBUS_TYPENUM_BASIC_h:
                return 'h';
        case DBUS_TYPENUM_BASIC_d:
                return 'd';
        case DBUS_TYPENUM_BASIC_s:
                return 's';
        case DBUS_TYPENUM_BASIC_o:
                return 'o';
        case DBUS_TYPENUM_BASIC_g:
                return 'g';
        default:
                assert(0);
                return 0;
        }
}

static int dbus_typenum_rule_TYPE(DBusTypenum *gen) {
        DBusTypenumState *next, *state = gen->tip;
        unsigned long val;
        int res;

        /*
         * TYPE ::= basic
         *          | 'v'
         *          | '(' ')'
         *          | 'm' TYPE
         *          | 'a' TYPE
         *          | '(' TUPLE ')'
         *          | '{' PAIR '}'
         */

        res = mpz_cmp_ui(state->seed, _DBUS_TYPENUM_BASIC_N + 2);
        if (res < 0) {
                /*
                 * TYPE ::= basic | 'v' | '(' ')'
                 */
                val = mpz_get_ui(state->seed);
                switch (val) {
                case _DBUS_TYPENUM_BASIC_N + 0:
                        /*
                         * TYPE ::= 'v'
                         */
                        dbus_typenum_pop(gen);
                        return 'v';
                case _DBUS_TYPENUM_BASIC_N + 1:
                        /*
                         * TYPE ::= '(' ')'
                         */
                        state->rule = DBUS_TYPENUM_RULE_TUPLE_CLOSE;
                        return '(';
                default:
                        /*
                         * TYPE ::= basic
                         */
                        dbus_typenum_pop(gen);
                        return dbus_typenum_map_basic(val);
                }
        } else {
                /*
                 * TYPE ::= 'm' TYPE | 'a' TYPE | '(' TUPLE ')' | '{' PAIR '}'
                 */
                mpz_sub_ui(state->seed, state->seed, _DBUS_TYPENUM_BASIC_N + 2);
                val = mpz_fdiv_q_ui(state->seed, state->seed, gen->n_compound);
                switch (val) {
                case DBUS_TYPENUM_COMPOUND_a:
                        /*
                         * TYPE ::= 'a' TYPE
                         */
                        state->rule = DBUS_TYPENUM_RULE_TYPE;
                        return 'a';
                case DBUS_TYPENUM_COMPOUND_r:
                        /*
                         * TYPE ::= '(' TUPLE ')'
                         */
                        state->rule = DBUS_TYPENUM_RULE_TUPLE_CLOSE;
                        next = dbus_typenum_push(gen);
                        next->rule = DBUS_TYPENUM_RULE_TUPLE;
                        mpz_set(next->seed, state->seed);
                        return '(';
                case DBUS_TYPENUM_COMPOUND_e:
                        /*
                         * TYPE ::= '{' PAIR '}'
                         */
                        state->rule = DBUS_TYPENUM_RULE_PAIR_CLOSE;
                        next = dbus_typenum_push(gen);
                        next->rule = DBUS_TYPENUM_RULE_PAIR;
                        mpz_set(next->seed, state->seed);
                        return '{';
                case DBUS_TYPENUM_COMPOUND_m:
                        /*
                         * TYPE ::= 'm' TYPE
                         */
                        state->rule = DBUS_TYPENUM_RULE_TYPE;
                        return 'm';
                default:
                        assert(0);
                        return 0;
                }
        }
}

static char dbus_typenum_rule_TUPLE(DBusTypenum *gen) {
        DBusTypenumState *next, *state = gen->tip;
        unsigned long val;

        /*
         * TUPLE ::= TYPE | TYPE TUPLE
         */

        val = mpz_fdiv_q_ui(state->seed, state->seed, 2);
        switch (val) {
        case 0:
                state->rule = DBUS_TYPENUM_RULE_TYPE;
                return dbus_typenum_rule_TYPE(gen);
        case 1:
                next = dbus_typenum_push(gen);
                next->rule = DBUS_TYPENUM_RULE_TYPE;
                dbus_typenum_inverse_pi(gen, state->seed, next->seed, state->seed);
                return dbus_typenum_rule_TYPE(gen);
        default:
                assert(0);
                return 0;
        }
}

static char dbus_typenum_rule_TUPLE_CLOSE(DBusTypenum *gen) {
        dbus_typenum_pop(gen);
        return ')';
}

static char dbus_typenum_rule_PAIR(DBusTypenum *gen) {
        DBusTypenumState *state = gen->tip;
        unsigned long val;

        /*
         * PAIR ::= basic TYPE
         */

        val = mpz_fdiv_q_ui(state->seed, state->seed, _DBUS_TYPENUM_BASIC_N);
        state->rule = DBUS_TYPENUM_RULE_TYPE;
        return dbus_typenum_map_basic(val);
}

static char dbus_typenum_rule_PAIR_CLOSE(DBusTypenum *gen) {
        dbus_typenum_pop(gen);
        return '}';
}

/*
 * Parser
 * ======
 *
 * This parser implements the inverse operation of the generator-rules defined
 * above. It simply inverts each step that the generator does, to allow callers
 * to turn a given gvariant into its corresponding seed.
 *
 * The grammar and names are exactly the same for the inverse operation.
 */

enum {
        DBUS_TYPENUM_PARSER_DONE,
        DBUS_TYPENUM_PARSER_FAIL,
        DBUS_TYPENUM_PARSER_TYPE,
        DBUS_TYPENUM_PARSER_MAYBE,
        DBUS_TYPENUM_PARSER_ARRAY,
        DBUS_TYPENUM_PARSER_TUPLE,
        DBUS_TYPENUM_PARSER_TUPLE_CLOSE,
        DBUS_TYPENUM_PARSER_PAIR,
        DBUS_TYPENUM_PARSER_PAIR_CLOSE,
        _DBUS_TYPENUM_PARSER_N,
};

static unsigned long dbus_typenum_unmap_basic(char c) {
        switch (c) {
        case 'b':
                return DBUS_TYPENUM_BASIC_b;
        case 'y':
                return DBUS_TYPENUM_BASIC_y;
        case 'n':
                return DBUS_TYPENUM_BASIC_n;
        case 'q':
                return DBUS_TYPENUM_BASIC_q;
        case 'i':
                return DBUS_TYPENUM_BASIC_i;
        case 'u':
                return DBUS_TYPENUM_BASIC_u;
        case 'x':
                return DBUS_TYPENUM_BASIC_x;
        case 't':
                return DBUS_TYPENUM_BASIC_t;
        case 'h':
                return DBUS_TYPENUM_BASIC_h;
        case 'd':
                return DBUS_TYPENUM_BASIC_d;
        case 's':
                return DBUS_TYPENUM_BASIC_s;
        case 'o':
                return DBUS_TYPENUM_BASIC_o;
        case 'g':
                return DBUS_TYPENUM_BASIC_g;
        default:
                return _DBUS_TYPENUM_BASIC_N;
        }
}

static void dbus_typenum_fold_MAYBE(DBusTypenum *gen) {
        DBusTypenumState *next, *state = gen->tip;

        mpz_mul_ui(state->seed, state->seed, gen->n_compound);
        mpz_add_ui(state->seed, state->seed, DBUS_TYPENUM_COMPOUND_m);
        mpz_add_ui(state->seed, state->seed, _DBUS_TYPENUM_BASIC_N + 2);

        next = dbus_typenum_pop(gen);
        mpz_set(next->seed, state->seed);
}

static void dbus_typenum_fold_ARRAY(DBusTypenum *gen) {
        DBusTypenumState *next, *state = gen->tip;

        mpz_mul_ui(state->seed, state->seed, gen->n_compound);
        mpz_add_ui(state->seed, state->seed, DBUS_TYPENUM_COMPOUND_a);
        mpz_add_ui(state->seed, state->seed, _DBUS_TYPENUM_BASIC_N + 2);

        next = dbus_typenum_pop(gen);
        mpz_set(next->seed, state->seed);
}

static int dbus_typenum_fold(DBusTypenum *gen) {
        DBusTypenumState *state, *next;

        for (;;) {
                state = gen->tip;
                switch (state->rule) {
                case DBUS_TYPENUM_PARSER_MAYBE:
                        dbus_typenum_fold_MAYBE(gen);
                        break;
                case DBUS_TYPENUM_PARSER_ARRAY:
                        dbus_typenum_fold_ARRAY(gen);
                        break;
                case DBUS_TYPENUM_PARSER_TUPLE_CLOSE:
                        next = dbus_typenum_pop(gen);
                        mpz_set(next->seed, state->seed);
                        break;
                case DBUS_TYPENUM_PARSER_TUPLE:
                        next = dbus_typenum_push(gen);
                        next->rule = DBUS_TYPENUM_PARSER_TUPLE;
                        /* fallthrough */
                default:
                        return 0;
                }
        }
}

static int dbus_typenum_parser_TYPE(DBusTypenum *gen, char c) {
        DBusTypenumState *next, *state = gen->tip;
        unsigned long val;

        val = dbus_typenum_unmap_basic(c);
        if (val < _DBUS_TYPENUM_BASIC_N) {
                next = dbus_typenum_pop(gen);
                mpz_set_ui(next->seed, val);
                return dbus_typenum_fold(gen);
        } else if (c == 'v') {
                next = dbus_typenum_pop(gen);
                mpz_set_ui(next->seed, _DBUS_TYPENUM_BASIC_N);
                return dbus_typenum_fold(gen);
        } else {
                switch (c) {
                case 'a':
                        state->rule = DBUS_TYPENUM_PARSER_ARRAY;
                        next = dbus_typenum_push(gen);
                        next->rule = DBUS_TYPENUM_PARSER_TYPE;
                        break;
                case '(':
                        state->rule = DBUS_TYPENUM_PARSER_TUPLE_CLOSE;
                        next = dbus_typenum_push(gen);
                        next->rule = DBUS_TYPENUM_PARSER_TUPLE;
                        return 0;
                case '{':
                        state->rule = DBUS_TYPENUM_PARSER_PAIR;
                        return 0;
                case 'm':
                        if (gen->n_compound >= _DBUS_TYPENUM_COMPOUND_N_MAYBE) {
                                state->rule = DBUS_TYPENUM_PARSER_MAYBE;
                                next = dbus_typenum_push(gen);
                                next->rule = DBUS_TYPENUM_PARSER_TYPE;
                                break;
                        }
                        /* fallthrough */
                default:
                        state->rule = DBUS_TYPENUM_PARSER_FAIL;
                        return -EINVAL;
                }
        }

        return 0;
}

static int dbus_typenum_parser_TUPLE(DBusTypenum *gen, char c) {
        DBusTypenumState *next, *state;

        if (c != ')') {
                next = dbus_typenum_push(gen);
                next->rule = DBUS_TYPENUM_PARSER_TYPE;
                return dbus_typenum_parser_TYPE(gen, c);
        }

        state = dbus_typenum_pop(gen);

        if (state->rule != DBUS_TYPENUM_PARSER_TUPLE) {
                /* unit type "()" */
                mpz_set_ui(state->seed, _DBUS_TYPENUM_BASIC_N + 1);
                return dbus_typenum_fold(gen);
        }

        /* fold decision to end TUPLE */
        mpz_mul_ui(state->seed, state->seed, 2);

        /* fold each decision to continue TUPLE */
        for (next = dbus_typenum_pop(gen);
             next->rule == DBUS_TYPENUM_PARSER_TUPLE;
             next = dbus_typenum_pop(gen)) {
                dbus_typenum_pi(gen, state->seed, state->seed, next->seed);
                mpz_mul_ui(state->seed, state->seed, 2);
                mpz_add_ui(state->seed, state->seed, 1);
        }

        /* fold decision to use TUPLE */
        mpz_mul_ui(state->seed, state->seed, gen->n_compound);
        mpz_add_ui(state->seed, state->seed, DBUS_TYPENUM_COMPOUND_r);
        mpz_add_ui(next->seed, state->seed, _DBUS_TYPENUM_BASIC_N + 2);

        return dbus_typenum_fold(gen);
}

static int dbus_typenum_parser_PAIR(DBusTypenum *gen, char c) {
        DBusTypenumState *next, *state = gen->tip;
        unsigned long val;

        val = dbus_typenum_unmap_basic(c);
        if (val >= _DBUS_TYPENUM_BASIC_N) {
                state->rule = DBUS_TYPENUM_PARSER_FAIL;
                return -EINVAL;
        }

        next = dbus_typenum_pop(gen);
        mpz_set_ui(next->seed, val);
        next = dbus_typenum_push(gen);
        next->rule = DBUS_TYPENUM_PARSER_PAIR_CLOSE;
        next = dbus_typenum_push(gen);
        next->rule = DBUS_TYPENUM_PARSER_TYPE;
        return 0;
}

static int dbus_typenum_parser_PAIR_CLOSE(DBusTypenum *gen, char c) {
        DBusTypenumState *next, *state = gen->tip;

        if (c != '}') {
                state->rule = DBUS_TYPENUM_PARSER_FAIL;
                return -EINVAL;
        }

        next = dbus_typenum_pop(gen);

        /* fold KEY and VALUE */
        mpz_mul_ui(state->seed, state->seed, _DBUS_TYPENUM_BASIC_N);
        mpz_add(next->seed, next->seed, state->seed);

        /* fold decision to use PAIR */
        mpz_mul_ui(next->seed, next->seed, gen->n_compound);
        mpz_add_ui(next->seed, next->seed, DBUS_TYPENUM_COMPOUND_e);
        mpz_add_ui(next->seed, next->seed, _DBUS_TYPENUM_BASIC_N + 2);

        return dbus_typenum_fold(gen);
}

/**
 * dbus_typenum_new() - allocate enumerator context
 * @genp:               output argument for new enumerator context
 * @flags:              flags to control behavior
 *
 * This function allocates a new enumerator. Each allocated enumerator is
 * independent of the other ones, and never touches *any* global state.
 *
 * The enumerator has an initial seed of 0 and can be used directly to start a
 * new sequence. Usually, you should seed it with the requested value, first,
 * and then start a new sequence via dbus_typenum_step().
 *
 * The enumerator uses libgmp (GnuMP) internally. The GnuMP lbrary is not OOM
 * safe, hence, this implementation will abort the application if out of
 * memory.
 *
 * Return: 0 on success, negative error code on failure.
 */
_public_ int dbus_typenum_new(DBusTypenum **genp, unsigned int flags) {
        DBusTypenum *gen;

        if (flags & ~(DBUS_TYPENUM_FLAG_ALLOW_MAYBE))
                return -EINVAL;

        gen = calloc(1, sizeof(*gen));
        if (!gen)
                return -ENOMEM;

        mpz_init(gen->seed);
        mpz_init(gen->root);
        mpz_init(gen->root_squared);
        mpz_init(gen->index);

        if (flags & DBUS_TYPENUM_FLAG_ALLOW_MAYBE)
                gen->n_compound = _DBUS_TYPENUM_COMPOUND_N_MAYBE;
        else
                gen->n_compound = _DBUS_TYPENUM_COMPOUND_N;

        *genp = gen;
        return 0;
}

/**
 * dbus_typenum_free() - destroy enumerator object
 * @gen:                enumerator to destroy, or NULL
 *
 * This destroys the passed enumerator and releases all allocated resources. If
 * NULL is passed, this is a no-op.
 *
 * Return: NULL is returned.
 */
_public_ DBusTypenum *dbus_typenum_free(DBusTypenum *gen) {
        DBusTypenumState *state;

        if (!gen)
                return NULL;

        while ((state = gen->unused)) {
                gen->unused = state->parent;
                dbus_typenum_state_free(state);
        }

        while ((state = gen->tip)) {
                gen->tip = state->parent;
                dbus_typenum_state_free(state);
        }

        mpz_clear(gen->index);
        mpz_clear(gen->root_squared);
        mpz_clear(gen->root);
        mpz_clear(gen->seed);
        free(gen);

        return NULL;
}

/**
 * dbus_typenum_reset() - reset enumerator
 * @gen:                enumerator to reset
 *
 * This resets the current state of the enumerator @gen. It does *not* reset
 * the seed value!
 *
 * The next call to dbus_typenum_step() will start a new sequence with the
 * current seed.
 */
_public_ void dbus_typenum_reset(DBusTypenum *gen) {
        while (gen->tip)
                dbus_typenum_pop(gen);
}

/**
 * dbus_typenum_seed_u32() - seed enumerator
 * @gen:                enumerator to seed
 * @seed:               new seed
 *
 * This seeds the enumerator @gen with @seed. It is similar to
 * dbus_typenum_seed_str(), but takes binary input, rather than string input.
 * But this limits the possible range to the range of an uint32_t.
 */
_public_ void dbus_typenum_seed_u32(DBusTypenum *gen, uint32_t seed) {
        mpz_set_ui(gen->seed, seed);
}

/**
 * dbus_typenum_seed_str() - seed enumerator
 * @gen:                enumerator to seed
 * @str:                string representation of the seed
 * @base:               base of the integer representation
 *
 * This seeds the given enumerator with the integer given in @str. The integer
 * must be given as ASCII string with a representation of base @base. Arbitrary
 * precision is supported.
 *
 * If there is currently a sequence ongoing, this has *no* effect on it. It
 * will only take effect on the *next* sequence you start.
 *
 * If @str is not formatted as an integer in base @base, this function will use
 * its first byte as binary seed. An error code is still returned!
 *
 * Return: 0 on success, negative error code if @str is wrongly formatted.
 */
_public_ int dbus_typenum_seed_str(DBusTypenum *gen, const char *str, int base) {
        int r;

        r = mpz_set_str(gen->seed, str, base);
        if (r < 0) {
                dbus_typenum_seed_u32(gen, *str);
                return -EINVAL;
        }

        return 0;
}

/**
 * dbus_typenum_step() - perform single step
 * @gen:                enumerator to operate on
 *
 * This performs a single generation step on the passed enumerator. If the
 * enumerator is unused (no step has been performed, yet, or it was reset),
 * this will start a new sequence based on the current seed. Otherwise, this
 * continues the previous sequence.
 *
 * Each call to this function returns the next element of a valid D-Bus
 * type. It is guaranteed to return a valid type. Once done, this returns 0.
 * You need to call dbus_typenum_reset() if you want to start a new sequence.
 *
 * If a new sequence is started, the current seed value is *copied*. That is,
 * any modification later on has *NO* effect on the current sequence.
 *
 * Return: Next D-Bus element of the current sequence, 0 if done.
 */
_public_ char dbus_typenum_step(DBusTypenum *gen) {
        DBusTypenumState *state = gen->tip;

        if (!state) {
                state = dbus_typenum_push(gen);
                state->rule = DBUS_TYPENUM_RULE_DONE;
                state = dbus_typenum_push(gen);
                state->rule = DBUS_TYPENUM_RULE_TYPE;
                mpz_set(state->seed, gen->seed);
        }

        switch (state->rule) {
        case DBUS_TYPENUM_RULE_DONE:
                return 0;
        case DBUS_TYPENUM_RULE_TYPE:
                return dbus_typenum_rule_TYPE(gen);
        case DBUS_TYPENUM_RULE_TUPLE:
                return dbus_typenum_rule_TUPLE(gen);
        case DBUS_TYPENUM_RULE_TUPLE_CLOSE:
                return dbus_typenum_rule_TUPLE_CLOSE(gen);
        case DBUS_TYPENUM_RULE_PAIR:
                return dbus_typenum_rule_PAIR(gen);
        case DBUS_TYPENUM_RULE_PAIR_CLOSE:
                return dbus_typenum_rule_PAIR_CLOSE(gen);
        default:
                assert(0);
                return 0;
        }
}

/**
 * dbus_typenum_feed() - feed next character into type parser
 * @gen:                enumerator to operate on
 * @c:                  next character to feed
 *
 * This is the inverse of dbus_typenum_step(). Rather than generating a type
 * from a seed, this parses a type one by one and generates the seed it
 * corresponds to. Simply feed your entire type into a reset enumerator and use
 * dbus_typenum_print() afterwards to access the resulting seed.
 *
 * To make sure your type is fully parsed, you can feed your final binary 0
 * into this just fine. If the type is done, this will succeed, otherwise it
 * will return an error.
 *
 * You better not mix dbus_typenum_feed() and dbus_typenum_step() without
 * resetting the enumerator in between. It will work fine, but the resulting
 * data will be undefined.
 *
 * Return: 0 on success, negative error code on failure.
 */
_public_ int dbus_typenum_feed(DBusTypenum *gen, char c) {
        DBusTypenumState *state = gen->tip;

        if (!state) {
                state = dbus_typenum_push(gen);
                state->rule = DBUS_TYPENUM_PARSER_DONE;
                state = dbus_typenum_push(gen);
                state->rule = DBUS_TYPENUM_PARSER_TYPE;
        }

        switch (state->rule) {
        case DBUS_TYPENUM_PARSER_DONE:
                if (!c)
                        return 0;
                state->rule = DBUS_TYPENUM_PARSER_FAIL;
                /* fallthrough */
        case DBUS_TYPENUM_PARSER_FAIL:
                return -EINVAL;
        case DBUS_TYPENUM_PARSER_TYPE:
                return dbus_typenum_parser_TYPE(gen, c);
        case DBUS_TYPENUM_PARSER_TUPLE:
                return dbus_typenum_parser_TUPLE(gen, c);
        case DBUS_TYPENUM_PARSER_PAIR:
                return dbus_typenum_parser_PAIR(gen, c);
        case DBUS_TYPENUM_PARSER_PAIR_CLOSE:
                return dbus_typenum_parser_PAIR_CLOSE(gen, c);
        default:
                assert(0);
                return 0;
        }
}

/**
 * dbus_typenum_print() - print final seed
 * @gen:                enumerator to query
 * @f:                  file to print to
 * @base:               base to print number in
 *
 * This call prints the final seed after a full sequence was parsed via
 * dbus_typenum_feed(). It prints "<invalid>" if the sequence failed or is not
 * finished, yet.
 */
_public_ void dbus_typenum_print(DBusTypenum *gen, FILE *f, int base) {
        DBusTypenumState *state = gen->tip;

        if (state && state->rule == DBUS_TYPENUM_PARSER_DONE)
                mpz_out_str(f, base, state->seed);
        else
                fprintf(f, "<invalid>");
}
