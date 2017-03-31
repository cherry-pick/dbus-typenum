#pragma once

/*
 * D-Bus Type Enumerator
 */

#ifdef __cplusplus
extern "C" {
#endif

#include <errno.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

typedef struct DBusTypenum DBusTypenum;

enum {
        DBUS_TYPENUM_FLAG_ALLOW_MAYBE                   = 0x0001,
};

int dbus_typenum_new(DBusTypenum **genp, unsigned int flags);
DBusTypenum *dbus_typenum_free(DBusTypenum *gen);

void dbus_typenum_reset(DBusTypenum *gen);

void dbus_typenum_seed_u32(DBusTypenum *gen, uint32_t seed);
int dbus_typenum_seed_str(DBusTypenum *gen, const char *str, int base);

char dbus_typenum_step(DBusTypenum *gen);

int dbus_typenum_feed(DBusTypenum *gen, char c);
void dbus_typenum_print(DBusTypenum *gen, FILE *f, int base);

static inline void dbus_typenum_freep(DBusTypenum **gen) {
        if (*gen)
                dbus_typenum_free(*gen);
}

#ifdef __cplusplus
}
#endif
