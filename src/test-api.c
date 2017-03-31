/*
 * Tests for Public API
 *
 * This tests for symbol visibility only! It does not perform any validity
 * tests. All symbols should be tested here for availablity.
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "dbus-typenum.h"

static void test_api(void) {
        __attribute__((__cleanup__(dbus_typenum_freep))) DBusTypenum *gen = NULL;
        int r;

        r = dbus_typenum_new(&gen, 0);
        assert(r >= 0);

        dbus_typenum_seed_u32(gen, 0);
        dbus_typenum_seed_str(gen, "0", 10);
        dbus_typenum_step(gen);

        dbus_typenum_reset(gen);

        dbus_typenum_feed(gen, 'y');
        dbus_typenum_print(gen, stdout, 10);

        gen = dbus_typenum_free(gen);
}

int main(int argc, char **argv) {
        test_api();
        return 0;
}
