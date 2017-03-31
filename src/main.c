/*
 * D-Bus Type Enumerator
 */

#include <errno.h>
#include <getopt.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "dbus-typenum.h"

#define _cleanup_(_x) __attribute__((__cleanup__(_x)))

static int fold(const char *arg) {
        _cleanup_(dbus_typenum_freep) DBusTypenum *e = NULL;
        int r;

        r = dbus_typenum_new(&e, 0);
        if (r < 0)
                return r;

        do {
                dbus_typenum_feed(e, *arg);
        } while (*arg++);

        dbus_typenum_print(e, stdout, 10);
        printf("\n");

        return 0;
}

static int unfold(const char *arg) {
        _cleanup_(dbus_typenum_freep) DBusTypenum *e = NULL;
        char c;
        int r;

        r = dbus_typenum_new(&e, 0);
        if (r < 0)
                return r;

        dbus_typenum_seed_str(e, arg, 10);

        while ((c = dbus_typenum_step(e)))
                printf("%c", c);
        printf("\n");

        return 0;
}

static void help(void) {
        printf("%s [GLOBALS...] COMMAND [LOCALS...] ...\n\n"
               "Enumerator or parse D-Bus types.\n\n"
               "  -h --help             Show this help\n"
               "     --version          Show package version\n"
               "\nCommands:\n"
               "  help                  Show this help\n"
               "  unfold                Map integer to type\n"
               "  fold                  Map type to integer\n"
               , program_invocation_short_name);
}

static int parse_argv(int argc, char *argv[]) {
        enum {
                ARG_VERSION = 0x100,
        };
        static const struct option options[] = {
                { "help",       no_argument,    NULL,   'h'             },
                { "version",    no_argument,    NULL,   ARG_VERSION     },
                {}
        };
        int c;

        while ((c = getopt_long(argc, argv, "h", options, NULL)) >= 0) {
                switch (c) {
                case 'h':
                        help();
                        return 0;

                case ARG_VERSION:
                        /* XXX: generate version from meson source */
                        puts("dbus-typenum 1");
                        return 0;

                case '?':
                        return -EINVAL;
                }
        }

        return 1;
}

int main(int argc, char **argv) {
        int r, left;

        r = parse_argv(argc, argv);
        if (r <= 0)
                goto exit;

        left = argc - optind;
        if (left <= 0) {
                help();
        } else if (!strcmp(argv[optind], "help")) {
                help();
        } else if (!strcmp(argv[optind], "fold")) {
                if (left == 2) {
                        r = fold(argv[optind + 1]);
                        if (r < 0)
                                fprintf(stderr, "Fold operation failed: %d\n", r);
                } else {
                        fprintf(stderr, "Invalid number of arguments.\n");
                        r = -EINVAL;
                }
        } else if (!strcmp(argv[optind], "unfold")) {
                if (left == 2) {
                        r = unfold(argv[optind + 1]);
                        if (r < 0)
                                fprintf(stderr, "Unfold operation failed: %d\n", r);
                } else {
                        fprintf(stderr, "Invalid number of arguments.\n");
                        r = -EINVAL;
                }
        } else {
                fprintf(stderr, "Unknown operation '%s'.\n", argv[optind]);
                r = -EINVAL;
        }

        r = 0;

exit:
        return r < 0 ? EXIT_FAILURE : EXIT_SUCCESS;
}
