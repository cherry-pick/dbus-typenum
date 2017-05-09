#
# target: libdbus-typenum.so
#

libdbus_typenum_symfile = join_paths(meson.current_source_dir(), 'libdbus-typenum.sym')

libdbus_typenum_private = static_library(
        'dbus-typenum-private',
        [
                'enumerator.c',
        ],
        c_args: [
                '-fvisibility=hidden',
                '-fno-common',
        ],
        dependencies: libgmp_dep,
        pic: true,
)

libdbus_typenum_shared = shared_library(
        'dbus-typenum',
        objects: libdbus_typenum_private.extract_all_objects(),
        install: not meson.is_subproject(),
        soversion: 0,
        link_depends: libdbus_typenum_symfile,
        dependencies: libgmp_dep,
        link_args: [
                '-Wl,--no-undefined',
                '-Wl,--version-script=@0@'.format(libdbus_typenum_symfile),
        ],
)

libdbus_typenum_dep = declare_dependency(
        include_directories: include_directories('.'),
        link_with: libdbus_typenum_private,
        dependencies: libgmp_dep,
        version: meson.project_version(),
)

if not meson.is_subproject()
        install_headers('dbus-typenum.h')

        mod_pkgconfig.generate(
                libraries: libdbus_typenum_shared,
                version: meson.project_version(),
                name: 'libdbus-typenum',
                filebase: 'libdbus-typenum',
                description: 'D-Bus Type Enumerator',
        )
endif

#
# target: dbus-typenum
#

dbus_typenum_exe = executable(
        'dbus-typenum',
        [
                'main.c',
        ],
        install: not meson.is_subproject(),
        link_with: libdbus_typenum_shared,
)

#
# target: test-*
#

test_api = executable('test-api', ['test-api.c'], link_with: libdbus_typenum_shared)
test('API Symbol Visibility', test_api)

test_basic = executable('test-basic', ['test-basic.c'], dependencies: libdbus_typenum_dep)
test('Basic API Behavior', test_basic)
