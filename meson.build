project('dbus-typenum',
        'c',
        version: '1',
        license: 'Apache',
        default_options: [ 'c_std=c11' ])

add_project_arguments('-D_GNU_SOURCE', language: 'c')
mod_pkgconfig = import('pkgconfig')
compiler_c = meson.get_compiler('c')
libgmp_dep = compiler_c.find_library('libgmp')

subdir('src')
