EwoK Standard library
=====================

[![Release](https://img.shields.io/github/release/wookey-project/libstd.svg)](https://github.com/wookey-project/libstd/releases/latest)
[![Build Status](https://dev.azure.com/phil0093/phil/_apis/build/status/wookey-project.manifest?branchName=master)](https://dev.azure.com/phil0093/phil/_build/latest?definitionId=1&branchName=master)

Introduction
------------

EwoK standard library is the EwoK microkernel userspace small libc implementation, hosting:

   * The userspace syscall part
   * The various embedded-specific utility functions (such as registers manipulation helpers)
   * Some various basic functions for string manipulation, etc.



libstd API
----------

The libstd API is decomposed in various and small foot-print specific components.

   * libstream: the I/O pretty printing API, such as printf API
   * libstring: string manipulation API
   * libarpa: endianess manipulation for protocol stacks
   * libembed: various embedded-related API, including data storage API and various others
   * liballoc: the memory allocator

libstd **does not aim** to be a POSIX compliant library. Nevertheless, for functions that behave
like POSIX ones, libstd try to keep the POSIX conformant API.

Each component is fully described in the libstd documentation (see doc/ dir or run make doc).

Building libstd
---------------

Libstd is to be build in the tataouine build environment as a userspace library (in the libs/ directory of tataouine).
See the tataouine documentation of the Wookey project for more information.
