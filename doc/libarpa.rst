Libstd libstream API
--------------------

Caution
"""""""

The libstd's libARPA implementation is **not** a network stack implementation but an implementation of the minimalist network bytes order encoding/decoding API.
These functions are requested for various usage, including a network stack, but also various other protocols such as USB, SCSI and cryptographic stacks.

.. include:: functions/htonl.rst
   :start-line: 4

