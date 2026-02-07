# Capabilities

Access to system resources is controlled via Capabilities (tokens witness permission).
- `IO` grants world capability.
- `ST` grants state token.

This linear resource tracking ensures single-threaded or synchronized access where required.
