# pilot: C EDSL inspired by copilot

A proper README is coming. For now, here's a jumping-off point:

```sh
cabal new-repl
# Load examples and the C generation module
> :m +Examples
> :m +Pilot.Interp.C
# Generates the C for example_17 and writes it to example.c
# Always use False for the boolean parameter. Setting to True enables
# compound type sharing but it probably doesn't work right at the moment.
> write_stream_expr "example.c" False example_17
```
