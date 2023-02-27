- `AppKind` can be deprecated?
- Add program context for better inference
- Error messages for `isProd` / `isOProd` / `isPi` could be confusing in
  introduction form
- Error message for dependent expressions are confusing
- Allow explicit label annotation
- Syntax highlight for VSCode and Emacs
- Add floating points
- More descriptive field names for syntax?
- Support tuple patterns in dependent case?
- Unordered oblivious case?
- Support nondeterministic oblivious value (of any oblivious type)?
  + May need to support bottom in the public computation, as a correspondence
- Option for name sanitization
- Option to runner to only run the first few test cases
- Parser for Oil
- `unsafe!if` -> `if` and `unsafe!r_bool`
- Remove unnecessary dead code elimination?
- Need to rename section / retraction functions before tupling?
- More partial evaluation on numbers and booleans?

- Known bug: early-tape optimization can cause non-termination in some cases.
  This can be fixed by keeping the public values (until we can't) in the
  oblivious array backends.
