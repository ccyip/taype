- `AppKind` can be deprecated?
- Consider checking labels in type equivalence
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

- Performance
  + `test_healthy_rate`
    * express boolean operators, including retraction, using MUX is a bad idea.
    * perform section earlier (for every iteration) can reduce the exponential
      MUX to linear.
  + `test_min_euclidean_distance`
    * Going from 5 to 6 is like day and night.
