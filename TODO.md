- Unordered oblivious case (only need to change parser)
- Uniplate inspired transform and universe
- Case pattern variables should not allow duplicates
- Scrap my boilerplate: instances for Monad, Eq1, etc
- Support tuple pattern in product case and oblivious sum case
- Consider using default language extensions in cabal file
- Consider define Fresh as a newtype
- Consider define contexts as a newtype
- Consider adding tests
- Separate global context into types and definitions, and maintain the right
  order when kinding or typing
- Add program context for better inference
- Error messages for `isProd` / `isOProd` / `isPi` could be confusing in
  introduction form
