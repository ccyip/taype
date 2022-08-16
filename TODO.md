- Pretty print
  + short and long versions
  + merge lambda arguments
  + add parentheses
- Preserve user-given names
- Equality check ignoring locations and user names
- Parser error reporting
  + Readable unexpected/expecting list
  + Case pattern variables have the same names
- Parsed ASTs should get rid of local names
- Scrap my boilerplate: instances for Monad, Eq1, etc
- Use smart constructor to avoid providing default fields?
- Simplify and abstract parser, e.g., unify infix, if and case
- Binders may contain location
