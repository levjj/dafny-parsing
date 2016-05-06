# dafny-parsing

**Parser combinator library for Dafny**

The API is currently based on algebraic datatypes and functions. 
It would be possible to offer a class/method-based API. However, Dafny
currently requires a statement based appraoch for imperative code and
does not allow allocation of (immutable) objects with expressions.

## Example

```dafny
include "Parsing.dfy"

module Example {
  import opened Parsing

  method Main() {
    print(Parse(DigitP(), "5")); // Some('5')
    print(Parse(DigitP(), "X")); // None
  }
}
```
