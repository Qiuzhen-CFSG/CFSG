module
unsafe def bad (P : Prop) : P := unsafeCast True.intro
 theorem foo (P : Prop) : P := unsafeCast True.intro
