module

public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Translations
public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Inner
public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Conjugation

/-!
# Native M22 quintet cores and their conjugation modules

The source sextet translations restrict to the intrinsic inner and outer
quintet cores, of orders 16 and 32. The literal action on the five remaining
parts has kernel O₂(Q) and identifies Q/O₂(Q) with S5, with an equation on
quotient representatives. The inner intersection is the natural F4 plane for
the actual L2(4) subgroup, and the outer core is a five-dimensional
indecomposable for this S5 quotient.

The hexacode intertwiners preserve the native group elements. Their transport
discharges the downstream inner irreducibility and outer indecomposability
premises, using the unconditional `innerInputs` from relative normalization,
index two and the native involution calculation. The quotient also supplies
the group premises of `NaturalQuotient.top_isIrreducible`. Thus this endpoint
establishes the group and conjugation-module branch of H.14.3(2).

Source: Aschbacher--Smith H.14.3, printed p.397, setup on p.396.
-/
