module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.TripleSixDegree.Reduction
public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion
public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration

/-!
# Excluding binary degree twelve for the actual triple-A₆ cover

The central cubic recovers F₄ scalars on the original faithful irreducible
binary representation of the actual even hexacode carrier. The resulting
irreducible module is a quotient of the central eigenspace in a Sylow coset
module. Its certified filtration has only three- and nine-dimensional simple
factors over F₄, excluding field dimension six and hence binary dimension
twelve. This argument includes nonabsolute irreducibility and discharges the
`NoTwelve` premise of the triple-A₆ degree reduction.

Source application: Aschbacher–Smith K.1.3, printed p.453 (PDF p.464),
citing GM02 Theorem 6.2 and Table 6.3.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.Alternating.TripleSixReduction
universe v

/-- Consumer adapter for the precise intrinsic component representation contract. -/
theorem noTwelve_of_cosetFiltration
    (h : Representation.Hexacode.TwelveDimensional.CosetFiltration) : NoTwelve.{v} := by
  intro V _ _ _ τ hf hi
  let := hi
  exact Representation.Hexacode.TwelveDimensional.finrank_ne_twelve_of_cosetFiltration h τ hf

/-- A faithful irreducible binary representation of the even hexacode cover
cannot have dimension twelve. The concrete coset certificate is discharged. -/
theorem noTwelve : NoTwelve.{v} :=
  noTwelve_of_cosetFiltration Representation.Hexacode.TwelveDimensional.cosetFiltration

end CFSG.Quasithin.ChapterK.Alternating.TripleSixReduction
