module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.BorelComparison.Inputs
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.BorelComparison.Irreducible
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.BorelComparison.RootIntertwiner
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.BorelComparison.TorusIntertwiner

/-!
# Assembly of the degree-twenty Borel comparison from nonzero intertwiners

Both literal Borel restrictions are irreducible by the extraspecial
minimum-degree argument, without assuming irreducibility of either original
representation. A nonzero root intertwiner and the torus fixed-vector
calculation then supply a nonzero Borel map. Schur's lemma makes that map an
actual equivalence over the original coefficient field.

The conditional assembly is retained, and `twenty_borel_comparison` discharges
both inputs using the proved root and torus calculations. It constructs the
equivalence over the original field with exactly the hypotheses of
`TwentyBorelComparison`.

Source motivation: Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 4.3, pp.10–11, and Aschbacher–Smith K.2, printed p.453.
-/

public section

namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
open BorelComparison Degrees
universe v

/-- Root-intertwiner existence and the torus fixed-vector calculation give
the actual Borel equivalence over the original coefficient field. -/
theorem twenty_borel_comparison_of_intertwiner_inputs
    (hroot : TwentyRootIntertwining.{v}) (htorus : BorelIntertwinerLifting.{v}) :
    TwentyBorelComparison.{v} := by
  intro F _ _ J hc hconj K _ _ _ U W _ _ _ _ _ _ ρ σ hρdim hσdim hρcenter hσcenter hρfix hσfix
  let : IsIrreducible (ρ.comp (standardBorel J).subtype) :=
    borel_restriction_isIrreducible J hc hconj ρ hρdim hρfix
  let : IsIrreducible (σ.comp (standardBorel J).subtype) :=
    borel_restriction_isIrreducible J hc hconj σ hσdim hσfix
  obtain ⟨f, hf⟩ := htorus F J hc hconj K U W ρ σ hρcenter hσcenter
    (hroot F J hc hconj K U W ρ σ hρdim hσdim hρfix hσfix)
  exact ⟨f.ofBijective ((IsIrreducible.bijective_or_eq_zero f).resolve_right hf)⟩

/-- The root-center-free degree-twenty modules killing the SU center have
equivalent restrictions to the literal Borel over their original field. -/
theorem twenty_borel_comparison : TwentyBorelComparison.{v} :=
  twenty_borel_comparison_of_intertwiner_inputs
    twenty_root_intertwining borel_intertwiner_lifting

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
