module

public import ABG.ChapterII.Section1.FocalGenerators
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Theory.GroupTheory.SpecificGroups.KleinFourAutDifference
public import Theory.GroupTheory.NormalizerActionSurjective

/-!
# Full normalizer fusion generates a four-subgroup

Let `U` be a Klein-four subgroup contained in `P`. If the ambient index
`|N(U):C(U)|` is six, the differences from normalizer fusion generate
exactly `U.subgroupOf P`. This is the high-index four-subgroup local
focal calculation used in Alperin--Brauer--Gorenstein, Chapter II,
Section 1, Proposition 1 (article pp. 10--11). The computation does not
require a quasi-dihedral presentation or a Sylow hypothesis on `P`.

The index-six condition and the six-element automorphism group make the
normalizer action surjective. For any `t` in the Klein-four group, choose
`x` outside `{1,t}`. Swapping `x` and `x*t` fixes the identity and hence
is an automorphism `f`; thus `t = x⁻¹*f(x)`. Lifting `f` to the actual
normalizer puts the image of `t` in the local fusion subgroup. Conversely,
normalizer invariance keeps every defining difference inside `U`.
The automorphism calculation is supplied by the reusable
`IsKleinFour.exists_mulAut_difference`. The proof uses the shared production
definition of normalizer fusion and the actual inclusion of `U` into `P`
throughout.
-/

namespace ABG
open scoped IsKleinFour
variable {G : Type*} [Group G]

/-- A full ambient automorphism action on a four-subgroup makes its local
normalizer fusion differences generate that entire subgroup inside `P`. -/
public theorem four_normalizerFusionSubgroup_eq [Finite G] (P U : Subgroup G)
    (hUP : U ≤ P) (hU : IsKleinFour U) (hindex : automizerIndex U = 6) :
    normalizerFusionSubgroup P U = U.subgroupOf P := by
  let := hU
  have hsurj : Function.Surjective U.normalizerMonoidHom :=
    U.normalizerMonoidHom_surjective_of_index_eq_card (by
      rw [IsKleinFour.card_mulAut U]
      exact hindex)
  apply le_antisymm (normalizerFusionSubgroup_le P U)
  intro z hz
  let t : U := ⟨z, hz⟩
  obtain ⟨x, f, hf⟩ := IsKleinFour.exists_mulAut_difference t
  have h := normalizerFusionSubgroup_mem_of_automorphism P U hUP hsurj f x
  have he : Subgroup.inclusion hUP (x⁻¹ * f x) = z := by
    apply Subtype.ext
    exact congrArg (fun u : U => (u : G)) hf
  rwa [he] at h

end ABG
