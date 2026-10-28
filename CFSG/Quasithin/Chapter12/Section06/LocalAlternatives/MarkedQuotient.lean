module

public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.Data.ZMod.Basic

/-!
# The marked conclusion of 12.6.31(3)

The quotient is the original `H/O₂(H)`. The local intersection is `M ∩ H`,
regarded as a subgroup of H, and every starred subgroup uses the same
quotient homomorphism. The conclusion records the index five, the equality
of the image of R₁ with the embedded two-core of M_H*, and an actual
four-group isomorphism in addition to the S₅ × S₃ isomorphism.

This is a conclusion type, not an assertion of existence or a proof of
12.6.31--33. Those proofs must construct its fields from the section setup.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
Lemma 12.6.31(3), printed p.835, and Lemma 12.6.33, printed pp.837--838.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter12.Section06.LocalAlternatives
variable {G : Type*} [Group G]

/-- The actual local quotient, with no change of carrier or kernel. -/
abbrev Star (H : Subgroup G) := H ⧸ pCore 2 H

/-- The original quotient homomorphism. -/
def starMap (H : Subgroup G) : H →* Star H := QuotientGroup.mk' (pCore 2 H)

/-- The image of an ambient subgroup, intersected with H before quotienting. -/
def starImage (H A : Subgroup G) : Subgroup (Star H) :=
  (A.subgroupOf H).map (starMap H)

/-- The four-group as an actual group carrier. -/
abbrev FourGroup := Multiplicative (Fin 2 → ZMod 2)

/-- All three clauses in 12.6.31(3), retained when the other cases have been
excluded. `M.subgroupOf H` is precisely the literal intersection M ∩ H. -/
structure SymmetricProductConclusion (M H R₁ : Subgroup G) : Prop where
  quotient : Nonempty (Star H ≃* (Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3)))
  index : (M.subgroupOf H).index = 5
  image_eq_core : starImage H R₁ = (starImage H M).pCoreIn 2
  image_four : Nonempty (starImage H R₁ ≃* FourGroup)

end CFSG.Quasithin.Chapter12.Section06.LocalAlternatives
