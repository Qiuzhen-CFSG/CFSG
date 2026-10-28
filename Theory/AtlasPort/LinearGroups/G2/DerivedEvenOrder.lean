module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup
public import Theory.AtlasPort.LinearGroups.G2.BinaryException

/-!
# The even-order derived G₂ carrier

Coefficient transport restricts to the actual commutator subgroup. The binary
carrier has order 6048, using the checked sign-character calculation. For a
field of order 2^f with f > 1, torus commutators prove perfectness, giving an
explicit equivalence from the derived carrier to the full octonion model.
Thus every positive binary exponent gives an even-order derived carrier.

These facts preserve the derived-group convention in Aschbacher--Smith,
E.1.14(1), printed p.214. The model, binary sign character and perfectness
proofs are reused from the licensed ATLAS port; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. No additional upstream source is copied here.
-/

@[expose] public section

open Subgroup Atlas.G2
namespace Atlas.G2.DerivedEvenOrder
variable {F K : Type*} [Field F] [Field K]

def derivedFieldEquiv (e : F ≃+* K) : commutator (Model F) ≃* commutator (Model K) :=
  ((fieldEquiv e).subgroupMap _).trans (MulEquiv.subgroupCongr (by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (fieldEquiv e).surjective]
    rfl))

theorem commutator_eq_top_of_card [Finite F] {f : ℕ} (hf : 1 < f)
    (hF : Nat.card F = 2 ^ f) : commutator (Model F) = ⊤ := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect (by
    rw [hF]
    exact (by simpa using (Nat.pow_lt_pow_right (by decide : 1 < 2) hf)))
  exact Group.IsPerfect.commutator_eq_top

noncomputable def derivedEquivModel [Finite F] {f : ℕ} (hf : 1 < f)
    (hF : Nat.card F = 2 ^ f) : commutator (Model F) ≃* Model F :=
  (MulEquiv.subgroupCongr (commutator_eq_top_of_card hf hF)).trans topEquiv

theorem card_derived_binary [Finite F] (hF : Nat.card F = 2) :
    Nat.card (commutator (Model F)) = 6048 := by
  rw [Nat.card_congr (derivedFieldEquiv (binaryFieldEquiv hF)).toEquiv,
    BinaryParabolicPair.commutator_eq_longRootClosure]
  exact BinaryException.card_H

theorem even_card_derived [Finite F] {f : ℕ} (hf : 0 < f)
    (hF : Nat.card F = 2 ^ f) : Even (Nat.card (commutator (Model F))) := by
  by_cases h1 : f = 1
  · have htwo : Nat.card F = 2 := by simpa [h1] using hF
    rw [card_derived_binary htwo]
    decide
  · rw [Nat.card_congr (derivedEquivModel (by omega) hF).toEquiv, card_Model]
    have hq : Even (Nat.card F) := by
      rw [hF]
      exact Nat.even_pow.mpr ⟨by decide, by omega⟩
    exact ((Nat.even_pow.mpr ⟨hq, by decide⟩).mul_right _).mul_right _

end Atlas.G2.DerivedEvenOrder
