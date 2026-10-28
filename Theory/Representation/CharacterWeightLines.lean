module

public import Theory.Representation.AbelianAllWeights
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Saturated character-weight decompositions

When the number of occurring characters equals the dimension, independence and
spanning imply that each weight space is a line: their positive dimensions sum
to the ambient dimension. This is the dimension step in Aschbacher–Smith,
Lemma A.3.21(c), printed pp. 55–56.
-/

public section

namespace Representation
variable {E K V : Type*} [Field E] [Group K]
  [AddCommGroup V] [Module E V] [IsMulCommutative K]
  [FiniteDimensional E V] [IsAlgClosed E]

/-- A full number of distinct weights forces every weight space to be a line. -/
theorem characterWeight_finrank_one_of_card_eq_finrank
    (sigma : Representation E K V) (horder : (Nat.card K : E) ≠ 0)
    (hcard : Nat.card sigma.CharacterWeight = Module.finrank E V)
    (chi : sigma.CharacterWeight) :
    Module.finrank E (sigma.characterWeightSpace chi.val) = 1 := by
  classical
  let := (sigma.characterWeight_card_le horder).1
  let := Fintype.ofFinite sigma.CharacterWeight
  let W : sigma.CharacterWeight → Submodule E V :=
    fun chi => sigma.characterWeightSpace chi.val
  have hind : iSupIndep W :=
    (sigma.characterWeightSpace_independent horder).comp Subtype.val_injective
  have hi : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind
      (sigma.iSup_characterWeightSpace_eq_top horder)
  have hsum : ∑ i, Module.finrank E (W i) = Module.finrank E V := by
    rw [← Module.finrank_directSum]
    exact (LinearEquiv.ofBijective (DirectSum.coeLinearMap W) hi).finrank_eq
  have hone (i : sigma.CharacterWeight) : 1 ≤ Module.finrank E (W i) :=
    Submodule.one_le_finrank_iff.mpr i.property
  have heq : (∑ _i : sigma.CharacterWeight, 1) = ∑ i, Module.finrank E (W i) := by
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      ← Nat.card_eq_fintype_card, hsum] using hcard
  exact ((Finset.sum_eq_sum_iff_of_le (fun i _ => hone i)).mp heq chi
    (Finset.mem_univ chi)).symm
end Representation
