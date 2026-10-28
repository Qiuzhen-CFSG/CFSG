module

public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.QuaternionPlacement.GraphField.MarkedAction
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.QuaternionPlacement.GraphField.GraphCharacter

/-!
# The marked matrix map of the full graph-field centralizer

The action on E₉ kills graph-field itself. A character to C₂ nontrivial on
this marked involution removes that obstruction: every character kills the
inner E₉, and the computed pointwise fixer then gives a three-group kernel
for the product map. The quaternion matrix fibers already lie in the actual
inner image joined with graph-field, independently of the character.

The graph-factor character constructed in `GraphCharacter` separates the
marked involution. Pairing it with the ternary action gives `matrixMap`,
with an unconditional three-group kernel and quaternion-fiber containment.
These are the inputs required by `graphField_placement_of_matrix_model`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.1.4(5),
printed p.1171, and the quaternion placement in 16.4.9(2), printed p.1192.
-/

@[expose] public section

namespace Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement.GraphField
open Subgroup ExtendedCentralizer ProjectiveFixer
noncomputable section

/-- A binary character kills the actual inner E₉, by coprime orders. -/
theorem character_modelConj (χ : automorphismCentralizer graphField →* C2) (y : model) :
    χ (modelConj y) = 1 := by
  apply orderOf_eq_one_iff.mp
  apply Nat.eq_one_of_dvd_coprimes (show Nat.Coprime 9 2 from by decide)
  · have h : (χ (modelConj y)) ^ 9 = 1 := by
      rw [← map_pow, ← map_pow]
      have hy : y ^ 9 = 1 := by simpa only [model_card] using (pow_card_eq_one' : y ^ Nat.card model = 1)
      rw [hy, map_one, map_one]
    exact orderOf_dvd_of_pow_eq_one h
  · simpa only [card_C2] using orderOf_dvd_natCard (χ (modelConj y))

/-- The desired product homomorphism, with its binary character still supplied. -/
def matrixMapWithCharacter (χ : automorphismCentralizer graphField →* C2) :
    automorphismCentralizer graphField →* GeneralLinearGroup (Fin 2) (ZMod 3) × C2 :=
  matrixAction.prod χ

/-- Separating the marked involution suffices for the three-group kernel. -/
theorem matrixMapWithCharacter_ker_isThreeGroup
    (χ : automorphismCentralizer graphField →* C2) (hχ : χ markedInvolution ≠ 1) :
    IsPGroup 3 (matrixMapWithCharacter χ).ker := by
  intro x
  have hm : matrixAction x.val = 1 := congrArg Prod.fst x.property
  have hc : χ x.val = 1 := congrArg Prod.snd x.property
  obtain ⟨⟨y,t⟩, ht⟩ := (matrixAction_eq_one_iff x.val).mp hm
  have hx : x.val = modelConj y * markedInvolution ^ t.toAdd.val := Subtype.ext ht.symm
  rw [hx, map_mul, map_pow, character_modelConj, one_mul] at hc
  have ht0 : t.toAdd.val = 0 := by
    have hb := ZMod.val_lt t.toAdd
    have hh : t.toAdd.val = 0 ∨ t.toAdd.val = 1 := by omega
    rcases hh with h | h
    · exact h
    · rw [h, pow_one] at hc
      exact (hχ hc).elim
  refine ⟨2, ?_⟩
  apply Subtype.ext
  change x.val ^ 9 = 1
  rw [hx, ht0, pow_zero, mul_one, ← map_pow]
  have hy : y ^ 9 = 1 := by simpa only [model_card] using (pow_card_eq_one' : y ^ Nat.card model = 1)
  rw [hy, map_one]

/-- The matrix-fiber conclusion holds for every choice of the binary character. -/
theorem matrixMapWithCharacter_fibers_inner
    (χ : automorphismCentralizer graphField →* C2) (x : automorphismCentralizer graphField)
    (hx : ((matrixMapWithCharacter χ x).1).val = 1 ∨
      ((matrixMapWithCharacter χ x).1).val = -1 ∨
      ((matrixMapWithCharacter χ x).1).val ^ 2 = -1) : x.val ∈ innerWith graphField :=
  quaternion_fibers_inner x hx

/-- The actual ternary action paired with the graph-factor character. -/
def matrixMap :
    automorphismCentralizer graphField →* GeneralLinearGroup (Fin 2) (ZMod 3) × C2 :=
  matrixMapWithCharacter binaryCharacter

/-- The kernel of the marked matrix map is a three-group. -/
theorem matrixMap_ker_isThreeGroup : IsPGroup 3 matrixMap.ker :=
  matrixMapWithCharacter_ker_isThreeGroup binaryCharacter
    binaryCharacter_markedInvolution_ne_one

/-- The eight quaternion matrix fibers lie in the actual inner image joined with graph-field. -/
theorem matrixMap_fibers_inner (x : automorphismCentralizer graphField)
    (hx : (matrixMap x).1.val = 1 ∨ (matrixMap x).1.val = -1 ∨
      (matrixMap x).1.val ^ 2 = -1) : (x : MulAut PSL) ∈ innerWith graphField :=
  matrixMapWithCharacter_fibers_inner binaryCharacter x hx

end
end Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement.GraphField
