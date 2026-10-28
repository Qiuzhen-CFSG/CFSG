module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E8.Operators.RootStrings
public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E8.Operators.CoordinateStrings

/-!
# The six positive integral E8 operators

The native Geck matrices are identified with computable integer matrices in
the proved 78-element basis. The squared-length argument gives coefficient
one for every root sum. Integer coordinate certificates show that a double
step only carries the negative simple root to its positive root, and that
there is no triple step. Thus the only quadratic entry is the rank-one one.
Source: the integral Geck construction, used in GLS3 §2.6.
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace Theory.SpecificGroups.LieType.SourceLevi.E8.Operators
open Coordinates
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

def positiveLinear (i : Fin 6) : Matrix (Fin 248) (Fin 248) ℤ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv <| Matrix.fromBlocks 0
    (fun r c => if r = node i ∧ c = negative i then 1 else 0)
    (fun r c => if r = simple i then |typeE8CartanMatrix (node i) c| else 0)
    (fun r c => if coord r = coord (simple i) + coord c then 1 else 0)

def positiveQuadratic (i : Fin 6) : Matrix (Fin 248) (Fin 248) ℤ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv <| Matrix.fromBlocks 0 0 0
    (fun r c => if r = simple i ∧ c = negative i then 1 else 0)

noncomputable section
open scoped Classical
local instance : InvolutiveNeg typeE8Roots := typeE8RootPairing.indexNeg
local instance : Fintype typeE8Roots := Fintype.ofFinite _

private theorem enum_apply (r : Fin 240) : rootEquiv r = root r := rfl

private theorem basis_at (r : Fin 8 ⊕ Fin 240) :
    basisEquiv (finSumFinEquiv r) =
      Equiv.sumCongr typeE8RootPairing_baseEquiv rootEquiv r := by
  simp [basisEquiv]

private theorem root_add_iff (r s t : Fin 240) :
    typeE8RootPairing.root (root r) =
      typeE8RootPairing.root (root s) + typeE8RootPairing.root (root t) ↔
      coord r = coord s + coord t := by
  simpa only [one_smul] using root_eq_add_nsmul_iff r s t 1

theorem positiveLinear_eq (i : Fin 6) :
    reindex (eMatrix (typeE8RootPairing_baseEquiv (node i))) = positiveLinear i := by
  ext r c
  obtain ⟨r, rfl⟩ := (finSumFinEquiv (m := 8) (n := 240)).surjective r
  obtain ⟨c, rfl⟩ := (finSumFinEquiv (m := 8) (n := 240)).surjective c
  rw [reindex_apply, basis_at, basis_at]
  simp only [positiveLinear, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases r with r | r <;> rcases c with c | c <;>
    simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, enum_apply]
  · rfl
  · change (if typeE8RootPairing_baseEquiv r = typeE8RootPairing_baseEquiv (node i) ∧
        root c = -(typeE8RootPairing_baseEquiv (node i) : typeE8Roots) then (1 : ℤ) else 0) = _
    rw [← root_negative]
    simp only [Equiv.apply_eq_iff_eq, root_injective.eq_iff, Matrix.fromBlocks_apply₁₂]
  · change (if root r = (typeE8RootPairing_baseEquiv (node i) : typeE8Roots) then
        |typeE8RootPairing_base.cartanMatrix (typeE8RootPairing_baseEquiv (node i))
          (typeE8RootPairing_baseEquiv c)| else 0) = _
    rw [← root_simple, typeE8RootPairing_base_cartan_apply]
    simp only [root_injective.eq_iff, Matrix.fromBlocks_apply₂₁]
  · simp only [eMatrix, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
    rw [← root_simple]
    by_cases h : typeE8RootPairing.root (root r) =
        typeE8RootPairing.root (root (simple i)) + typeE8RootPairing.root (root c)
    · rw [if_pos h, chainBotCoeff_of_sum h]
      simp only [Nat.cast_zero, zero_add,
        if_pos ((root_add_iff r (simple i) c).mp h)]
    · simp only [if_neg h,
        if_neg (fun hc => h ((root_add_iff r (simple i) c).mpr hc))]

private theorem bot_negative (i : typeE8RootPairing_base.support) :
    typeE8RootPairing.chainBotCoeff i (-i) = 0 := by
  apply typeE8RootPairing.chainBotCoeff_of_not_linearIndependent
  rw [RootPairing.indexNeg_neg, typeE8RootPairing.root_reflectionPerm,
    typeE8RootPairing.reflection_apply_self, LinearIndependent.pair_neg_right_iff]
  simp_rw [LinearIndependent.pair_iff, not_forall]
  exact ⟨1, -1, by simp, by simp⟩

theorem positiveQuadratic_eq (i : Fin 6) :
    reindex (eDividedPower (typeE8RootPairing_baseEquiv (node i)) 2) = positiveQuadratic i := by
  ext r c
  obtain ⟨r, rfl⟩ := (finSumFinEquiv (m := 8) (n := 240)).surjective r
  obtain ⟨c, rfl⟩ := (finSumFinEquiv (m := 8) (n := 240)).surjective c
  rw [reindex_apply, basis_at, basis_at]
  simp only [positiveQuadratic, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases r with r | r <;> rcases c with c | c <;>
    simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, enum_apply]
  · rfl
  · rfl
  · rfl
  · simp only [eDividedPower, Matrix.of_apply, Matrix.fromBlocks_apply₂₂]
    rw [← root_simple]
    simp only [Nat.zero_add, root_eq_add_nsmul_iff, twice_coordinates]
    by_cases h : r = simple i ∧ c = negative i
    · obtain ⟨rfl, rfl⟩ := h
      simp only [and_self, if_true, root_simple, root_negative, bot_negative,
        zero_add, Nat.choose_self, Nat.cast_one]
    · simp only [if_neg h]

theorem positiveCubic_eq_zero (i : Fin 6) :
    reindex (eDividedPower (typeE8RootPairing_baseEquiv (node i)) 3) = 0 := by
  ext r c
  obtain ⟨r, rfl⟩ := (finSumFinEquiv (m := 8) (n := 240)).surjective r
  obtain ⟨c, rfl⟩ := (finSumFinEquiv (m := 8) (n := 240)).surjective c
  rw [reindex_apply, basis_at, basis_at]
  rcases r with r | r <;> rcases c with c | c <;>
    simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, enum_apply]
  · rfl
  · rfl
  · rfl
  · simp only [eDividedPower, Matrix.of_apply, Matrix.zero_apply]
    rw [← root_simple]
    simp only [root_eq_add_nsmul_iff, if_neg (thrice_coordinates i r c)]

end
end Theory.SpecificGroups.LieType.SourceLevi.E8.Operators
