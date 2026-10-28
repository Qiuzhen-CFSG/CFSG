module
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.Descent
public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer.RankOne.Comparison
public import Theory.AlgebraicGroup.RootSystems.SimpleGeckGroup.Commutation
public import Theory.AlgebraicGroup.RootSystems.TypeD4Irreducible

/-!
# Pinned triality rank-one maps in arbitrary characteristic

Transvection induction restricts the integral matrix action to the actual split
Geck group. Orthogonality of the three arm roots gives their commutation.
Neither argument uses perfectness of SL₂, so the construction includes SL₂(3).

Source: GLS3 §§2.4, 2.6, particularly Proposition 2.6.2
(`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
open Matrix
open scoped MatrixGroups
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.SimpleGeckGroup
namespace Triality.Standard.OddFundamentalCentralizer.RankOne
open Parabolics

/-- Faithful maps pinned to the genuine positive and negative Geck curves. -/
def pinnedRankOneMaps (P : Parameters) : PinnedRankOneMaps P := by
  have hmem (i : Fin 4) (A : SL(2, ExtensionField P)) :
      ambientHom i A ∈ subgroup (typeDRootPairing_base 2) (ExtensionField P) := by
    apply sl2_root_induction (fun A => ambientHom i A ∈
      subgroup (typeDRootPairing_base 2) (ExtensionField P)) ?_ ?_ ?_ A
    · intro t
      rw [ambientHom_positive]
      exact positiveUnit_mem _ _
    · intro t
      rw [ambientHom_negative]
      exact negativeUnit_mem _ _
    · intro A B hA hB
      simpa only [map_mul] using Subgroup.mul_mem _ hA hB
  let f (i : Fin 4) : SL(2, ExtensionField P) →* SplitGroup P :=
    (ambientHom i).codRestrict _ (hmem i)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro i A B h
    exact ambientHom_injective i (congrArg Subtype.val h)
  · intro i t
    exact Subtype.ext (ambientHom_positive i t)
  · intro i t
    exact Subtype.ext (ambientHom_negative i t)

@[simp] theorem pinnedRankOneMaps_hom_val (P : Parameters) (i : Fin 4)
    (A : SL(2, ExtensionField P)) : ((pinnedRankOneMaps P).hom i A).val =
      ambientHom i A := rfl

private theorem arm_cartan_zero (i j : Fin 4)
    (hi : i ≠ 1) (hj : j ≠ 1) (hij : i ≠ j) :
    (typeDRootPairing_base 2).cartanMatrix
      (typeDRootPairing_baseEquiv 2 j) (typeDRootPairing_baseEquiv 2 i) = 0 := by
  rw [typeDRootPairing_base_cartanMatrix]
  fin_cases i <;> fin_cases j <;> first | contradiction | decide

/-- Orthogonal arm curves commute, without a characteristic restriction. -/
theorem armRootCommutation (P : Parameters) : ArmRootCommutation P := by
  let := typeD4RootPairing_isIrreducible
  refine ⟨?_, ?_, ?_⟩
  · intro i j hi hj hij t u
    exact commute_positive_positive_of_cartan_eq_zero
      _ _ (fun h => hij ((typeDRootPairing_baseEquiv 2).injective h))
      (arm_cartan_zero i j hi hj hij) t u
  · intro i j _hi _hj hij t u
    exact commute_positive_negative
      _ _ (fun h => hij ((typeDRootPairing_baseEquiv 2).injective h)) t u
  · intro i j hi hj hij t u
    exact commute_negative_negative_of_cartan_eq_zero
      _ _ (fun h => hij ((typeDRootPairing_baseEquiv 2).injective h))
      (arm_cartan_zero i j hi hj hij) t u

end Triality.Standard.OddFundamentalCentralizer.RankOne
