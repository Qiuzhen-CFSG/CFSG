module

public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Coordinates
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.SpecificGroups.PSL3Two.Cardinality
public import Mathlib.GroupTheory.Sylow

/-!
# Fixed points of subgroups of order three on the binary Steinberg module

A coordinate 3-cycle fixes precisely the matrices with coordinates
(a,b,b,a,a,b,0,0), giving an explicit equivalence with F₂². Since SL₃(2)
has order 168, every subgroup of order three is Sylow; conjugacy transports
the calculation to every such subgroup of the literal matrix group.

Source: the proof of Aschbacher–Smith H.6.3(3), printed p.387, and its use
in B.4.11, printed p.96 (combined manuscript of 1 March 2004).
-/

public section
open Matrix Representation Representation.BinaryOffender
open BinaryLinearThree BinaryLinearThree.IrreducibleCatalogue
namespace BinaryLinearThree.SteinbergStructure.ParabolicFactors
private theorem cycle_action (v : Steinberg) :
    coordinates (S cycle v) = cycleMatrix *ᵥ coordinates v := by
  rw [← coordinateMatrix_cycle]
  simp [coordinateMatrix, LinearMap.toMatrix'_mulVec]


private def fixedVector (a : ZMod 2 × ZMod 2) : Eight :=
  ![a.1,a.2,a.2,a.1,a.1,a.2,0,0]
private theorem fixed_test : ∀ v : Eight,
    cycleMatrix *ᵥ v = v ↔ fixedVector (v 0, v 1) = v := by decide +kernel
private theorem fixedVector_test : ∀ a : ZMod 2 × ZMod 2,
    cycleMatrix *ᵥ fixedVector a = fixedVector a := by decide
noncomputable def cycleFixedEquiv :
    fixedSpace S (Subgroup.zpowers cycle) ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2) where
  toFun v := (coordinates v.val 0, coordinates v.val 1)
  invFun a := ⟨coordinates.symm (fixedVector a), by
    rw [mem_fixedSpace_zpowers_iff]
    apply coordinates.injective
    rw [cycle_action, coordinates.apply_symm_apply]
    exact fixedVector_test a⟩
  left_inv v := by
    apply Subtype.ext
    apply coordinates.injective
    rw [coordinates.apply_symm_apply]
    apply (fixed_test _).mp
    rw [← cycle_action, (mem_fixedSpace_zpowers_iff S cycle v.val).mp v.property]
  right_inv a := by simp [fixedVector]
  map_add' v w := by simp
  map_smul' c v := by simp

theorem finrank_fixedSpace_cycle :
    Module.finrank (ZMod 2) (fixedSpace S (Subgroup.zpowers cycle)) = 2 := by
  simpa using cycleFixedEquiv.finrank_eq

theorem finrank_fixedSpace_order_three (X : Subgroup Group) (hX : Nat.card X = 3) :
    Module.finrank (ZMod 2) (fixedSpace S X) = 2 := by
  have hc : Nat.card (Subgroup.zpowers cycle) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by decide : cycle ^ 3 = 1) (by decide : cycle ≠ 1)
  let syl (K : Subgroup Group) (hK : Nat.card K = 3) : Sylow 3 Group :=
    (IsPGroup.of_card (n := 1) (by simpa using hK)).toSylow (by
      have hi := K.card_mul_index
      rw [hK, Matrix.PSL3Two.card_SL] at hi
      have hind : K.index = 56 := by omega
      rw [hind]
      decide)
  let P : Sylow 3 Group := syl (Subgroup.zpowers cycle) hc
  let Q : Sylow 3 Group := syl X hX
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Group P Q
  have he : (Subgroup.zpowers cycle).map (MulAut.conj g).toMonoidHom = X :=
    congrArg (fun T : Sylow 3 Group => (T : Subgroup Group)) hg
  rw [← he, ← (fixedSpaceConjEquiv S (Subgroup.zpowers cycle) g).finrank_eq]
  exact finrank_fixedSpace_cycle
end BinaryLinearThree.SteinbergStructure.ParabolicFactors
