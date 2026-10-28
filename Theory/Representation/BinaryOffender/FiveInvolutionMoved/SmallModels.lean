module

public import Theory.Representation.BinaryOffender.FiveInvolutionMoved
public import Theory.SpecificGroups.Suzuki.SmallAutomorphisms
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Involution movement in the small five-local models

In D10 and the faithful group C5:C4, every nonidentity involution has a
conjugate whose product with it has order five. The finite coordinate
identities are kernel checked. Transport to the actual actor and the affine
five-orbit bound give a moved plane for every subgroup of order two.
-/

public noncomputable section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [Finite V] (ρ : Representation (ZMod 2) G V)

private theorem model_bound {D : Type*} [Group D]
    (e : G ≃* D)
    (hpair : ∀ x : D, x^2=1 → x≠1 →
      ∃ g : D, (x*(g*x*g⁻¹))^5=1 ∧ x*(g*x*g⁻¹)≠1)
    (hf : Function.Injective ρ) (E : Subgroup G) (hE : Nat.card E = 2) :
    4 ≤ Nat.card (subspaceCommutator ρ ⊤ E) := by
  let : Finite E := Nat.finite_of_card_ne_zero (by rw [hE]; decide)
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := E) 2 (by rw [hE])
  have ht2 : (t : G)^2=1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h
    exact congrArg Subtype.val h
  have ht1 : (t : G)≠1 := by
    intro h
    have h' : t=1 := Subtype.ext h
    simp [h'] at ht
  obtain ⟨d,hd5,hd1⟩ := hpair (e t)
    (by rw [←map_pow,ht2,map_one]) (e.map_ne_one_iff.mpr ht1)
  let g := e.symm d
  have hfive : orderOf ((t : G)*(g*t*g⁻¹))=5 := by
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    rw [←e.orderOf_eq]
    simp only [map_mul,map_inv,g,e.apply_symm_apply]
    exact orderOf_eq_prime hd5 hd1
  exact four_le_card_subspaceCommutator_of_conjugate_five ρ hf E t t.property g hfive

/-- Every order-two subgroup of a faithfully represented D10 moves at least
a binary plane, including fixed summands in the ambient module. -/
theorem dihedral_five_four_le_card_subspaceCommutator
    (e : G ≃* DihedralGroup 5) (hf : Function.Injective ρ)
    (E : Subgroup G) (hE : Nat.card E = 2) :
    4 ≤ Nat.card (subspaceCommutator ρ ⊤ E) := by
  apply model_bound ρ e ?_ hf E hE
  decide +kernel

/-- The same whole-module bound for the actual small Suzuki matrix group
Sz(2), transported through its faithful C5:C4 coordinates. -/
theorem suzuki_zero_four_le_card_subspaceCommutator
    (e : G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)
    (hf : Function.Injective ρ) (E : Subgroup G) (hE : Nat.card E = 2) :
    4 ≤ Nat.card (subspaceCommutator ρ ⊤ E) := by
  apply model_bound ρ (e.trans FiveFour.suzukiZeroEquiv.symm) ?_ hf E hE
  decide +kernel

end Representation.BinaryOffender
