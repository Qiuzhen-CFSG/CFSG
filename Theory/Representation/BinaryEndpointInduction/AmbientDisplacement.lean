module
public import Theory.Representation.ElementaryPerfectSplit
public import Theory.GroupTheory.Commutator.Basic
public import Mathlib.FieldTheory.Finiteness

/-!
# Literal ambient displacement as a binary subspace

An elementary abelian ambient subgroup gives a canonical binary subspace
from its group commutator. Its order is unchanged, and every displacement
from the specified conjugation action lies in that subspace.
-/
public noncomputable section
namespace BinaryEndpointInduction
open Subgroup
open scoped IsMulCommutative

/-- The actual ambient commutator supplies a subspace of the same order,
containing all differences for the specified conjugation action. -/
theorem exists_ambient_displacement
    {G X : Type*} [Group G] [Finite G] [Group X]
    (C W L : Subgroup G) [IsElementaryAbelian 2 W]
    (q : C →* X) (hLC : L ≤ C) (hLW : L ≤ normalizer W)
    (σ : Representation (ZMod 2) X (Additive W))
    (hσ : ∀ (x : C) (w : Additive W),
      ((σ (q x) w).toMul : G)=x*(w.toMul : G)*(x : G)⁻¹) :
    ∃ D : Submodule (ZMod 2) (Additive W),
      Nat.card D=Nat.card (⁅W,L⁆ : Subgroup G) ∧
      (∀ (l : L) (w : Additive W), σ (q ⟨l,hLC l.property⟩) w-w ∈ D) := by
  let T := ⁅W,L⁆
  have hTW : T ≤ W := le_normalizer_iff_commutator_le_left.mp hLW
  let D : Submodule (ZMod 2) (Additive W) :=
    AddSubgroup.toZModSubmodule 2 (T.subgroupOf W).toAddSubgroup
  have hd : Nat.card D=Nat.card T := by
    have he : D ≃ T.subgroupOf W :=
      { toFun := fun x => ⟨x.val.toMul,x.property⟩
        invFun := fun x => ⟨Additive.ofMul x.val,x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (Nat.card_congr he).trans
      (Nat.card_congr (subgroupOfEquivOfLe hTW).toEquiv)
  refine ⟨D,hd,?_⟩
  intro l w
  change ((σ (q ⟨l,hLC l.property⟩) w-w).toMul : G) ∈ T
  rw [toMul_sub, Subgroup.coe_div, div_eq_mul_inv]
  rw [hσ]
  have hc := commutator_mem_commutator l.property w.toMul.property
  rw [commutator_comm L W] at hc
  exact hc

end BinaryEndpointInduction
