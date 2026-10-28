/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/ThreeTranspositionFrames.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Commuting frames in three-transposition groups

Commuting involutions generate a two-group. Maximal commuting frames are
intersections with Sylow two-subgroups, so Sylow conjugacy gives frame conjugacy.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/ThreeTranspositionFrames.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and rewritten project imports;
the closure uses the current `IsMulCommutative` interface. The frame predicate
remains exposed for downstream calculations.
-/

@[expose] public section

noncomputable section
namespace Atlas.GroupTheory

/-- Maximality is among commuting subsets of the specified distinguished set. -/
def IsCommutingFrame {G : Type*} [Group G] (D F : Set G) : Prop :=
  F ⊆ D ∧ (∀ x ∈ F, ∀ y ∈ F, Commute x y) ∧
    ∀ E : Set G, E ⊆ D → (∀ x ∈ E, ∀ y ∈ E, Commute x y) → F ⊆ E → E = F

theorem commuting_involution_closure_isTwoGroup {G : Type*} [Group G]
    (F : Set G) (hsq : ∀ x ∈ F, x ^ 2 = 1)
    (hc : ∀ x ∈ F, ∀ y ∈ F, Commute x y) : IsPGroup 2 (Subgroup.closure F) := by
  let := Subgroup.isMulCommutative_closure (fun x hx y hy => (hc x hx y hy).eq)
  have hh : ∀ x (hx : x ∈ Subgroup.closure F), x ^ 2 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hsq x hx
    | one => simp
    | mul x y hx hy ihx ihy =>
      have hc' : Commute x y := by
        have ht := mul_comm' (⟨x,hx⟩ : Subgroup.closure F) ⟨y,hy⟩
        exact congrArg Subtype.val ht
      rw [hc'.mul_pow, ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  intro x
  refine ⟨1, ?_⟩
  apply Subtype.ext
  exact hh x.val x.property

/-- In a Sylow two-subgroup, the order-three alternative is impossible. -/
theorem threeTransposition_sylow_commute {G : Type*} [Group G]
    (D : Set G) (hsq : ∀ x ∈ D, x ^ 2 = 1)
    (hprod : ∀ x ∈ D, ∀ y ∈ D, (x*y)^2=1 ∨ orderOf (x*y)=3)
    (P : Sylow 2 G) (x y : G) (hx : x ∈ D ∩ (P : Set G))
    (hy : y ∈ D ∩ (P : Set G)) : Commute x y := by
  rcases hprod x hx.1 y hy.1 with h | h
  · have hi : x⁻¹=x := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hsq x hx.1)
    have hj : y⁻¹=y := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hsq y hy.1)
    have ht := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h)
    change x*y=y*x
    rw [← ht, mul_inv_rev, hi, hj]
  · have ht := P.isPGroup'.orderOf_coprime (by decide : Nat.Coprime 2 3)
      (⟨x*y,P.mul_mem hx.2 hy.2⟩ : P)
    rw [Subgroup.orderOf_mk, h] at ht
    norm_num at ht

/-- Every frame is exactly the distinguished elements in some Sylow two-subgroup.
No order or cardinality of the ambient finite group is specified. -/
theorem commutingFrame_eq_sylow_intersection {G : Type*} [Group G]
    (D F : Set G) (hsq : ∀ x ∈ D, x ^ 2 = 1)
    (hprod : ∀ x ∈ D, ∀ y ∈ D, (x*y)^2=1 ∨ orderOf (x*y)=3)
    (hF : IsCommutingFrame D F) :
    ∃ P : Sylow 2 G, F = D ∩ (P : Set G) := by
  have hp := commuting_involution_closure_isTwoGroup F
    (fun x hx => hsq x (hF.1 hx)) hF.2.1
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  refine ⟨P, (hF.2.2 _ (fun _ h => h.1)
    (fun x hx y hy => threeTransposition_sylow_commute D hsq hprod P x y hx hy) ?_).symm⟩
  intro x hx
  exact ⟨hF.1 hx,hP (Subgroup.subset_closure hx)⟩

/-- Sylow conjugacy gives frame conjugacy without any numerical group order. -/
theorem commutingFrames_conjugate {G : Type*} [Group G] [Finite G]
    (D F K : Set G) (hsq : ∀ x ∈ D, x ^ 2 = 1)
    (hprod : ∀ x ∈ D, ∀ y ∈ D, (x*y)^2=1 ∨ orderOf (x*y)=3)
    (hD : ∀ g : G, (MulAut.conj g) '' D = D)
    (hF : IsCommutingFrame D F) (hK : IsCommutingFrame D K) :
    ∃ g : G, (MulAut.conj g) '' F = K := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨P,rfl⟩ := commutingFrame_eq_sylow_intersection D F hsq hprod hF
  obtain ⟨Q,rfl⟩ := commutingFrame_eq_sylow_intersection D K hsq hprod hK
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G P Q
  refine ⟨g, ?_⟩
  rw [Set.image_inter (MulAut.conj g).injective, hD g]
  congr 1
  exact congrArg (fun R : Sylow 2 G => (R : Set G)) hg

end Atlas.GroupTheory
