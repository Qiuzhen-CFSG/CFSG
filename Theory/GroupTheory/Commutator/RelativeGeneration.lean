module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Commutator bounds through relative normal generation

If H normalizes C and each Aᵢ lies in H with [Aᵢ,B]≤C, then
[⟨Aᵢ⟩,B]≤C. The elements of H centralizing B modulo C form a subgroup;
this proves the bound without asserting that C is ambient-normal.
The binary-join version supplies the seed-orbit calculation in
Aschbacher–Smith, D.1.4, printed p.176.
-/

public section
namespace Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G]
theorem commutator_iSup_le_of_relative_normal {ι : Sort*} (H B C : Subgroup G)
    (A : ι → Subgroup G) (hHC : H ≤ normalizer (C : Set G))
    (hAH : ∀ i, A i ≤ H) (hAB : ∀ i, ⁅A i,B⁆ ≤ C) :
    ⁅⨆ i, A i, B⁆ ≤ C := by
  let Z : Subgroup G :=
    { carrier := {x | x ∈ H ∧ ∀ b ∈ B, ⁅x,b⁆ ∈ C}
      one_mem' := ⟨H.one_mem, by simp⟩
      mul_mem' := by
        rintro x y ⟨hx,hxc⟩ ⟨hy,hyc⟩
        refine ⟨H.mul_mem hx hy, ?_⟩
        intro b hb
        rw [commutatorElement_mul_left_eq_conj_mul]
        exact C.mul_mem (le_normalizer_iff.mp hHC x hx _ (hyc b hb)) (hxc b hb)
      inv_mem' := by
        rintro x ⟨hx,hxc⟩
        refine ⟨H.inv_mem hx, ?_⟩
        intro b hb
        rw [commutatorElement_inv_left]
        have hinv : ⁅b,x⁆ ∈ C := by rw [← commutatorElement_inv]; exact C.inv_mem (hxc b hb)
        simpa only [inv_inv] using le_normalizer_iff.mp hHC x⁻¹ (H.inv_mem hx) _ hinv }
  have hAZ : (⨆ i, A i) ≤ Z := iSup_le fun i x hx =>
    ⟨hAH i hx, commutator_le.mp (hAB i) x hx⟩
  exact commutator_le.mpr fun x hx => (hAZ hx).2

theorem commutator_sup_le_of_relative_normal (H A B Q C : Subgroup G)
    (hHC : H ≤ normalizer (C : Set G)) (hAH : A ≤ H) (hBH : B ≤ H)
    (hAQ : ⁅A,Q⁆ ≤ C) (hBQ : ⁅B,Q⁆ ≤ C) : ⁅A ⊔ B,Q⁆ ≤ C := by
  have h := commutator_iSup_le_of_relative_normal H Q C
    (fun b : Bool => if b then A else B) hHC
    (by intro b; cases b <;> assumption) (by intro b; cases b <;> assumption)
  simpa only [iSup_bool_eq, Bool.false_eq_true, ↓reduceIte, sup_comm] using h
end Subgroup

