import Theory.AtlasPort.LinearGroups.Symplectic.Generation
import Mathlib.GroupTheory.IsPerfect
set_option warningAsError false

noncomputable section
namespace Atlas.Symplectic
open scoped commutatorElement
variable {n : ℕ} {F : Type*} [Field F]

/-- A nonexceptional field contains a nonzero scalar whose square is not one. -/
theorem exists_scalar_square_ne_one [Finite F] (hq : 3 < Nat.card F) :
    ∃ c : F, c ≠ 0 ∧ c^2 ≠ 1 := by
  classical
  let := Fintype.ofFinite F
  have hcard : ({0,1,-1} : Finset F).card < (Finset.univ : Finset F).card := by
    have h := Finset.card_le_three (a := (0 : F)) (b := 1) (c := -1)
    simpa only [Finset.card_univ,← Nat.card_eq_fintype_card] using lt_of_le_of_lt h hq
  obtain ⟨c,_,hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hc
  exact ⟨c,hc.1,fun h => (sq_eq_one_iff.mp h).elim hc.2.1 hc.2.2⟩

/-- A scalar conjugation gives each transvection as an actual commutator. -/
theorem transvection_mem_commutator_of_scalar (c : F) (hc : c ≠ 0) (hc₂ : c^2 ≠ 1)
    (v : Vector n F) (a : F) : transvection v a ∈ commutator (Sp n F) := by
  by_cases hv : v = 0
  · subst v
    simp
  obtain ⟨g,_,hg⟩ := exists_generated_send hv (smul_ne_zero hc hv)
  let b := a/(c^2-1)
  have hb : (c^2-1)*b=a := by dsimp [b]; exact mul_div_cancel₀ a (sub_ne_zero.mpr hc₂)
  have he : ⁅g,transvection v b⁆ = transvection v a := by
    rw [commutatorElement_def,transvection_conjugate,hg,transvection_scale,
      transvection_inverse,← transvection_add]
    congr 1
    have h : c^2*b + -b = (c^2-1)*b := by ring
    rw [h,hb]
  rw [← he]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- Full perfectness from the already verified full transvection generation. -/
theorem perfect_of_transvections
    (h : ∀ (v : Vector n F) (a : F), transvection v a ∈ commutator (Sp n F)) :
    Group.IsPerfect (Sp n F) := by
  constructor
  apply top_unique
  rw [← transvectionGroup_eq_top (n := n) (F := F)]
  apply (Subgroup.closure_le _).mpr
  rintro t ⟨v,a,rfl⟩
  exact h v a

theorem perfect_of_card_gt_three [Finite F] (hq : 3 < Nat.card F) : Group.IsPerfect (Sp n F) := by
  obtain ⟨c,hc,hc₂⟩ := exists_scalar_square_ne_one hq
  exact perfect_of_transvections (transvection_mem_commutator_of_scalar c hc hc₂)

theorem projective_perfect_of_card_gt_three [Finite F] (hq : 3 < Nat.card F) :
    Group.IsPerfect (PSp n F) := by
  let := perfect_of_card_gt_three (n := n) hq
  infer_instance

end Atlas.Symplectic
