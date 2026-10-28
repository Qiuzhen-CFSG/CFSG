module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic.NormNum
public import Mathlib.GroupTheory.Sylow

/-!
# Coordinate parabolics in S₃ × S₃

Fix the stabilizer of zero in each natural three-letter action. The two
parabolics are C₂ × S₃ and S₃ × C₂. Their intersection is a Sylow two-subgroup,
both have index three and are maximal, and their setwise product is the whole
group. The coordinate permutation homomorphisms have complementary factor
kernels and prescribe the two permutations independently.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.5.3
and I.5.7, printed pp. 419–420. The order calculations use kernel-checked
finite enumeration; prime index proves maximality.
-/

@[expose] public section

namespace SymmetricThreeProduct

abbrev S3 := Equiv.Perm (Fin 3)
abbrev G := S3 × S3

def pointStabilizer : Subgroup S3 := MulAction.stabilizer S3 (0 : Fin 3)
def leftParabolic : Subgroup G := pointStabilizer.prod ⊤
def rightParabolic : Subgroup G := (⊤ : Subgroup S3).prod pointStabilizer
def borel : Subgroup G := pointStabilizer.prod pointStabilizer
instance : DecidablePred (· ∈ pointStabilizer) := fun _ => inferInstanceAs (Decidable (_ = _))
instance : DecidablePred (· ∈ leftParabolic) := fun g => inferInstanceAs (Decidable (g.1 0 = 0 ∧ True))
instance : DecidablePred (· ∈ rightParabolic) := fun g => inferInstanceAs (Decidable (True ∧ g.2 0 = 0))
instance : DecidablePred (· ∈ borel) := fun g => inferInstanceAs (Decidable (g.1 0 = 0 ∧ g.2 0 = 0))

theorem mem_leftParabolic (g : G) : g ∈ leftParabolic ↔ g.1 0 = 0 := by
  simp [Subgroup.mem_prod, leftParabolic, pointStabilizer, MulAction.mem_stabilizer_iff]

theorem mem_rightParabolic (g : G) : g ∈ rightParabolic ↔ g.2 0 = 0 := by
  simp [Subgroup.mem_prod, rightParabolic, pointStabilizer, MulAction.mem_stabilizer_iff]

theorem parabolics_inf : leftParabolic ⊓ rightParabolic = borel := by
  ext g
  simp [Subgroup.mem_prod, leftParabolic, rightParabolic, borel]

theorem parabolics_ne : leftParabolic ≠ rightParabolic := by
  intro h
  have hm : ((1 : S3), Equiv.swap (0 : Fin 3) 1) ∈ leftParabolic := by rw [mem_leftParabolic]; rfl
  rw [h, mem_rightParabolic] at hm
  norm_num at hm

theorem parabolics_product (g : G) :
    ∃ p ∈ leftParabolic, ∃ r ∈ rightParabolic, p * r = g := by
  refine ⟨(1, g.2), ?_, (g.1, 1), ?_, ?_⟩
  · rw [mem_leftParabolic]; rfl
  · rw [mem_rightParabolic]; rfl
  · simp

theorem card_group : Nat.card G = 36 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_borel : Nat.card borel = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_leftParabolic : Nat.card leftParabolic = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_rightParabolic : Nat.card rightParabolic = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem index_leftParabolic : leftParabolic.index = 3 := by
  have h := leftParabolic.card_mul_index
  rw [card_leftParabolic, card_group] at h
  omega

theorem index_rightParabolic : rightParabolic.index = 3 := by
  have h := rightParabolic.card_mul_index
  rw [card_rightParabolic, card_group] at h
  omega

theorem index_borel : borel.index = 9 := by
  have h := borel.card_mul_index
  rw [card_borel, card_group] at h
  omega

noncomputable def sylow : Sylow 2 G :=
  (IsPGroup.of_card (show Nat.card borel = 2 ^ 2 by rw [card_borel]; decide)).toSylow
    (by rw [index_borel]; decide)

@[simp] theorem sylow_coe : (sylow : Subgroup G) = borel := rfl

private theorem isCoatom_of_index_three (P : Subgroup G) (hP : P.index = 3) :
    IsCoatom P := by
  refine ⟨?_, ?_⟩
  · intro h
    simp [h] at hP
  · intro U hU
    have hd : U.index ∣ 3 := (Subgroup.index_dvd_of_le hU.le).trans (dvd_of_eq hP)
    rcases (show Nat.Prime 3 by decide).eq_one_or_self_of_dvd _ hd with h | h
    · exact Subgroup.index_eq_one.mp h
    · have he := Subgroup.relIndex_mul_index hU.le
      rw [hP, h] at he
      have hr : P.relIndex U = 1 := by omega
      exact (hU.not_ge (Subgroup.relIndex_eq_one.mp hr)).elim

theorem leftParabolic_isCoatom : IsCoatom leftParabolic :=
  isCoatom_of_index_three _ index_leftParabolic

theorem rightParabolic_isCoatom : IsCoatom rightParabolic :=
  isCoatom_of_index_three _ index_rightParabolic

/-- The actual first-coordinate permutation representation. -/
def leftAction : G →* Equiv.Perm (Fin 3) := MonoidHom.fst _ _

/-- The actual second-coordinate permutation representation. -/
def rightAction : G →* Equiv.Perm (Fin 3) := MonoidHom.snd _ _

theorem ker_leftAction : leftAction.ker = (⊥ : Subgroup S3).prod ⊤ := by
  ext g
  change g.1 = 1 ↔ g.1 ∈ (⊥ : Subgroup S3) ∧ g.2 ∈ (⊤ : Subgroup S3)
  simp

theorem ker_rightAction : rightAction.ker = (⊤ : Subgroup S3).prod ⊥ := by
  ext g
  change g.2 = 1 ↔ g.1 ∈ (⊤ : Subgroup S3) ∧ g.2 ∈ (⊥ : Subgroup S3)
  simp

/-- Each permutation can be prescribed independently of the other. -/
theorem independent_actions (a b : Equiv.Perm (Fin 3)) :
    ∃ g : G, leftAction g = a ∧ rightAction g = b := ⟨(a, b), rfl, rfl⟩

/-- The joint action on the two three-element sets is faithful. -/
theorem joint_action_faithful {g h : G}
    (hl : ∀ i, leftAction g i = leftAction h i)
    (hr : ∀ i, rightAction g i = rightAction h i) : g = h :=
  Prod.ext (Equiv.ext hl) (Equiv.ext hr)

end SymmetricThreeProduct
