module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic.NormNum

/-!
# Subgroups of order twenty-four in the five-point symmetric group

A Sylow two-subgroup has order eight and fixes a point in the odd-sized
five-point set. The whole group's orbit of that point has size one or three.
An invariant three-point set would embed the group in S₃ × S₂, of order
twelve. Therefore the point is fixed by the whole group, and equality with
its S₄ stabilizer follows by counting.

This uses the literal permutation action and does not enumerate subgroups.
Source application: Aschbacher–Smith, Remark 14.7.64 and the proof of14.7.70,
printed pp.1069–1074, the image of the original parabolic L₁T in H/O₂(H).
-/

public section

noncomputable section
open Subgroup MulAction
namespace Theory.SpecificGroups.Alternating.FivePointTwentyFour
local notation "S5" => Equiv.Perm (Fin 5)

private theorem card_stabilizer (i : Fin 5) : Nat.card (stabilizer S5 i) = 24 := by
  have hindex : (stabilizer S5 i).index = 5 := by
    rw [index_stabilizer, orbit_eq_univ]
    simp
  have hc := (stabilizer S5 i).card_mul_index
  have hS : Nat.card S5 = 120 := by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  rw [hindex, hS] at hc
  omega

private theorem invariant_three_card_le (I : Subgroup S5) (O : Set (Fin 5))
    (hO : Nat.card O = 3) (hinv : ∀ g : I, ∀ x, g.val x ∈ O ↔ x ∈ O) :
    Nat.card I ≤ 12 := by
  classical
  let f : I → Equiv.Perm O × Equiv.Perm {x : Fin 5 // x ∉ O} := fun g =>
    ⟨g.val.subtypePerm (hinv g), g.val.subtypePerm (fun x => not_congr (hinv g x))⟩
  have hf : Function.Injective f := by
    intro g h he
    apply Subtype.ext
    apply Equiv.ext
    intro x
    by_cases hx : x ∈ O
    · exact congrArg Subtype.val (congrArg (fun p => p.1 ⟨x, hx⟩) he)
    · exact congrArg Subtype.val (congrArg (fun p => p.2 ⟨x, hx⟩) he)
  have hb := Nat.card_le_card_of_injective f hf
  have hOf : Fintype.card O = 3 := by
    simpa only [Nat.card_eq_fintype_card] using hO
  have hOc : Fintype.card {x : Fin 5 // x ∉ O} = 2 := by
    rw [Fintype.card_subtype_compl, hOf]
    rfl
  have hsize : Nat.card (Equiv.Perm O × Equiv.Perm {x : Fin 5 // x ∉ O}) = 12 := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_perm, hOf, hOc]
    rfl
  exact hsize ▸ hb

/-- A subgroup of order twenty-four in the natural symmetric group on five
points is an actual point stabilizer. -/
theorem exists_eq_stabilizer (I : Subgroup S5) (hI : Nat.card I = 24) :
    ∃ i : Fin 5, I = stabilizer S5 i := by
  classical
  let P : Sylow 2 I := default
  have hP : Nat.card P = 8 := by
    rw [P.card_eq_multiplicity, hI]
    decide +kernel
  obtain ⟨i, hi⟩ := P.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card (Fin 5)
    (by norm_num)
  have hle : (P : Subgroup I) ≤ stabilizer I i := by
    intro g hg
    exact hi ⟨g, hg⟩
  have hindex : (P : Subgroup I).index = 3 := by
    have h := (P : Subgroup I).card_mul_index
    rw [hP, hI] at h
    omega
  have hd : (stabilizer I i).index ∣ 3 := hindex ▸ index_dvd_of_le hle
  have hfix : i ∈ fixedPoints I (Fin 5) := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with h | h
    · have he : stabilizer I i = ⊤ := index_eq_one.mp h
      intro g
      exact show g ∈ stabilizer I i from he.symm ▸ mem_top g
    · have hO : Nat.card (orbit I i) = 3 := by
        simpa only [index_stabilizer, Nat.card_coe_set_eq] using h
      have hinv (g : I) (x : Fin 5) : g.val x ∈ orbit I i ↔ x ∈ orbit I i := by
        constructor
        · rintro ⟨a, ha⟩
          refine ⟨g⁻¹ * a, ?_⟩
          change g.val⁻¹ (a.val i) = x
          change a.val i = g.val x at ha
          rw [ha]
          exact g.val.symm_apply_apply x
        · rintro ⟨a, rfl⟩
          exact ⟨g * a, rfl⟩
      have hb := invariant_three_card_le I (orbit I i) hO hinv
      omega
  refine ⟨i, eq_of_le_of_card_ge ?_ ?_⟩
  · intro g hg
    exact hfix ⟨g, hg⟩
  · rw [card_stabilizer, hI]
end Theory.SpecificGroups.Alternating.FivePointTwentyFour
