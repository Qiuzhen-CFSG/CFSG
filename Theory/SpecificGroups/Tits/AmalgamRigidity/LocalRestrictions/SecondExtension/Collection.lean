module

public import Theory.SpecificGroups.Tits.AmalgamRigidity.LocalRestrictions.SecondExtension.Words
import Mathlib.Tactic.Group

/-!
# Normal forms from the second-parabolic collection equations

Successive cyclic collection gives 2048 Sylow words. Right-generator induction
and the literal three-coset transitions extend this to 6144 words in every
finite group satisfying the equations. We apply this to the graph subgroup,
so no faithfulness or presentation assumption is hidden in the construction.
Source: Parrott (1972), §5, p.683; proof adapted from
`Atlas1600SylowTwoEnumeration` and `SecondOrder`.
-/

@[expose] public section
namespace Tits.AmalgamRigidity.SecondExtension
open Theory.GroupTheory RelativeSecondBlockLayers
variable {G : Type*} [Group G] (g : Fin 9 → G)

local notation "s₁" => g 1
local notation "s₂" => g 2
local notation "s₃" => g 3
local notation "s₄" => g 4
local notation "s₅" => g 5
local notation "s₆" => g 6
local notation "s₇" => g 7
local notation "s₈" => g 8

private theorem conjugates_1 :
    ∀ b ∈ (∅ : Set G),
      s₁ * b * s₁⁻¹ ∈ Subgroup.closure (∅ : Set G) := by
  simp

private theorem conjugates_2 (h : SylowRelations g) :
    ∀ b ∈ ({s₁} : Set G),
      s₂ * b * s₂⁻¹ ∈ Subgroup.closure {s₁} := by
  intro b hb
  simp only [Set.mem_singleton_iff] at hb
  subst b
  rw [h.conjugate_2_1]
  repeat first
    | apply Subgroup.mul_mem
    | apply Subgroup.pow_mem
    | exact Subgroup.subset_closure (by simp)

private theorem conjugates_3 (h : SylowRelations g) :
    ∀ b ∈ ({s₂, s₁} : Set G),
      s₃ * b * s₃⁻¹ ∈ Subgroup.closure {s₂, s₁} := by
  intro b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
  rcases hb with rfl | rfl
  · rw [h.conjugate_3_2]
    repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.pow_mem
      | exact Subgroup.subset_closure (by simp)
  · rw [h.conjugate_3_1]
    repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.pow_mem
      | exact Subgroup.subset_closure (by simp)

private theorem conjugates_4 (h : SylowRelations g) :
    ∀ b ∈ ({s₃, s₂, s₁} : Set G),
      s₄ * b * s₄⁻¹ ∈ Subgroup.closure {s₃, s₂, s₁} := by
  intro b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
  rcases hb with rfl | rfl | rfl
  · rw [h.conjugate_4_3]
    repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.pow_mem
      | exact Subgroup.subset_closure (by simp)
  · rw [h.conjugate_4_2]
    repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.pow_mem
      | exact Subgroup.subset_closure (by simp)
  · rw [h.conjugate_4_1]
    repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.pow_mem
      | exact Subgroup.subset_closure (by simp)

private theorem conjugates_5 (h : SylowRelations g) :
    ∀ b ∈ ({s₄, s₃, s₂, s₁} : Set G),
      s₅ * b * s₅⁻¹ ∈ Subgroup.closure {s₄, s₃, s₂, s₁} := by
  intro b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · rw [h.conjugate_5_4]
    repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.pow_mem
      | exact Subgroup.subset_closure (by simp)
  · rw [h.conjugate_5_3]
    repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.pow_mem
      | exact Subgroup.subset_closure (by simp)
  · rw [h.conjugate_5_2]
    repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.pow_mem
      | exact Subgroup.subset_closure (by simp)
  · rw [h.conjugate_5_1]
    repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.pow_mem
      | exact Subgroup.subset_closure (by simp)

private theorem conjugates_6 (h : SylowRelations g) :
    ∀ b ∈ ({s₅, s₄, s₃, s₂, s₁} : Set G),
      s₆ * b * s₆⁻¹ ∈ Subgroup.closure {s₅, s₄, s₃, s₂, s₁} := by
  intro b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · rw [h.conjugate_6_5]
    repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.pow_mem
      | exact Subgroup.subset_closure (by simp)
  · rw [h.conjugate_6_4]
    repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.pow_mem
      | exact Subgroup.subset_closure (by simp)
  · rw [h.conjugate_6_3]
    repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.pow_mem
      | exact Subgroup.subset_closure (by simp)
  · rw [h.conjugate_6_2]
    repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.pow_mem
      | exact Subgroup.subset_closure (by simp)
  · rw [h.conjugate_6_1]
    repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.pow_mem
      | exact Subgroup.subset_closure (by simp)

private theorem conjugates_7 (h : SylowRelations g) :
    ∀ b ∈ ({s₆, s₅, s₄, s₃, s₂, s₁} : Set G),
      s₇ * b * s₇⁻¹ ∈ Subgroup.closure {s₆, s₅, s₄, s₃, s₂, s₁} := by
  intro b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.conjugate_7_6]
    repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.pow_mem
      | exact Subgroup.subset_closure (by simp)
  · rw [h.conjugate_7_5]
    repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.pow_mem
      | exact Subgroup.subset_closure (by simp)
  · rw [h.conjugate_7_4]
    repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.pow_mem
      | exact Subgroup.subset_closure (by simp)
  · rw [h.conjugate_7_3]
    repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.pow_mem
      | exact Subgroup.subset_closure (by simp)
  · rw [h.conjugate_7_2]
    repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.pow_mem
      | exact Subgroup.subset_closure (by simp)
  · rw [h.conjugate_7_1]
    repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.pow_mem
      | exact Subgroup.subset_closure (by simp)

private theorem conjugates_8 (h : SylowRelations g) :
    ∀ b ∈ ({s₇, s₆, s₅, s₄, s₃, s₂, s₁} : Set G),
      s₈ * b * s₈⁻¹ ∈ Subgroup.closure {s₇, s₆, s₅, s₄, s₃, s₂, s₁} := by
  intro b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.conjugate_8_7]
    repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.pow_mem
      | exact Subgroup.subset_closure (by simp)
  · rw [h.conjugate_8_6]
    repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.pow_mem
      | exact Subgroup.subset_closure (by simp)
  · rw [h.conjugate_8_5]
    repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.pow_mem
      | exact Subgroup.subset_closure (by simp)
  · rw [h.conjugate_8_4]
    repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.pow_mem
      | exact Subgroup.subset_closure (by simp)
  · rw [h.conjugate_8_3]
    repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.pow_mem
      | exact Subgroup.subset_closure (by simp)
  · rw [h.conjugate_8_2]
    repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.pow_mem
      | exact Subgroup.subset_closure (by simp)
  · rw [h.conjugate_8_1]
    repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.pow_mem
      | exact Subgroup.subset_closure (by simp)

/-- Each enumerated word belongs to the generated subgroup. -/
theorem word_mem (n : Fin 2048) :
    word g n ∈ sylowClosure g := by
  rw [sylowClosure, word]
  repeat first
    | apply Subgroup.mul_mem
    | apply Subgroup.pow_mem
    | exact Subgroup.subset_closure (by simp)

/-- A Sylow word belongs to any subgroup containing its eight letters. -/
theorem word_mem_of (H : Subgroup G) (h : ∀ a : Fin 9, a ≠ 0 → g a ∈ H)
    (n : Fin 2048) : word g n ∈ H := by
  simp only [word]
  repeat first
    | apply Subgroup.mul_mem
    | apply Subgroup.pow_mem
    | exact h _ (by decide)

/-- Every displayed normal form is in the subgroup generated by its letters. -/
theorem normalForm_mem (p : Fin 2048 × Fin 3) :
    word g p.1 * rep g p.2 ∈ Subgroup.closure (Set.range g) := by
  simp only [word, rep]
  repeat first
    | apply Subgroup.mul_mem
    | apply Subgroup.pow_mem
    | exact Subgroup.subset_closure ⟨_, rfl⟩

variable [Finite G]

/-- Every element of the generated subgroup has an ordered normal form. -/
theorem word_surjective (h : SylowRelations g)
    {x : G} (hx : x ∈ sylowClosure g) :
    ∃ n : Fin 2048, word g n = x := by
  rw [sylowClosure] at hx
  obtain ⟨y7, hy7, a8, rfl⟩ :=
    exists_mul_pow_of_mem_closure_insert {s₇, s₆, s₅, s₄, s₃, s₂, s₁}
      s₈ 2 (by decide) h.power_8 (conjugates_8 g h) hx
  obtain ⟨y6, hy6, a7, rfl⟩ :=
    exists_mul_pow_of_mem_closure_insert {s₆, s₅, s₄, s₃, s₂, s₁}
      s₇ 4 (by decide) h.power_7 (conjugates_7 g h) hy7
  obtain ⟨y5, hy5, a6, rfl⟩ :=
    exists_mul_pow_of_mem_closure_insert {s₅, s₄, s₃, s₂, s₁}
      s₆ 2 (by decide) h.power_6 (conjugates_6 g h) hy6
  obtain ⟨y4, hy4, a5, rfl⟩ :=
    exists_mul_pow_of_mem_closure_insert {s₄, s₃, s₂, s₁}
      s₅ 4 (by decide) h.power_5 (conjugates_5 g h) hy5
  obtain ⟨y3, hy3, a4, rfl⟩ :=
    exists_mul_pow_of_mem_closure_insert {s₃, s₂, s₁}
      s₄ 2 (by decide) h.power_4 (conjugates_4 g h) hy4
  obtain ⟨y2, hy2, a3, rfl⟩ :=
    exists_mul_pow_of_mem_closure_insert {s₂, s₁}
      s₃ 4 (by decide) h.power_3 (conjugates_3 g h) hy3
  obtain ⟨y1, hy1, a2, rfl⟩ :=
    exists_mul_pow_of_mem_closure_insert {s₁}
      s₂ 2 (by decide) h.power_2 (conjugates_2 g h) hy2
  obtain ⟨y0, hy0, a1, rfl⟩ :=
    exists_mul_pow_of_mem_closure_insert (∅ : Set G)
      s₁ 2 (by decide) h.power_1 (conjugates_1 g) (by simpa using hy1)
  simp only [Subgroup.closure_empty, Subgroup.mem_bot] at hy0
  subst y0
  let n : Fin 2048 :=
    ⟨a1.val + 2 * a2.val + 4 * a3.val + 16 * a4.val + 32 * a5.val +
      128 * a6.val + 256 * a7.val + 1024 * a8.val, by omega⟩
  refine ⟨n, ?_⟩
  have h1 : n.val % 2 = a1.val := by dsimp [n]; omega
  have h2 : n.val / 2 % 2 = a2.val := by dsimp [n]; omega
  have h3 : n.val / 4 % 4 = a3.val := by dsimp [n]; omega
  have h4 : n.val / 16 % 2 = a4.val := by dsimp [n]; omega
  have h5 : n.val / 32 % 4 = a5.val := by dsimp [n]; omega
  have h6 : n.val / 128 % 2 = a6.val := by dsimp [n]; omega
  have h7 : n.val / 256 % 4 = a7.val := by dsimp [n]; omega
  have h8 : n.val / 1024 % 2 = a8.val := by dsimp [n]; omega
  simp only [word, h1, h2, h3, h4, h5, h6, h7, h8, one_mul]


/-- Collection in the entire group generated by the nine marked elements. -/
theorem normalForm_surjective (hs : SylowRelations g) (hc : CosetRelations g)
    {x : G} (hx : x ∈ Subgroup.closure (Set.range g)) :
    ∃ p : Fin 2048 × Fin 3, word g p.1 * rep g p.2 = x := by
  induction hx using Subgroup.closure_induction_right with
  | one => exact ⟨(0, 0), by simp [word, rep]⟩
  | mul_right x _ y hy ih =>
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨⟨n, i⟩, rfl⟩ := ih
    obtain ⟨m, hm⟩ := word_surjective g hs
      ((sylowClosure g).mul_mem (word_mem g n) (word_mem g (SecondOrder.factor a i)))
    refine ⟨(m, SecondOrder.dest a i), ?_⟩
    rw [hm, mul_assoc, ← hc a i, ← mul_assoc]
  | mul_inv_cancel x _ y hy ih =>
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨⟨n, i⟩, rfl⟩ := ih
    let j := SecondOrder.destInverse a i
    let k := SecondOrder.factor a j
    have ht : rep g j * g a = word g k * rep g i := by
      simpa only [j, k, SecondOrder.dest_inverse] using hc a j
    have he : rep g i * (g a)⁻¹ = (word g k)⁻¹ * rep g j := by
      calc
        rep g i * (g a)⁻¹ = (word g k)⁻¹ *
            (rep g j * g a) * (g a)⁻¹ := by rw [ht]; group
        _ = (word g k)⁻¹ * rep g j := by group
    obtain ⟨m, hm⟩ := word_surjective g hs
      ((sylowClosure g).mul_mem (word_mem g n)
        ((sylowClosure g).inv_mem (word_mem g k)))
    refine ⟨(m, j), ?_⟩
    rw [hm, mul_assoc, ← he, ← mul_assoc]


end Tits.AmalgamRigidity.SecondExtension
