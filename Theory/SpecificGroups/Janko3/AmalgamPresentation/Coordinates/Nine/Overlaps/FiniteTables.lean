module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.Overlaps.Basic
import Mathlib.Tactic.FinCases

/-! Finite projective representative tables retain exact subgroup carriers. -/
@[expose] public section
namespace Sporadic.Janko3.AmalgamPresentation.NineCoordinates.OverlapTables
open Subgroup

/-- The first nonzero first-row entry is the chosen projective pivot. -/
def pivot (m : GL9) : F := if m 0 0 = 0 then m 0 1 else m 0 0

theorem pivot_scalar (m : GL9) (u : Fˣ) :
    pivot (m * Matrix.GeneralLinearGroup.scalar (Fin 2) u) = pivot m * (u : F) := by
  classical
  have he (i j : Fin 2) : (m * Matrix.GeneralLinearGroup.scalar (Fin 2) u) i j = m i j * (u : F) := by
    simp [Matrix.GeneralLinearGroup.coe_scalar,Matrix.scalar]
  unfold pivot
  rw [he,he]
  by_cases hm : m 0 0 = 0 <;> simp [hm,Units.ne_zero u]

/-- Equality of projective classes of normalized matrices is literal equality. -/
theorem normalized_injective {m n : GL9} (hm : pivot m = 1) (hn : pivot n = 1)
    (h : Matrix.ProjGenLinGroup.mk m = Matrix.ProjGenLinGroup.mk n) : m = n := by
  obtain ⟨u,hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  have hp := congrArg pivot hu
  rw [pivot_scalar,hm,hn,one_mul] at hp
  have he : u = 1 := Units.ext hp
  simpa [he] using hu

/-- Signed right transitions plus actual membership identify the entire closure. -/
theorem closure_eq_range {G α ι : Type*} [Group G] (g : α → G) (r : ι → G)
    (i₀ : ι) (h₀ : r i₀ = 1)
    (hm : ∀ i, r i ∈ closure (Set.range g))
    (step : ∀ i a, ∃ j, r i * g a = r j)
    (back : ∀ i a, ∃ j, r i * (g a)⁻¹ = r j) :
    (closure (Set.range g) : Set G) = Set.range r := by
  ext x
  constructor
  · intro hx
    induction hx using closure_induction_right with
    | one => exact ⟨i₀,h₀⟩
    | mul_right x hx y hy ih =>
      obtain ⟨i,rfl⟩ := ih
      obtain ⟨a,rfl⟩ := hy
      obtain ⟨j,hj⟩ := step i a
      exact ⟨j,hj.symm⟩
    | mul_inv_cancel x hx y hy ih =>
      obtain ⟨i,rfl⟩ := ih
      obtain ⟨a,rfl⟩ := hy
      obtain ⟨j,hj⟩ := back i a
      exact ⟨j,hj.symm⟩
  · rintro ⟨i,rfl⟩
    exact hm i

/-- An acyclic table of positive generator edges proves actual membership. -/
theorem row_mem_of_parent {G : Type*} [Group G] {n : Nat} [NeZero n]
    (g : Bool → G) (r : Fin n → G) (h₀ : r 0 = 1)
    (parent : Fin n → Fin n) (letter : Fin n → Bool)
    (hp : ∀ i, i ≠ 0 → (parent i).val < i.val)
    (he : ∀ i, i ≠ 0 → r i = r (parent i) * g (letter i)) :
    ∀ i, r i ∈ closure (Set.range g) := by
  have h (k : Nat) : ∀ hk : k < n, r ⟨k,hk⟩ ∈ closure (Set.range g) := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      by_cases h0 : k = 0
      · subst k
        rw [show (⟨0,hk⟩ : Fin n) = 0 from rfl,h₀]
        exact one_mem _
      · have hi : (⟨k,hk⟩ : Fin n) ≠ 0 := fun hh => h0 (congrArg Fin.val hh)
        rw [he _ hi]
        exact mul_mem (ih _ (hp _ hi) (parent ⟨k,hk⟩).isLt)
          (subset_closure (Set.mem_range_self _))
  intro i
  exact h i.val i.isLt

noncomputable def subgroupEquivOfRange {G ι : Type*} [Group G] (H : Subgroup G)
    (r : ι → G) (hr : Function.Injective r) (he : (H : Set G) = Set.range r) : ι ≃ H :=
  Equiv.ofBijective (fun i => ⟨r i,by change r i ∈ (H : Set G); rw [he]; exact Set.mem_range_self i⟩) (by
    constructor
    · intro i j hij
      exact hr (congrArg Subtype.val hij)
    · intro x
      have hx : x.val ∈ Set.range r := by
        rw [←he]
        exact x.property
      obtain ⟨i,hi⟩ := hx
      exact ⟨i,Subtype.ext hi⟩)

theorem card_of_range {G : Type*} [Group G] {n : Nat} (H : Subgroup G)
    (r : Fin n → G) (hr : Function.Injective r) (he : (H : Set G) = Set.range r) :
    Nat.card H = n := by
  rw [←Nat.card_congr (subgroupEquivOfRange H r hr he)]
  exact Nat.card_fin n

end Sporadic.Janko3.AmalgamPresentation.NineCoordinates.OverlapTables
