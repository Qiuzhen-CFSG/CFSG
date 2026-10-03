module

public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cardinal bounds from certified coset coverings

A finite family of representatives covers a generated group if it contains the
identity and is closed, modulo left multiplication by a subgroup, under right
multiplication by every generator and its inverse. Each transition is an equality
in the group itself; a permutation action or an unverified coset table does not
supply these hypotheses.

Induction on words proves the covering, giving a surjection from the product of
the subgroup and the representative indices. Its cardinality bounds the group.
The presented-group specialization uses the canonical generators. This is the
usual coset-enumeration upper-bound argument, independent of a particular
presentation or enumeration algorithm.
-/

namespace Subgroup

/-- Evidence that a family of representatives is stable modulo a subgroup under
right multiplication by the generators and their inverses. -/
public structure GeneratorCosetCover {G α : Type*} [Group G]
    (H : Subgroup G) (g : α → G) (ι : Type*) where
  repr : ι → G
  initial : ι
  initial_eq : repr initial = 1
  step : ∀ i a, ∃ h : H, ∃ j, repr i * g a = h.val * repr j
  inv_step : ∀ i a, ∃ h : H, ∃ j, repr i * (g a)⁻¹ = h.val * repr j

/-- Certified transitions imply that every group element has a representative. -/
public theorem GeneratorCosetCover.covers {G α ι : Type*} [Group G]
    {H : Subgroup G} {g : α → G} (C : GeneratorCosetCover H g ι)
    (hgen : closure (Set.range g) = ⊤) (x : G) :
    ∃ h : H, ∃ i, x = h.val * C.repr i := by
  have hx : x ∈ closure (Set.range g) := by rw [hgen]; trivial
  induction hx using closure_induction_right with
  | one => exact ⟨1, C.initial, by simp [C.initial_eq]⟩
  | mul_right x _ y hy ih =>
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨h, i, rfl⟩ := ih
    obtain ⟨h', j, he⟩ := C.step i a
    refine ⟨h * h', j, ?_⟩
    change (h.val * C.repr i) * g a = (h.val * h'.val) * C.repr j
    rw [mul_assoc, he, ← mul_assoc]
  | mul_inv_cancel x _ y hy ih =>
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨h, i, rfl⟩ := ih
    obtain ⟨h', j, he⟩ := C.inv_step i a
    refine ⟨h * h', j, ?_⟩
    change (h.val * C.repr i) * (g a)⁻¹ = (h.val * h'.val) * C.repr j
    rw [mul_assoc, he, ← mul_assoc]

/-- A finite certified cover by a finite subgroup gives a finite cardinal bound. -/
public theorem GeneratorCosetCover.finite_card_le {G α ι : Type*} [Group G]
    {H : Subgroup G} {g : α → G} [Finite H] [Finite ι]
    (C : GeneratorCosetCover H g ι) (hgen : closure (Set.range g) = ⊤) :
    Finite G ∧ Nat.card G ≤ Nat.card H * Nat.card ι := by
  have hsurj : Function.Surjective (fun p : H × ι => p.1.val * C.repr p.2) := by
    intro x
    obtain ⟨h, i, hi⟩ := C.covers hgen x
    exact ⟨(h, i), hi.symm⟩
  refine ⟨Finite.of_surjective _ hsurj, ?_⟩
  simpa only [Nat.card_prod] using Nat.card_le_card_of_surjective _ hsurj

end Subgroup

namespace PresentedGroup

/-- The coset-cover bound specialized to the canonical generators of a presentation. -/
public theorem finite_card_le_of_cosetCover {α ι : Type*}
    {rels : Set (FreeGroup α)} (H : Subgroup (PresentedGroup rels))
    [Finite H] [Finite ι]
    (C : Subgroup.GeneratorCosetCover H PresentedGroup.of ι) :
    Finite (PresentedGroup rels) ∧ Nat.card (PresentedGroup rels) ≤ Nat.card H * Nat.card ι :=
  C.finite_card_le (closure_range_of rels)

end PresentedGroup
