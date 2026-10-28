module

public import Theory.Representation.BinaryOffender.Basic

/-!
# The centralizer of offender displacements

For a subgroup `A` acting on a binary module, `displacementCentralizer ρ A`
is the concrete subgroup `C_A([V,A])`: it fixes every vector `ρ a v - v`.
It acts quadratically, since its own displacements are among those of `A`.
The nontriviality and equal-weight assertions of Timmesfeld replacement are
separate results; they are not part of this definition.

Source: GLS, *The Classification of the Finite Simple Groups*, vol. 2,
Theorem 26.23(i), and the construction in the proof of Theorem 26.24.
-/

@[expose] public section
namespace Representation.BinaryOffender

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The actual subgroup `C_A([V,A])`, defined by fixing displacement generators. -/
def displacementCentralizer (A : Subgroup G) : Subgroup G where
  carrier := {c | c ∈ A ∧ ∀ a ∈ A, ∀ v : V, ρ c (ρ a v - v) = ρ a v - v}
  one_mem' := ⟨A.one_mem, by simp⟩
  mul_mem' := by
    rintro c d ⟨hc, hcfix⟩ ⟨hd, hdfix⟩
    refine ⟨A.mul_mem hc hd, fun a ha v => ?_⟩
    rw [map_mul]
    change ρ c (ρ d (ρ a v - v)) = _
    rw [hdfix a ha v, hcfix a ha v]
  inv_mem' := by
    rintro c ⟨hc, hcfix⟩
    refine ⟨A.inv_mem hc, fun a ha v => ?_⟩
    have h := congrArg (ρ c⁻¹) (hcfix a ha v)
    have hmul : ρ c⁻¹ (ρ c (ρ a v - v)) = ρ a v - v := by
      change (ρ c⁻¹ * ρ c) (ρ a v - v) = _
      rw [← map_mul, inv_mul_cancel, map_one]
      rfl
    exact (hmul.symm.trans h).symm

@[simp] theorem mem_displacementCentralizer {A : Subgroup G} {c : G} :
    c ∈ displacementCentralizer ρ A ↔
      c ∈ A ∧ ∀ a ∈ A, ∀ v : V, ρ c (ρ a v - v) = ρ a v - v := Iff.rfl

theorem displacementCentralizer_le (A : Subgroup G) :
    displacementCentralizer ρ A ≤ A := fun _ hc => hc.1

/-- The replacement subgroup is quadratic without any weight hypothesis. -/
theorem displacementCentralizer_isQuadratic (A : Subgroup G) :
    IsQuadratic ρ (displacementCentralizer ρ A) := by
  intro c hc d hd v
  exact hc.2 d hd.1 v

/-- Every displacement of `A` is fixed by its displacement centralizer. -/
theorem displacement_mem_fixedSpace_displacementCentralizer
    {A : Subgroup G} {a : G} (ha : a ∈ A) (v : V) :
    ρ a v - v ∈ fixedSpace ρ (displacementCentralizer ρ A) := by
  rw [fixedSpace, Representation.mem_invariants]
  intro c
  exact c.property.2 a ha v

/-- For an elementary abelian `A`, nontriviality is the only missing condition
for its displacement centralizer to be elementary two. -/
theorem displacementCentralizer_isElementaryTwo {A : Subgroup G}
    (hA : IsElementaryTwo A) (hne : displacementCentralizer ρ A ≠ ⊥) :
    IsElementaryTwo (displacementCentralizer ρ A) :=
  hA.of_le (displacementCentralizer_le ρ A) hne

end Representation.BinaryOffender
