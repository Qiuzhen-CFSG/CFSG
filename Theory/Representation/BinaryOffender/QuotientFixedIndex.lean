module
public import Theory.Representation.BinaryOffender.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A centralizer index bound from quotient coordinates

Surjective coordinates from a finite subgroup onto a binary representation
carry its literal centralizer into the fixed space. The fixed-space preimage
therefore has no larger index than the centralizer. Counting the quotient
gives the fixed-codimension lower bound without requiring an ambient normal
kernel.

Source application: Aschbacher–Smith 3.3.28, printed p.601, retaining the
central kernel of the intrinsic six-dimensional G₂ block quotient.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender
variable {G D V : Type*} [Group G] [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Fixed quotient coordinates give a lower bound on the literal centralizer index. -/
theorem quotient_centralizer_index_le
    (σ : Representation (ZMod 2) D V)
    (X A : Subgroup G) [Finite X]
    (α : X →* Multiplicative V) (hα : Function.Surjective α) (β : A →* D)
    (hfix : ∀ (x : X), (x : G) ∈ centralizer (A : Set G) →
      ∀ a : A, σ (β a) (α x).toAdd = (α x).toAdd) :
    2 ^ fixedCodim σ β.range ≤ (centralizer (A : Set G)).relIndex X := by
  let F : Subgroup (Multiplicative V) :=
    (fixedSpace σ β.range).toAddSubgroup.toSubgroup
  have hf : F.index = 2 ^ fixedCodim σ β.range := by
    have hc := F.card_mul_index
    have hF : Nat.card F = 2 ^ Module.finrank (ZMod 2) (fixedSpace σ β.range) := by
      exact (Module.natCard_eq_pow_finrank
        (K := ZMod 2) (V := fixedSpace σ β.range)).trans (by rw [Nat.card_zmod])
    have hV : Nat.card (Multiplicative V) = 2 ^ Module.finrank (ZMod 2) V := by
      exact (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)).trans
        (by rw [Nat.card_zmod])
    rw [hF, hV, ← fixedCodim_add_finrank σ β.range, add_comm, pow_add] at hc
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hc
  have hle : (centralizer (A : Set G)).subgroupOf X ≤ F.comap α := by
    intro x hx
    change (α x).toAdd ∈ fixedSpace σ β.range
    rintro ⟨a, b, rfl⟩
    exact hfix x hx b
  calc
    2 ^ fixedCodim σ β.range = F.index := hf.symm
    _ = (F.comap α).index := (F.index_comap_of_surjective hα).symm
    _ ≤ ((centralizer (A : Set G)).subgroupOf X).index := index_antitone hle

end Representation.BinaryOffender
