module

public import Theory.Character.Induction
public import Theory.Character.ConjClassFunction
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.GroupTheory.Nilpotent

/-!
# Integer spans for Brauer induction

The induced linear-character lattice consists of finite integer combinations
of characters induced from one-dimensional subgroup characters. Membership
is equivalent to an explicit sum indexed by `Fin r`, with no denominators.

We also define the integer span of characters induced from nilpotent
subgroups. The reduction lemma isolates two mathematical inputs: generation
by those characters, and their membership in the induced linear-character
lattice. Neither generation nor monomiality is assumed as an axiom here.

This is the lattice bookkeeping for Brauer induction, as in Serre,
*Linear Representations of Finite Groups*, Chapter 10, together with the
monomiality of irreducible characters of finite nilpotent groups.
-/

open scoped BigOperators
noncomputable section

@[expose] public section

namespace BrauerInduction
variable {G : Type*} [Group G] [Fintype G]

/-- A subgroup together with a one-dimensional complex character. -/
abbrev LinearDatum (G : Type*) [Group G] := Σ H : Subgroup G, H →* ℂ

/-- The integer span of all induced one-dimensional subgroup characters. -/
def inducedLinearSpan (G : Type*) [Group G] [Fintype G] : Submodule ℤ (ClassFunction G) :=
  Submodule.span ℤ (Set.range fun d : LinearDatum G => inducedClassFunction d.1 d.2)

/-- Every generator belongs to the induced linear-character lattice. -/
theorem inducedLinear_mem (H : Subgroup G) (χ : H →* ℂ) :
    inducedClassFunction H χ ∈ inducedLinearSpan G :=
  Submodule.subset_span ⟨⟨H, χ⟩, rfl⟩

/-- Membership in the integer span is exactly a finite integral induction formula. -/
theorem mem_inducedLinearSpan_iff (f : ClassFunction G) :
    f ∈ inducedLinearSpan G ↔
      ∃ (r : ℕ) (H : Fin r → Subgroup G) (linear : ∀ j, H j →* ℂ)
        (a : Fin r → ℤ),
        ∀ g, f g = ∑ j, (a j : ℂ) * inducedClassFunction (H j) (linear j) g := by
  classical
  constructor
  · intro hf
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hf
    let e := (Fintype.equivFin c.support).symm
    refine ⟨Fintype.card c.support, fun j => (e j).val.1,
      fun j => (e j).val.2, fun j => c (e j).val, ?_⟩
    intro g
    have hsum : (∑ j, c (e j).val • inducedClassFunction (e j).val.1 (e j).val.2) = f := by
      calc
        _ = ∑ j : c.support, c j.val • inducedClassFunction j.val.1 j.val.2 :=
          e.sum_comp _
        _ = c.sum (fun d a => a • inducedClassFunction d.1 d.2) := by
          rw [Finsupp.sum]
          exact Finset.sum_coe_sort c.support
            (fun d => c d • inducedClassFunction d.1 d.2)
        _ = f := hc
    simpa [ClassFunction] using (congrFun hsum g).symm
  · rintro ⟨r, H, linear, a, hf⟩
    have heq : f = ∑ j, a j • inducedClassFunction (H j) (linear j) := by
      ext g
      simpa [ClassFunction] using hf g
    rw [heq]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (inducedLinear_mem (H j) (linear j))

/-- The integer span of ordinary characters induced from nilpotent subgroups. -/
def nilpotentInducedSpan (G : Type*) [Group G] [Fintype G] :
    Submodule ℤ (ClassFunction G) :=
  Submodule.span ℤ {f | ∃ (H : Subgroup G), Group.IsNilpotent H ∧
    ∃ φ : ClassFunction H, IsCharacter φ ∧ f = inducedClassFunction H φ}

/-- Generator-wise monomial induction implies inclusion of the two lattices. -/
theorem nilpotentInducedSpan_le
    (hmonomial : ∀ (H : Subgroup G), Group.IsNilpotent H →
      ∀ (φ : ClassFunction H), IsCharacter φ →
        inducedClassFunction H φ ∈ inducedLinearSpan G) :
    nilpotentInducedSpan G ≤ inducedLinearSpan G := by
  apply Submodule.span_le.mpr
  rintro f ⟨H, hH, φ, hφ, rfl⟩
  exact hmonomial H hH φ hφ

/-- Convert nilpotent-subgroup generation and monomial induction to the
explicit integral formula used by field-of-definition constructions. -/
theorem exists_integral_induction_of_nilpotent_span (χ : ConjClassFunction G)
    (hχ : ofConjClassFunction χ ∈ nilpotentInducedSpan G)
    (hmonomial : ∀ (H : Subgroup G), Group.IsNilpotent H →
      ∀ (φ : ClassFunction H), IsCharacter φ →
        inducedClassFunction H φ ∈ inducedLinearSpan G) :
    ∃ (r : ℕ) (H : Fin r → Subgroup G) (linear : ∀ j, H j →* ℂ)
      (a : Fin r → ℤ),
      ∀ g, χ (ConjClasses.mk g) =
        ∑ j, (a j : ℂ) * inducedClassFunction (H j) (linear j) g :=
  (mem_inducedLinearSpan_iff (ofConjClassFunction χ)).mp
    (nilpotentInducedSpan_le hmonomial hχ)

end BrauerInduction
