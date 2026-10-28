module
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.Geometry

/-!
# Type inertia and homogeneous orbits

An order action on actual subrepresentations that transports equivariant
isomorphisms has an inertia subgroup for each simple type. If inertia fixes
a constituent, its distinct orbit members have distinct types, hence form
an independent family of homogeneous summands. The converse follows by
inclusion of every isomorphic conjugate in the homogeneous part.

Source: Aschbacher–Smith, Lemma A.1.42(1),(3), printed p.32.
-/
@[expose] public section
noncomputable section
open scoped MonoidAlgebra
namespace Representation.BinaryOffender.Homogeneous
variable {E W P : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) E W} [Group P]

/-- An action on actual subrepresentations, preserving their isomorphism relation.
The normalizer action in the literal central quotient supplies this structure. -/
structure TypeAction (σ : Representation (ZMod 2) E W) (P : Type*) [Group P] where
  conjugate : P → Subrepresentation σ ≃o Subrepresentation σ
  one : ∀ A, conjugate 1 A = A
  mul : ∀ t u A, conjugate (t * u) A = conjugate t (conjugate u A)
  same : ∀ t A B, SameModule A B ↔ SameModule (conjugate t A) (conjugate t B)

namespace TypeAction
variable (c : TypeAction σ P)

@[simp] theorem inv_conjugate (t : P) (A : Subrepresentation σ) :
    c.conjugate t⁻¹ (c.conjugate t A) = A := by
  rw [← c.mul, inv_mul_cancel, c.one]

@[simp] theorem conjugate_inv (t : P) (A : Subrepresentation σ) :
    c.conjugate t (c.conjugate t⁻¹ A) = A := by
  rw [← c.mul, mul_inv_cancel, c.one]

/-- The inertia subgroup of the actual isomorphism class of A. -/
def inertia (A : Subrepresentation σ) : Subgroup P where
  carrier := {t | SameModule A (c.conjugate t A)}
  one_mem' := by rw [Set.mem_ofPred_eq, c.one]; exact SameModule.refl A
  mul_mem' := by
    intro t u ht hu
    change SameModule A (c.conjugate (t * u) A)
    rw [c.mul]
    exact ht.trans ((c.same t A (c.conjugate u A)).mp hu)
  inv_mem' := by
    intro t ht
    have h := (c.same t⁻¹ A (c.conjugate t A)).mp ht
    rw [c.inv_conjugate] at h
    exact h.symm

/-- The sum of the actual translates. -/
def span (A : Subrepresentation σ) : Subrepresentation σ := ⨆ t, c.conjugate t A

theorem le_span (A : Subrepresentation σ) : A ≤ c.span A := by
  change A ≤ ⨆ t, c.conjugate t A
  exact (c.one A).ge.trans (le_iSup (fun t => c.conjugate t A) 1)

theorem conjugate_span (t : P) (A : Subrepresentation σ) :
    c.conjugate t (c.span A) = c.span A := by
  change c.conjugate t (⨆ u, c.conjugate u A) = ⨆ u, c.conjugate u A
  rw [(c.conjugate t).map_iSup]
  apply le_antisymm
  · exact iSup_le fun u => by rw [← c.mul]; exact le_iSup (fun u => c.conjugate u A) (t * u)
  · refine iSup_le fun u => ?_
    exact le_iSup_of_le (t⁻¹ * u) (by rw [← c.mul, mul_inv_cancel_left])

/-- Distinct translates, each recorded once. -/
def orbit (A : Subrepresentation σ) : Set (Subrepresentation σ) :=
  Set.range (fun t => c.conjugate t A)

theorem iSup_orbit (A : Subrepresentation σ) :
    (⨆ B : c.orbit A, B.val.toSubmodule) = (c.span A).toSubmodule := by
  rw [span, toSubmodule_iSup]
  apply le_antisymm
  · apply iSup_le
    rintro ⟨B, t, rfl⟩
    exact le_iSup (fun t => (c.conjugate t A).toSubmodule) t
  · refine iSup_le fun t => ?_
    exact le_iSup (fun B : c.orbit A => B.val.toSubmodule) ⟨_, t, rfl⟩

theorem conjugate_irreducible (A : Subrepresentation σ)
    (hA : IsIrreducible A.toRepresentation) (t : P) :
    IsIrreducible (c.conjugate t A).toRepresentation := by
  rw [Subrepresentation.irreducible_iff_isAtom] at hA ⊢
  exact ((c.conjugate t).isAtom_iff A).mpr hA

/-- Fixation by type inertia forces distinct orbit members to have different types. -/
theorem orbit_not_sameModule (A : Subrepresentation σ)
    (hfix : ∀ t ∈ c.inertia A, c.conjugate t A = A)
    (B C : c.orbit A) (hne : B ≠ C) : ¬ SameModule B.val C.val := by
  obtain ⟨B, t, rfl⟩ := B
  obtain ⟨C, u, rfl⟩ := C
  intro he
  have h := (c.same t⁻¹ (c.conjugate t A) (c.conjugate u A)).mp he
  rw [c.inv_conjugate, ← c.mul] at h
  have hf := hfix (t⁻¹ * u) h
  have heq := congrArg (c.conjugate t) hf
  rw [← c.mul, mul_inv_cancel_left] at heq
  exact hne (Subtype.ext heq.symm)

/-- Homogeneity is equivalent to fixation by the inertia subgroup. -/
theorem homogeneous_iff_inertia_fixes (A : Subrepresentation σ)
    (hA : IsIrreducible A.toRepresentation) :
    homogeneousPart A (c.span A).toSubmodule = A.toSubmodule ↔
      ∀ t ∈ c.inertia A, c.conjugate t A = A := by
  constructor
  · intro hh t ht
    have hle : (c.conjugate t A).toSubmodule ≤ homogeneousPart A (c.span A).toSubmodule :=
      le_iSup_of_le (c.conjugate t A)
        (le_iSup_of_le ⟨show c.conjugate t A ≤ c.span A from le_iSup (fun t => c.conjugate t A) t, ht⟩ le_rfl)
    rw [hh] at hle
    apply ((Subrepresentation.irreducible_iff_isAtom A).mp hA).le_iff_eq
      ((Subrepresentation.irreducible_iff_isAtom _).mp (c.conjugate_irreducible A hA t)).ne_bot |>.mp
    exact hle
  · intro hfix
    let a : c.orbit A := ⟨A, 1, c.one A⟩
    have hfamily (B : c.orbit A) : IsIrreducible B.val.toRepresentation := by
      obtain ⟨B, t, rfl⟩ := B
      exact c.conjugate_irreducible A hA t
    have h := homogeneousPart_family (fun B : c.orbit A => B.val) hfamily a
      (fun B hB => c.orbit_not_sameModule A hfix a B hB.symm)
    rw [c.iSup_orbit] at h
    exact h

/-- Homogeneous orbits are independent as a whole family of binary subspaces. -/
theorem orbit_independent (A : Subrepresentation σ)
    (hA : IsIrreducible A.toRepresentation)
    (hh : homogeneousPart A (c.span A).toSubmodule = A.toSubmodule) :
    iSupIndep (fun B : c.orbit A => B.val.toSubmodule) := by
  apply independent_of_pairwise_not_sameModule
  · rintro ⟨B, t, rfl⟩
    exact c.conjugate_irreducible A hA t
  · exact c.orbit_not_sameModule A ((c.homogeneous_iff_inertia_fixes A hA).mp hh)

end TypeAction
end Representation.BinaryOffender.Homogeneous
