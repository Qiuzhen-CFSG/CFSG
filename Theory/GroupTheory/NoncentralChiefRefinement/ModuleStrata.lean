module

public import Theory.GroupTheory.NoncentralChiefRefinement.Actions
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Data.ZMod.Basic

/-!
# Equivariant coordinates for binary strata

A homogeneous stratum is an actual relative quotient isomorphic to a finite
power of a specified binary representation. Coordinates intertwine its literal
conjugation action. A central stratum is assigned multiplicity zero.

Zero copies give equal endpoints. Positive multiplicity is noncentral if the
specified representation acts nontrivially. The separate irreducibility
hypothesis used in chief refinement must not be confused with nontrivial action:
the trivial one-dimensional representation is also irreducible.

These definitions are the input interface for the chief-factor accounting in
Aschbacher–Smith, G.2.5(8), printed pp.335–336. They assume no chief conclusion.
-/

@[expose] public section
open Subgroup
namespace NoncentralChiefRefinement
variable {K : Type*} [Group K]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Actual coordinates for a homogeneous binary section. Equivariance refers
to the literal ambient conjugation action and the specified representation. -/
structure SectionCoordinates (A B : NormalNode K)
    (ρ : Representation (ZMod 2) K V) (m : ℕ) where
  equiv : Section A B ≃* Multiplicative (Fin m → V)
  equivariant (k : K) (x : Section A B) (i : Fin m) :
    (equiv (sectionAction A B k x)).toAdd i = ρ k ((equiv x).toAdd i)

/-- A central stratum contributes zero; any other stratum is supplied as a
literal quotient with homogeneous equivariant coordinates. This records no
chief intervals or counts. -/
def IsModuleStratum (ρ : Representation (ZMod 2) K V)
    (A B : NormalNode K) (m : ℕ) : Prop :=
  (IsCentral A B ∧ m = 0) ∨ Nonempty (SectionCoordinates A B ρ m)

namespace SectionCoordinates
variable {A B C D : NormalNode K} {ρ : Representation (ZMod 2) K V} {m : ℕ}

/-- Transport preserves the specified representation, not merely dimensions. -/
def transport (c : SectionCoordinates A B ρ m) (e : SectionEquiv C D A B) :
    SectionCoordinates C D ρ m where
  equiv := e.equiv.trans c.equiv
  equivariant k x i := by
    change (c.equiv (e.equiv (sectionAction C D k x))).toAdd i = _
    rw [e.equivariant]
    exact c.equivariant k (e.equiv x) i

/-- Zero multiplicity gives a repeated coarse term, not a chief factor. -/
theorem endpoints_eq_of_zero (hAB : A ≤ B) (c : SectionCoordinates A B ρ 0) : A = B := by
  have hs : Subsingleton (Section A B) := ⟨fun x y =>
    c.equiv.injective (Subsingleton.elim _ _)⟩
  have ht : A.val.subgroupOf B.val = ⊤ := QuotientGroup.subsingleton_iff.mp hs
  exact Subtype.ext (le_antisymm hAB (Subgroup.subgroupOf_eq_top.mp ht))

/-- A positive homogeneous section is noncentral when the specified module
has nontrivial action. Irreducibility alone would not exclude the trivial
one-dimensional binary representation. -/
theorem not_isCentral (c : SectionCoordinates A B ρ m) (hm : 0 < m)
    (hρ : ∃ k v, ρ k v ≠ v) : ¬ IsCentral A B := by
  intro hc
  obtain ⟨k, v, hv⟩ := hρ
  obtain ⟨x, hx⟩ := c.equiv.surjective (Multiplicative.ofAdd (fun _ : Fin m => v))
  have he := c.equivariant k x ⟨0, hm⟩
  rw [(isCentral_iff_action A B).mp hc k x, hx] at he
  exact hv he.symm

end SectionCoordinates


end NoncentralChiefRefinement
