module

public import Theory.SpecificGroups.ReeTwo.Relations
public import Mathlib.GroupTheory.PresentedGroup

/-!
# A universal interface for the Ree two centralizer core

The ten roots and their relations are those in `ReeTwo.CoreRelations`,
from Shinoda (1975), (2.3), pp. 81–82. We quotient the free group by these
relators and prove the universal property in the root notation. This gives
homomorphisms into actual groups once their root relations are established.

This module alone makes no assertion about the order of the presented group.
A faithful finite model and a normal form are needed to prove that it has
order 1024; matching cardinalities without this presentation is insufficient.
-/

@[expose] public section
namespace ReeTwo

@[simp] theorem map_rootWord {G H : Type*} [Group G] [Group H]
    (f : G →* H) (x : CoreRoot → G) (w : List CoreRoot) :
    f (rootWord x w) = rootWord (fun i => f (x i)) w := by
  induction w with
  | nil => simp
  | cons i w ih => simp only [rootWord_cons, map_mul, ih]

@[simp] theorem map_rightComm {G H : Type*} [Group G] [Group H]
    (f : G →* H) (a b : G) : f (rightComm a b) = rightComm (f a) (f b) := by
  simp only [rightComm, map_mul, map_inv]

/-- Relations are preserved under homomorphisms. -/
theorem CoreRelations.map {G H : Type*} [Group G] [Group H]
    {x : CoreRoot → G} (h : CoreRelations x) (f : G →* H) :
    CoreRelations (fun i => f (x i)) where
  square i := by simpa using congrArg f (h.square i)
  commutator i j hij := by simpa using congrArg f (h.commutator i j hij)

/-- Only core squares and core commutators enter this presentation. -/
def coreRelators : Set (FreeGroup CoreRoot) :=
  {r | (∃ i, r = FreeGroup.of i * FreeGroup.of i *
      (rootWord FreeGroup.of (coreSquare i))⁻¹) ∨
    ∃ i j, i < j ∧ r = rightComm (FreeGroup.of i) (FreeGroup.of j) *
      (rootWord FreeGroup.of (coreCommutator i j))⁻¹}

/-- The group presented by roots 3 through 12. -/
abbrev PresentedCore := PresentedGroup coreRelators

/-- The canonical root in the presented core. -/
def presentedRoot (i : CoreRoot) : PresentedCore := PresentedGroup.of i

/-- The canonical roots satisfy the complete core relations. -/
theorem presentedCore_relations : CoreRelations presentedRoot where
  square i := by
    have he := PresentedGroup.mk_eq_mk_of_mul_inv_mem
      (rels := coreRelators) (Or.inl ⟨i, rfl⟩)
    unfold presentedRoot PresentedGroup.of
    simpa only [map_mul, map_rootWord] using he
  commutator i j hij := by
    have he := PresentedGroup.mk_eq_mk_of_mul_inv_mem
      (rels := coreRelators) (Or.inr ⟨i, j, hij, rfl⟩)
    unfold presentedRoot PresentedGroup.of
    simpa only [map_rightComm, map_rootWord] using he

/-- A homomorphism into any group whose specified roots satisfy the core relations. -/
def corePresentationHom {G : Type*} [Group G] {x : CoreRoot → G}
    (h : CoreRelations x) : PresentedCore →* G :=
  PresentedGroup.toGroup (f := x) (by
    intro r hr
    rcases hr with ⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩
    · simp only [map_mul, map_inv, map_rootWord, FreeGroup.lift_apply_of,
        h.square, mul_inv_cancel]
    · simp only [map_mul, map_inv, map_rightComm, map_rootWord, FreeGroup.lift_apply_of,
        h.commutator i j hij, mul_inv_cancel])

@[simp] theorem corePresentationHom_root {G : Type*} [Group G] {x : CoreRoot → G}
    (h : CoreRelations x) (i : CoreRoot) : corePresentationHom h (presentedRoot i) = x i :=
  PresentedGroup.toGroup.of _

/-- The canonical roots generate the presented core. -/
theorem presentedCore_generated : Subgroup.closure (Set.range presentedRoot) = ⊤ :=
  PresentedGroup.closure_range_of coreRelators

/-- Homomorphisms from the core presentation are determined by their roots. -/
@[ext] theorem corePresentationHom_ext {G : Type*} [Group G]
    {f g : PresentedCore →* G} (h : ∀ i, f (presentedRoot i) = g (presentedRoot i)) :
    f = g := PresentedGroup.ext h

end ReeTwo
