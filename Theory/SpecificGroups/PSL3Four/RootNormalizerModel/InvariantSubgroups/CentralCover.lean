module
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.InvariantSubgroups
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Basic
public import Theory.GroupTheory.CentralDerivedKernelGeneration
public import Theory.ElementaryAbelian.Injective

/-!
# Diagonal rigidity in actual perfect Sylow covers

The coordinate rigidity theorem lifts through a central kernel contained in
the Sylow derived subgroup. Elementary full preimages ensure that a
non-elementary subgroup still has non-elementary image. Central Sylow transfer
then removes the possible covering kernel from the generation conclusion.
The explicit coordinate equivalence uses the same three matrix entries as
the general-field marks used by Chapter 2.

Source: Aschbacher--Smith 2.5.7, printed p.556, including the possible
exceptional central two-cover rather than assuming its center is trivial.
-/

@[expose] public section
open Subgroup
namespace Matrix.PSL3Four.RootNormalizerModel

/-- The general-field and fixed-field unitriangular carriers have identical
matrix coordinates and multiplication. -/
def evenRootEquiv : PSL3Even.UnipotentGeometry.U F ≃* Root where
  toFun q := ⟨q.x, q.y, q.c⟩
  invFun q := ⟨q.x, q.y, q.c⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable {P : Type*} [Group P]

/-- Elementary full preimages and a central derived kernel lift diagonal
rigidity to the original Sylow cover. -/
theorem diagonal_invariant_cover_eq_top
    (f : P →* Root) (hc : f.ker ≤ center P)
    (hd : f.ker ≤ _root_.commutator P)
    (hlift : ∀ W : Subgroup Root, IsElementaryAbelian 2 W →
      IsElementaryAbelian 2 (W.comap f))
    (A : Subgroup P)
    (hinv : ∀ d : Fˣ × Fˣ, ∀ q ∈ A.map f, diagonal d q ∈ A.map f)
    (hne : ¬ IsElementaryAbelian 2 A) : A = ⊤ := by
  have hneImage : ¬ IsElementaryAbelian 2 (A.map f) := by
    intro he
    let := hlift (A.map f) he
    let i : A →* (A.map f).comap f :=
      Subgroup.inclusion (le_comap_map f A)
    exact hne (IsElementaryAbelian.of_injective i (Subgroup.inclusion_injective _))
  exact eq_top_of_map_eq_top_of_central_derived_kernel f hc hd A
    (diagonal_invariant_eq_top (A.map f) hinv hneImage)

/-- Apply the preceding theorem to an actual Sylow subgroup of a perfect
central cover. The kernel is the literal restriction of the ambient center. -/
theorem diagonal_invariant_sylow_cover_eq_top
    {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (P : Sylow 2 K) (f : P →* Root)
    (hk : f.ker = (center K).subgroupOf P)
    (hlift : ∀ W : Subgroup Root, IsElementaryAbelian 2 W →
      IsElementaryAbelian 2 (W.comap f))
    (A : Subgroup P)
    (hinv : ∀ d : Fˣ × Fˣ, ∀ q ∈ A.map f, diagonal d q ∈ A.map f)
    (hne : ¬ IsElementaryAbelian 2 A) : A = ⊤ := by
  have hc : f.ker ≤ center P := by
    rw [hk]
    intro a ha
    exact mem_center_iff.mpr (fun b => Subtype.ext (mem_center_iff.mp ha b))
  have hd : f.ker ≤ _root_.commutator P := by
    rw [hk]
    exact center_subgroupOf_sylow_le_commutator P
  exact diagonal_invariant_cover_eq_top f hc hd hlift A hinv hne
end Matrix.PSL3Four.RootNormalizerModel
