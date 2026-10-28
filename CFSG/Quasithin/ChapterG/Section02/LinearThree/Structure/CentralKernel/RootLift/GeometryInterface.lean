module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.CentralKernel.Interface

/-!
# The remaining finite-matrix calculation for G.2.5

The actual order and natural action identify a point radical. A normalized
Sylow containing it must be covered by that radical and the intersection
with one of its conjugates, with trivial intersection between the two
factors. This is a geometric obligation in SL₃, without a central extension.
`RootLift` discharges every hypothesis when applying it to the source.

Source: Aschbacher–Smith G.2.5(3), printed pp.335–336.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.CentralKernel
open Setup

/-- The finite SL₃ flag calculation needed for the root lift. Its premises
specify an actual point radical by its order and natural action. -/
def ModelRootGeometry (F : Type*) [Field F] : Prop :=
  ∀ (point : Submodule F (Fin 3 → F)) (A : Subgroup SL(3, F)) (R : Sylow 2 SL(3, F)),
    Module.finrank F point = 1 → Nat.card A = Nat.card F ^ 2 →
    (∀ a ∈ A, ∀ v : Fin 3 → F, a.val *ᵥ v - v ∈ point) →
    (∀ a ∈ A, ∀ v ∈ point, a.val *ᵥ v = v) →
    A ≤ R → (R : Subgroup SL(3, F)) ≤ normalizer (A : Set SL(3, F)) →
    ∃ x : SL(3, F),
      Disjoint A ((R : Subgroup SL(3, F)) ⊓ A.map (MulAut.conj x⁻¹).toMonoidHom) ∧
      (R : Subgroup SL(3, F)) ≤ A ⊔
        ((R : Subgroup SL(3, F)) ⊓ A.map (MulAut.conj x⁻¹).toMonoidHom)


end CFSG.Quasithin.ChapterG.Section02.LinearThree.CentralKernel
