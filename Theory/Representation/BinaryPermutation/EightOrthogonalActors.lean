module

public import Theory.LinearAlgebra.QuadraticPlaneDisplacement
public import Theory.Representation.BinaryPermutation.SymmetricEightTransvections
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.Representation.BinaryPermutationAlternatingActions
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.EightCoordinates
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.Geometry
public import Theory.ElementaryAbelian.Basic

/-!
# Small elementary actors on the orthogonal six-space

The faithful symmetric-eight action on the binary deleted module extends the
alternating-eight action. Its transvection theorem implies that a nonidentity
even involution moves at least two dimensions: a transvection would be an odd
transposition. The actual half-weight quadratic form has nondegenerate polar
form, so the plane-displacement theorem bounds an elementary even actor moving
at most one plane by two elements.

These are the lower bound and equality case in Aschbacher–Smith 13.8.32,
*The Classification of Quasithin Groups*, printed p.965. The application retains
the original quotient through the marked exterior/deleted-module equivalence.
The quadratic model and its attribution are inherited from the existing ATLAS
port via `TerminalOrthogonal.EightCoordinates`.
-/

public section
open Module Subgroup Representation
namespace BinaryPermutation.EightOrthogonalActors
abbrev Space := natural (Fin 8)

private noncomputable def linearAction : Equiv.Perm (Fin 8) →* (Space ≃ₗ[ZMod 2] Space) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Space).toMonoidHom.comp
    (naturalRepresentation (Fin 8)).asGroupHom

private theorem linearAction_injective : Function.Injective linearAction := fun _ _ h =>
  naturalRepresentation_injective (Fin 8) (by decide) (congrArg LinearEquiv.toLinearMap h)

/-- A nonidentity even involution moves at least two dimensions on the actual
six-dimensional deleted module. -/
theorem two_le_displacement (a : Equiv.Perm (Fin 8))
    (ha : a ∈ alternatingGroup (Fin 8)) (hne : a ≠ 1) (ha2 : a ^ 2 = 1) :
    2 ≤ finrank (ZMod 2) (naturalRepresentation (Fin 8) a - LinearMap.id).range := by
  by_contra! hsmall
  have hs := Representation.SymmetricEightTransvections.isSwap_of_transvection
    linearAction linearAction_injective a hne ha2
    (Representation.SymmetricEightTransvections.Linear.of_small_displacement
      (linearAction a) (by
        change finrank (ZMod 2) (naturalRepresentation (Fin 8) a - LinearMap.id).range ≤ 1
        omega))
  have he : Equiv.Perm.sign a = 1 := ha
  rw [hs.sign_eq] at he
  exact (by decide : (-1 : ℤˣ) ≠ 1) he

private theorem form_nondegenerate : TerminalOrthogonal.Eight.form.polarBilin.Nondegenerate := by
  let e := TerminalOrthogonal.Eight.splitIsometry
  have he : LinearMap.BilinForm.congr e.toLinearEquiv
      (ClassicalOrthogonal.formD 3 (ZMod 2)).polarBilin =
      TerminalOrthogonal.Eight.form.polarBilin := by
    ext x y
    change ClassicalOrthogonal.formD 3 (ZMod 2) (e.symm x + e.symm y) -
      ClassicalOrthogonal.formD 3 (ZMod 2) (e.symm x) -
      ClassicalOrthogonal.formD 3 (ZMod 2) (e.symm y) = _
    rw [← map_add, e.symm.map_app, e.symm.map_app, e.symm.map_app]
    rfl
  rw [← he]
  exact LinearMap.BilinForm.Nondegenerate.congr e.toLinearEquiv
    (ClassicalOrthogonal.polarD_nondegenerate (n := 3) (F := ZMod 2))

/-- On the orthogonal six-space an elementary even actor whose movement
lies in one plane has order at most two. -/
theorem card_le_two_of_plane_displacement
    (A : Subgroup (Equiv.Perm (Fin 8))) (hA : A ≤ alternatingGroup (Fin 8))
    (hsq : ∀ a ∈ A, a ^ 2 = 1)
    (P : Submodule (ZMod 2) Space) (hP : finrank (ZMod 2) P = 2)
    (hmove : ∀ a ∈ A, (naturalRepresentation (Fin 8) a - LinearMap.id).range ≤ P) :
    Nat.card A ≤ 2 := by
  apply QuadraticForm.card_le_two_of_plane_displacement
    TerminalOrthogonal.Eight.form form_nondegenerate (linearAction.comp A.subtype)
    (fun a => Subtype.ext (hsq a a.property))
    (fun a x => TerminalOrthogonal.Eight.form_invariant a x)
    (fun a ha => two_le_displacement a (hA a.property)
      (fun hh => ha (Subtype.ext hh)) (hsq a a.property)) P hP
  exact fun a => hmove a a.property

end BinaryPermutation.EightOrthogonalActors
