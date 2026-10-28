module

public import Theory.SpecificGroups.ClassicalUnitary.SylowOvergroupParabolics.Placement.Flags
public import Theory.SpecificGroups.ClassicalUnitary.SylowOvergroupParabolics.Placement.Bruhat
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Coordinate contracts for unitary Bruhat and flag geometry

A Witt basis has antidiagonal Gram matrix and identifies every member of
the complete isotropic flag with its initial coordinate space. The monomial
condition refers to actual special-unitary representatives in this basis,
not to an abstract Weyl-group tag.

These shared definitions separate the concrete Bruhat construction from the
Borel-overgroup argument. The latter can use the former as an explicit input
while it proves root extraction and invariant-subspace existence. Existence
of the data is a separate theorem, not a consequence of this record.

Source: GLS3, §§2.3 and 2.6--2.7, with coordinates ordered along the
antidiagonal Hermitian form.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix Subgroup Theory.GroupTheory

namespace Theory.SpecificGroups.ClassicalUnitary.SylowOvergroupParabolics

variable {F : Type*} [Field F] {d : ℕ} (J : HermitianForm d F)

/-- An actual antidiagonal Hermitian basis adapted to the full flag. -/
structure WittCoordinates (f : IsotropicFlag J) where
  basis : Module.Basis (Fin d) F (Fin d → F)
  gram : ∀ i j, dotProduct (fun k => J.conj (basis i k))
    (J.form.mulVec (basis j)) = if i = Fin.rev j then 1 else 0
  flag_eq : ∀ i, f.space i = Submodule.span F
    (basis '' {j : Fin d | j.val ≤ i.val})

/-- A projective element has a representative permuting the basis lines,
with every scalar coefficient nonzero. -/
def WittCoordinates.IsMonomial {f : IsotropicFlag J}
    (C : WittCoordinates J f) (x : ProjectiveSpecialUnitaryMatrixGroup J) : Prop :=
  ∃ g : J.specialSubgroup, project J g = x ∧
    ∃ σ : Equiv.Perm (Fin d), ∀ i, ∃ t : F, t ≠ 0 ∧
      linearAction J g (C.basis i) = t • C.basis (σ i)

/-- Concrete shared inputs for the unitary flag argument. The Bruhat data
has an actual Sylow subgroup and normal-generation proof; the monomial
subgroup acts on the actual Witt frame. No overgroup conclusion is assumed. -/
structure FlagBruhatData where
  flag : IsotropicFlag J
  coordinates : WittCoordinates J flag
  bruhat : SylowBruhatData flag.borel
  monomial_frame : ∀ n ∈ bruhat.monomial, coordinates.IsMonomial J n

end Theory.SpecificGroups.ClassicalUnitary.SylowOvergroupParabolics
