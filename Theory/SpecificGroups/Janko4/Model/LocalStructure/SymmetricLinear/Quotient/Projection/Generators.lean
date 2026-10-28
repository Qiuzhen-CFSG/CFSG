module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Model

/-!
# Candidate generator images for the literal max4 quotient

These are the two literal ATLAS subgroup generators and their proposed images
in S₅ × SL₃(2). The determinant-one identities are checked here; descent from
the actual 112-dimensional matrices and generation of the product are separate
obligations. Thus these definitions alone assert no quotient identification.

The permutation factors invert the right actions on row vectors, whereas the
matrix factors use ordinary matrix multiplication. This convention is required
by Lean's composition law on `Equiv.Perm`.

Source: ATLAS `J4G1-max4W1` and `J4G1-f2r112B0`, attributed in
`SymmetricLinear.Model` and `Janko4.Model.Data`. The source application is
Aschbacher–Smith, Proposition 1.3.4, printed p.511/PDF p.528. Exploration data
and its untrusted status are documented in `Projection/source/README.md`.
-/

@[expose] public section
namespace Janko4.LocalStructure.SymmetricLinear.Projection

/-- The first literal ATLAS output in its generated subgroup. -/
def first : max4Subgroup :=
  ⟨(max4Program a b).1, Subgroup.subset_closure (Set.mem_insert _ _)⟩
/-- The second literal ATLAS output in its generated subgroup. -/
def second : max4Subgroup :=
  ⟨(max4Program a b).2, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

/-- Inverse of the first right-action permutation of the five binary rows. -/
def firstPerm : Equiv.Perm (Fin 5) where
  toFun := ![0, 1, 2, 4, 3]
  invFun := ![0, 1, 2, 4, 3]
  left_inv := by decide
  right_inv := by decide

/-- Inverse of the second right-action permutation of the five binary rows. -/
def secondPerm : Equiv.Perm (Fin 5) where
  toFun := ![2, 0, 4, 3, 1]
  invFun := ![1, 4, 0, 3, 2]
  left_inv := by decide
  right_inv := by decide

/-- Proposed first action on the three-dimensional section, packed rows `[5,6,4]`. -/
def firstLinear : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 1; 0, 1, 1; 0, 0, 1], by decide +kernel⟩

/-- Proposed second action on the three-dimensional section, packed rows `[7,5,3]`. -/
def secondLinear : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![1, 1, 1; 1, 0, 1; 1, 1, 0], by decide +kernel⟩

/-- The proposed first image in the genuine product carrier. -/
def firstImage : QuotientModel := (firstPerm, firstLinear)
/-- The proposed second image in the genuine product carrier. -/
def secondImage : QuotientModel := (secondPerm, secondLinear)

end Janko4.LocalStructure.SymmetricLinear.Projection
