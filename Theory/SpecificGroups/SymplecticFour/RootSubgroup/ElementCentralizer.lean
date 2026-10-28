module

public import Theory.SpecificGroups.SymplecticFour.RootSubgroup

/-!
# Centralizers of nonidentity symplectic root elements

Every one of the eight standard root matrices has the form `1 + t • N`,
with N independent of the parameter. Cancellation of a nonzero scalar shows
that a matrix commuting with one nonidentity root element commutes with every
element of that root family. Restricting through the actual inclusion of the
derived subgroup gives the same assertion for its conjugation fixed points;
no identification of the derived carrier with the full group is assumed.

This is the root-action centralizer calculation used in Aschbacher–Smith,
combined manuscript (1 March 2004), E.6.23, printed p.254 (PDF p.265),
for the alternative E.6.8(2b) on printed p.247.
-/

public section

open Matrix Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.RootSubgroup

variable {F : Type*} [Field F]

private theorem rootMatrix_affine (r : Fin 8) (t : F) :
    rootMatrix r t = 1 + t • (rootMatrix r 1 - 1) := by
  fin_cases r <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.fromBlocks, Matrix.single]

/-- Centralizing one nonidentity matrix root element centralizes the whole
root family, for either root length and over any field. -/
theorem commute_element_of_ne_zero (r : Fin 8) {t : F} (ht : t ≠ 0) (g : Sp F)
    (hc : Commute g (rootElement r t)) (s : F) : Commute g (rootElement r s) := by
  have hm := congrArg (fun x : Sp F => x.val) hc.eq
  change g.val * rootMatrix r t = rootMatrix r t * g.val at hm
  rw [rootMatrix_affine, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, add_right_inj] at hm
  have hh : g.val * (rootMatrix r 1 - 1) = (rootMatrix r 1 - 1) * g.val :=
    (smul_right_injective _ ht) hm
  apply Subtype.ext
  change g.val * rootMatrix r s = rootMatrix r s * g.val
  rw [rootMatrix_affine, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, hh]

/-- The same fixed-point calculation on the literal derived carrier.
The subtype inclusion compares its conjugation with multiplication in Sp₄. -/
theorem derived_fixed_of_ne_zero (r : Fin 8) {t : F} (ht : t ≠ 0)
    (x : commutator (Sp F))
    (hx : (MulAut.conjNormal (H := commutator (Sp F)) (rootElement r t)) x = x)
    (s : F) :
    (MulAut.conjNormal (H := commutator (Sp F)) (rootElement r s)) x = x := by
  have hc : Commute (x : Sp F) (rootElement r t) := by
    have he := congrArg (fun y : commutator (Sp F) => (y : Sp F)) hx
    rw [MulAut.conjNormal_apply, mul_inv_eq_iff_eq_mul] at he
    exact he.symm
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, mul_inv_eq_iff_eq_mul]
  exact (commute_element_of_ne_zero r ht x hc s).symm.eq

end Theory.SpecificGroups.SymplecticFour.RootSubgroup
