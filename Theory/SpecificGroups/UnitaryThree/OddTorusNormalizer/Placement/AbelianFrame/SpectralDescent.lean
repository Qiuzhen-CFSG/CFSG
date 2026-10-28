module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.AbelianFrame.Basic
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.AbelianFrame.SpectralDescent.SplitAssembly
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.AbelianFrame.SpectralDescent.InvariantLine
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.AbelianFrame.SpectralDescent.QuadraticFactor

/-!
# Descent of the abelian unitary spectrum

A common invariant line is anisotropic by the source no-Borel hypothesis.
Its actual vector representative consequently supplies the input to a
single-operator spectral descent theorem. Once that theorem proves splitting
over the original field, odd order and commutativity give a simultaneous
basis whose projective lines are fixed by the subgroup.

Reducibility supplies a common invariant line: a proper invariant plane has
an invariant orthogonal complement of dimension one. For each group element,
the norm-one eigenvalue on this line reduces its characteristic polynomial
to a quadratic over the fixed field, which splits over its quadratic
extension `E`. The final assembly discharges both inputs and constructs the
basis over `E`, without a splitting or normalizing-involution hypothesis.

Source: GLS4, Chapter 4, Lemma 3.11(a),
`refs/KGroup/GLS4/Chapter4.tex`, lines 585–603.
-/

public section

open BenderSuzuki.MatrixGroups
open scoped LinearAlgebra.Projectivization
namespace UnitaryThree.OddTorusNormalizer.AbelianFrame
variable {E : Type*} [Field E] [Finite E]

/-- The actual common-line and single-operator descent inputs suffice for
an eigenbasis over the original field. This interface keeps the two inputs
explicit; `exists_commonEigenbasis_of_reducible` constructs them below. -/
theorem exists_commonEigenbasis_of_commonEigenline_and_descent
    (J : HermitianForm 3 E) {n : ℕ} (hcard : Nat.card E = (2 ^ n) ^ 2)
    (H : Subgroup J.specialSubgroup) (hodd : Odd (Nat.card H)) [IsMulCommutative H]
    (hB : SpecialNoBorel J H)
    (hline : ∃ l : ℙ E (Fin 3 → E), l ∈ commonEigenlines J H)
    (hdescent : ∀ (g : J.specialSubgroup) (v : Fin 3 → E) (a : E),
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) ≠ 0 →
      specialNatural J g v = a • v → (specialNatural J g).charpoly.Splits) :
    ∃ b : Module.Basis (Fin 3) E (Fin 3 → E), IsCommonEigenbasis J H b := by
  obtain ⟨l, hl⟩ := hline
  obtain ⟨haniso, heigen⟩ := commonEigenline_rep_spectral_data J H hB hl
  apply exists_commonEigenbasis_of_split_charpolys J hcard H hodd
  intro h
  obtain ⟨a, ha⟩ := heigen h
  exact hdescent h.val l.rep a haniso ha

/-- A reducible odd abelian special-unitary action satisfying the source
no-Borel hypothesis has a simultaneous eigenbasis over the matrix field.
Both the common invariant line and spectral splitting are proved from the
stated hypotheses. -/
theorem exists_commonEigenbasis_of_reducible
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (H : Subgroup J.specialSubgroup) (hodd : Odd (Nat.card H)) [IsMulCommutative H]
    (hB : SpecialNoBorel J H)
    (hred : ¬ Representation.IsIrreducible ((specialNatural J).comp H.subtype)) :
    ∃ b : Module.Basis (Fin 3) E (Fin 3 → E), IsCommonEigenbasis J H b :=
  exists_commonEigenbasis_of_commonEigenline_and_descent J hcard H hodd hB
    (exists_commonEigenline_of_reducible J H hred)
    (special_charpoly_splits_of_anisotropic_eigenvector J hn hcard hfixed)

end UnitaryThree.OddTorusNormalizer.AbelianFrame
