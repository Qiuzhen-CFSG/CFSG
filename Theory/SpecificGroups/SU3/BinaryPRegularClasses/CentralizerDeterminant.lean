module

public import Theory.SpecificGroups.SU3.BinaryPRegularClasses.CentralizerDeterminant.NormalCorrection
public import Theory.SpecificGroups.SU3.BinaryPRegularClasses.CentralizerDeterminant.IrreducibleNormal
public import Theory.SpecificGroups.SU3.BinaryPRegularClasses.CentralizerDeterminant.ReducibleNormal

/-!
# Unitary centralizer determinant surjectivity for binary SU₃

Every norm-one field unit is the determinant of a unitary matrix centralizing
any given odd-order special unitary element. The irreducible cubic case uses
the norm from the cubic root field. In the reducible nonscalar case, scaling
an eigenspace along its canonical invariant complement supplies a normal
linear witness; the scalar case uses an orthonormal basis. Adjoint correction
then makes these witnesses unitary with the prescribed determinant.

The proof uses the original nondegenerate Gram matrix and includes repeated
eigenvalues, isotropic eigenspaces, and the cubic center at odd exponents.
The exhaustive assembly is independent of the class-bound module
`BinaryPRegularClasses`.

Source context: GLS III 2.8.2, 2.8.6(a), and 2.8.10(c),
`refs/KGroup/GLS3/chapter2.tex`.
-/

namespace Theory.SpecificGroups.SU3.BinaryPRegularClasses
open Matrix BenderSuzuki.MatrixGroups CentralizerDeterminant
variable {F : Type*} [Field F] [Finite F]

/-- The determinant correction for the literal special unitary input, given
a normal linear centralizer witness. -/
public theorem exists_unitary_centralizer_det_of_normal
    (J : HermitianForm 3 F) (g : J.specialSubgroup) (s : ℕ) (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (d : Fˣ)
    (hd : J.conj (d : F) * (d : F) = 1)
    (A : GL (Fin 3) F) (hAg : Commute A g.val)
    (hAn : Commute A (adjoint J A)) (hAd : GeneralLinearGroup.det A = d) :
    ∃ C : J.unitarySubgroup, Commute C.val g.val ∧ GeneralLinearGroup.det C.val = d := by
  exact exists_unitary_commuting_det_of_normal J
    ⟨g.val, J.specialSubgroup_le_unitarySubgroup g.property⟩ s (by omega)
    hcard d hd A hAg hAn hAd

/-- The full unitary centralizer of an odd-order binary SU₃ element realizes
every norm-one determinant, for any nondegenerate Hermitian form. -/
public theorem exists_unitary_centralizer_det [Algebra (ZMod 2) F]
    (J : HermitianForm 3 F) (s : ℕ) (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (g : J.specialSubgroup) (hg : ¬ 2 ∣ orderOf g)
    (d : Fˣ) (hd : J.conj (d : F) * (d : F) = 1) :
    ∃ C : J.unitarySubgroup, Commute C.val g.val ∧ GeneralLinearGroup.det C.val = d := by
  classical
  by_cases hirr : Irreducible g.val.val.charpoly
  · exact exists_unitary_centralizer_det_of_irreducible J g hirr s hs hcard d hd
  · exact ReducibleNormal.exists_unitary_commuting_det J s hs hcard hconj g hg hirr d hd

end Theory.SpecificGroups.SU3.BinaryPRegularClasses
