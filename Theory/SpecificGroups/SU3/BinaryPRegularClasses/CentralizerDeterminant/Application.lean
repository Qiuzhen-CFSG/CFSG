module

public import Theory.SpecificGroups.SU3.BinaryPRegularClasses.CentralizerDeterminant
public import Theory.SpecificGroups.SU3.BinaryPRegularClasses

/-!
# SU₃ conjugacy from a unitary intertwiner

Unitary centralizer determinant surjectivity supplies the determinant premise of
`isConj_of_unitary_intertwiner_of_centralizer_determinants`. Thus the conjugator
lies in the full special unitary group, including its cubic center. The given
unitary intertwiner is an independent input; constructing it is not needed
for this conditional application. For odd-order elements, no centralizer
witness or determinant-surjectivity premise remains.

This discharges the determinant correction in the class argument associated
with GLS III 2.8.2, 2.8.6(a), and 2.8.10(c),
`refs/KGroup/GLS3/chapter2.tex`.
-/

namespace Theory.SpecificGroups.SU3.BinaryPRegularClasses
open Matrix BenderSuzuki.MatrixGroups CentralizerDeterminant
variable {F : Type*} [Field F] [Finite F]

/-- Apply the proved adjoint correction to the actual SU₃ conjugacy consumer.
Only normal linear centralizer witnesses and a unitary intertwiner are assumed. -/
public theorem isConj_of_unitary_intertwiner_of_normal_centralizer_witnesses
    (J : HermitianForm 3 F) (g h : J.specialSubgroup) (s : ℕ) (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hnormal : ∀ d : Fˣ, J.conj (d : F) * (d : F) = 1 →
      ∃ A : GL (Fin 3) F, Commute A g.val ∧ Commute A (adjoint J A) ∧
        GeneralLinearGroup.det A = d)
    (U : J.unitarySubgroup) (hU : U.val * g.val = h.val * U.val) : IsConj g h := by
  apply isConj_of_unitary_intertwiner_of_centralizer_determinants J g h ?_ U hU
  intro d hd
  obtain ⟨A, hAg, hAn, hAd⟩ := hnormal d hd
  exact exists_unitary_centralizer_det_of_normal J g s hs hcard d hd A hAg hAn hAd

/-- A unitary intertwiner for an odd-order binary SU₃ element can be corrected
to a conjugator in the full special unitary group. -/
public theorem isConj_of_unitary_intertwiner [Algebra (ZMod 2) F]
    (J : HermitianForm 3 F) (s : ℕ) (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (g h : J.specialSubgroup) (hg : ¬ 2 ∣ orderOf g)
    (U : J.unitarySubgroup) (hU : U.val * g.val = h.val * U.val) : IsConj g h := by
  exact isConj_of_unitary_intertwiner_of_centralizer_determinants J g h
    (exists_unitary_centralizer_det J s hs hcard hconj g hg) U hU

end Theory.SpecificGroups.SU3.BinaryPRegularClasses
