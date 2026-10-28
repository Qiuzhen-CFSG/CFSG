module

public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.TwoLocalConjugateCover
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFormTransport
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.PointParabolic
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.PlaneParabolic
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.TwoLocalCover

/-!
# Local conditions for the PSU₄ even-characteristic converse

The actual PSU₄ carrier for an arbitrary allowed Hermitian form is
isomorphic to the antidiagonal SU₄ model on the same field. The radical of
the fixed space of a nonidentity two-subgroup, followed by unitary basis
transport and determinant correction, puts its normalizer in a conjugate
of a full point or plane parabolic. The proved odd-prime rank bounds on
these parabolics therefore give QT. Both parabolics are themselves two-local,
so maximality identifies every maximal two-local with one of their conjugates.
Their intrinsic two-core centralizer bounds then give condition E.

The unconditional projective results below discharge every premise of the
retained conditional reductions. They apply to arbitrary Hermitian forms
with the prescribed Frobenius involution, including the field of four
elements, without simplicity or local-classification assumptions.

Source: Aschbacher–Smith, Theorem 0.1.2(1), printed p.4, restated as
Theorem 0.1.1(1), printed p.482, `refs/quasithin.pdf`; the classical fixed-space
argument is GLS III, printed p.115, `refs/KGroup/GLS3/chapter3.tex`.
-/

namespace CFSG.Quasithin.MainConverse.UnitaryFour

open BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFormTransport UnitaryFourConverse

variable {F : Type*} [Field F]

/-- The two full geometric parabolics of the existing antidiagonal SU₄ model:
`false` is the point stabilizer and `true` is the plane stabilizer. -/
@[expose] public def standardParabolic (J : HermitianForm 4 F) (plane : Bool) :
    Subgroup (standardForm J).specialSubgroup :=
  if plane then UnitaryFourFlag.planeParabolicSU F (standardForm J)
  else UnitaryFourFlag.pointParabolicSU F (standardForm J)

variable [Finite F] (J : HermitianForm 4 F)
  [Finite (ProjectiveSpecialUnitaryMatrixGroup J)]

/-- Conditional QT reduction to the two full parabolics, including the
proved transport from an arbitrary source Hermitian form. -/
public theorem quasithin_of_parabolic_cover
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hcover : ∀ M : Subgroup (standardForm J).specialSubgroup, IsTwoLocal M →
      ∃ b g, M ≤ (standardParabolic J b).map (MulAut.conj g).toMonoidHom)
    (hbound : ∀ b p, p.Prime → Odd p → primeRank p (standardParabolic J b) ≤ 2) :
    IsQuasithin (ProjectiveSpecialUnitaryMatrixGroup J) := by
  obtain ⟨e⟩ := nonempty_projectiveEquiv_standardSU J n hn hcard hconj
  apply Theory.GroupTheory.isQuasithin_of_equiv e.symm
  apply CFSG.Quasithin.isQuasithin_iff_twoLocal.mpr
  intro M hM p hp ho
  exact Theory.GroupTheory.primeRank_le_of_twoLocal_conjugate_cover
    (standardParabolic J) p 2 (fun b => hbound b p hp ho) hcover M hM

/-- Conditional E reduction. The two-core is intrinsic to each full
parabolic; the cover is used with maximality among actual two-locals. -/
public theorem evenCharacteristic_of_parabolic_cover
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hcover : ∀ M : Subgroup (standardForm J).specialSubgroup, IsTwoLocal M →
      ∃ b g, M ≤ (standardParabolic J b).map (MulAut.conj g).toMonoidHom)
    (hlocal : ∀ b, IsTwoLocal (standardParabolic J b))
    (hcore : ∀ b, Subgroup.centralizer
      (pCore 2 (standardParabolic J b) : Set (standardParabolic J b)) ≤
        pCore 2 (standardParabolic J b)) :
    IsEvenCharacteristic (ProjectiveSpecialUnitaryMatrixGroup J) := by
  obtain ⟨e⟩ := nonempty_projectiveEquiv_standardSU J n hn hcard hconj
  apply IsEvenCharacteristic.of_equiv e.symm
  intro T M hM _
  exact Theory.GroupTheory.centralizer_pCore_le_of_twoLocal_conjugate_cover
    (standardParabolic J) hlocal hcore hcover M hM

omit [Finite (ProjectiveSpecialUnitaryMatrixGroup J)] in
private theorem standardParabolic_cover
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (M : Subgroup (standardForm J).specialSubgroup) (hM : IsTwoLocal M) :
    ∃ b g, M ≤ (standardParabolic J b).map (MulAut.conj g).toMonoidHom := by
  let : CharP F 2 := charP_two n hn hcard
  obtain ⟨g, hpoint | hplane⟩ := TwoLocalCover.twoLocal_parabolic_cover
    J.conj J.conj_involutive n hn hcard hconj M hM
  · exact ⟨false, g, hpoint⟩
  · exact ⟨true, g, hplane⟩

/-- Every source PSU₄(2ⁿ) carrier is quasithin, including `n = 1`.
The full parabolic ranks and geometric cover have no remaining premises. -/
public theorem projective_quasithin
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    IsQuasithin (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : CharP F 2 := charP_two n hn hcard
  apply quasithin_of_parabolic_cover J n hn hcard hconj
    (standardParabolic_cover J n hn hcard hconj)
  intro b p hp ho
  cases b with
  | false => exact PointParabolic.primeRank_le_two F J.conj J.conj_involutive hp ho
  | true => exact PlaneParabolic.odd_primeRank_le_two F J.conj J.conj_involutive p hp ho

/-- The source QT clause for every two-local of the actual projective carrier,
with no assumption that it contains an ambient Sylow subgroup. -/
public theorem projective_twoLocal_rank
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hM : IsTwoLocal M)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) : primeRank p M ≤ 2 :=
  CFSG.Quasithin.isQuasithin_iff_twoLocal.mp
    (projective_quasithin J n hn hcard hconj) M hM p hp ho

/-- Every source PSU₄(2ⁿ) carrier has even characteristic, including `n = 1`.
Both full parabolics are genuine two-locals with self-centralizing two-core. -/
public theorem projective_evenCharacteristic
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    IsEvenCharacteristic (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : CharP F 2 := charP_two n hn hcard
  apply evenCharacteristic_of_parabolic_cover J n hn hcard hconj
    (standardParabolic_cover J n hn hcard hconj)
  · intro b
    cases b with
    | false => exact PointParabolic.isTwoLocal F J.conj J.conj_involutive
    | true => exact PlaneParabolic.isTwoLocal F J.conj J.conj_involutive
  · intro b
    cases b with
    | false => exact PointParabolic.centralizer_twoCore_le F J.conj J.conj_involutive
    | true => exact PlaneParabolic.centralizer_twoCore_le F J.conj J.conj_involutive

/-- The source E clause: the intrinsic two-core is self-centralizing in every
maximal two-local containing the specified ambient Sylow two-subgroup. -/
public theorem projective_maximalTwoLocal_core
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hM : IsMaximalTwoLocal M)
    (hTM : (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ M) :
    Subgroup.centralizer (pCore 2 M : Set M) ≤ pCore 2 M :=
  projective_evenCharacteristic J n hn hcard hconj T M hM hTM

end CFSG.Quasithin.MainConverse.UnitaryFour
