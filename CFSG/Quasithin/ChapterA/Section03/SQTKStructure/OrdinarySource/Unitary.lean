module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.UnitaryOddPartCases
public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.LargePrimary.Complete
public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.ThreePrimary.Complete
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic
/-!
# Unitary ordinary components in A.3.6

The completed odd-primary kernel calculations discharge the unitary
scalar-cover inputs, including PSU₃(8) and every odd-prime parameter.
Every branch supplies the full common Fitting and radical conclusion.

Source: Aschbacher–Smith A.3.6 and I.1.3, printed pp.43–45, 407.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterA.SQTKStructure.OrdinarySource
open Chapter1.Section02 HermitianForm.UniversalCover

/-- The actual PSU₃(2ⁿ) scalar-cover source case, including q=8, with all
large- and three-primary calculations discharged. -/
theorem a36_unitary_even {X : Type*} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L) (hcore : pCore 2 L = ⊥)
    (n : ℕ) (hn : 2 ≤ n) (F : Type) [Field F] [Finite F]
    (J : HermitianForm 3 F)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (e : L ⧸ center L ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    A36Conclusion L :=
  UnitaryOddPartCases.a36_unitary_even L hL hcore n hn F J hcard hconj e
    (fun _ hr hr3 => EvenKernelBound.LargePrimary.not_dvd_universal_kernel
      J hn hr hr3 hcard hconj)
    (fun ho => EvenKernelBound.ThreePrimary.not_nine_dvd_universal_kernel
      J hn ho hcard hconj)

/-- The actual odd-prime unitary source case, with all cross-odd and
three-primary bounds supplied by the original finite-cover calculations. -/
theorem a36_unitary_odd_prime {X : Type*} [Group X] [Finite X]
    (L : Subgroup X) (hL : IsComponent X L) (hcore : pCore 2 L = ⊥)
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (F : Type) [Field F] [Finite F]
    (J : HermitianForm 3 F)
    (hcard : Nat.card F = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p)
    (e : L ⧸ center L ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    A36Conclusion L := by
  have hp2 : 2 < p := by
    have := hp.two_le
    have : p ≠ 2 := by rintro rfl; norm_num at ho
    omega
  let := projective_isQuasisimple J hp2 hcard hconj
  apply UnitaryOddPartCases.a36_unitary_odd_prime L hL hcore p hp ho F J hcard hconj e
  · intro r hr hr2 hr3 hrp
    exact OddKernelBound.OddCrossCharacteristic.not_dvd_kernel J (e := 1)
      hp (by decide) hr hr2 hr3 hrp (by simpa using hcard)
      (by simpa using hconj) (universalCover _)
  · intro hm
    exact OddKernelBound.OddCrossCharacteristic.not_nine_dvd_kernel J
      hcard hconj hm (universalCover _)
end CFSG.Quasithin.ChapterA.SQTKStructure.OrdinarySource
