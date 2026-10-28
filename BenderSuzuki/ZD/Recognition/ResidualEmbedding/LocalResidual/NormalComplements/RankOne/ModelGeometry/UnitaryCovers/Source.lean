module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryCovers
public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.LargePrimary.Complete
public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.ThreePrimary.Complete.Descent
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore

/-!
# Odd central covers of the even unitary groups

An odd-center perfect cover is quasisimple and has trivial two-core. The
proved odd-primary universal-kernel bounds therefore give a lift from the
literal SU₃ scalar cover. Its prime-order scalar kernel leaves precisely
PSU₃ and SU₃, and preserves the specified quotient equivalence.

Source: GLS IV, Chapter 4, Lemma 2.8(a), used in Chapter 2, Lemma 16.3(a)
and the centralizing-extension argument of Lemma 12.3; GLS III, Theorem 6.1.4.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering BenderSuzuki.MatrixGroups

namespace BenderSuzuki.ZD.RankOneModelGeometry

variable {G E : Type*} [Group G] [Finite G] [Field E] [Finite E]

/-- The SU₃ lift uses the original marked central quotient. All odd-primary
kernel bounds and the target's two-core condition are discharged here. -/
theorem exists_unitary_centralCover_lift_of_odd_center
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (hperfect : commutator G = ⊤) (hodd : Odd (Nat.card (center G)))
    (e : (G ⧸ center G) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    ∃ k : J.specialSubgroup →* G, Function.Surjective k ∧
      (e.toMonoidHom.comp (QuotientGroup.mk' (center G))).comp k =
        J.specialToProjective := by
  let : Group.IsPerfect G := ⟨hperfect⟩
  have hconj := External.huppert_II_10_4_conj_eq_frobenius J (2 ^ n) hcard hfixed
  have hq : 2 < 2 ^ n := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide) hn)
  let := HermitianForm.UniversalCover.projective_isQuasisimple J hq hcard hconj
  let : IsQuasisimple G := (centralQuotientCover e).isQuasisimple
  have hcore : pCore 2 G = ⊥ := by
    rcases (pCore_isPGroup (p := 2) (G := G)).card_eq_or_dvd with hcard | htwo
    · exact Subgroup.card_eq_one.mp hcard
    · exact (hodd.not_two_dvd_nat
        (htwo.trans (Subgroup.card_dvd_of_le (IsQuasisimple.pCore_le_center 2)))).elim
  exact HermitianForm.UniversalCover.OddPartDescent.exists_lift_even_of_large_prime_exclusion
    J hn hcard hconj
    (fun r hr hr3 => HermitianForm.UniversalCover.EvenKernelBound.LargePrimary.not_dvd_universal_kernel
      J hn hr hr3 hcard hconj)
    (e.toMonoidHom.comp (QuotientGroup.mk' (center G)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hcore

/-- GLS IV, Chapter 4, Lemma 2.8(a): both actual unitary central-cover
alternatives, with no additional lifting or kernel-bound premise. -/
theorem unitary_centralCover_alternative_of_odd_center
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (hperfect : commutator G = ⊤) (hodd : Odd (Nat.card (center G)))
    (e : (G ⧸ center G) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    Nonempty (G ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
      Nonempty (G ≃* J.specialSubgroup) := by
  obtain ⟨k, _, hk⟩ := exists_unitary_centralCover_lift_of_odd_center
    J hn hcard hfixed hperfect hodd e
  exact unitary_centralCover_alternative_of_lift J hperfect e k hk

/-- The nontrivial-center branch has center of order three and odd exponent;
the centerless branch is the original projective unitary model. -/
theorem unitary_centralCover_cases_of_odd_center
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (hperfect : commutator G = ⊤) (hodd : Odd (Nat.card (center G)))
    (e : (G ⧸ center G) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    (center G = ⊥ ∧ Nonempty (G ≃* ProjectiveSpecialUnitaryMatrixGroup J)) ∨
      (Nat.card (center G) = 3 ∧ Odd n ∧ Nonempty (G ≃* J.specialSubgroup)) := by
  obtain ⟨k, _, hk⟩ := exists_unitary_centralCover_lift_of_odd_center
    J hn hcard hfixed hperfect hodd e
  exact unitary_centralCover_cases_of_lift J hn hcard hfixed hperfect e k hk

end BenderSuzuki.ZD.RankOneModelGeometry
