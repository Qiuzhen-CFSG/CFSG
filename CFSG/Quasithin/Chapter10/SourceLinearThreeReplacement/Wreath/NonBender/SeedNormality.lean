module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.NonBender.Closure
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Preparation
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Seed.Residual

/-!
# Deriving the required normality from the parabolic seed

The recognized parabolic has a two-group kernel and S₃-wreath quotient,
so all its prime divisors are two or three. The original C_{L₀}(z) is a
subgroup of that same parabolic. The proved prime-to-three residual
comparison consequently supplies normality of X in every relevant normal
intermediate subgroup. This removes the separate SeedAnalysis premise
from the strict-closure branch; no reduced-module conclusion is used.

Source: Aschbacher--Smith 10.1.3, 10.2.4 and 10.3.3, pp.742,747,756.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender
open Chapter3.Section02 Overgroups.Closure
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D}

private theorem parabolicWreath_twoThree : IsPiGroup twoThreePrimes ParabolicWreath := by
  have hc : Nat.card ParabolicWreath = 72 := by
    change Nat.card (RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) = 72
    rw [RegularWreathProduct.card]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  rw [IsPiGroup_iff, hc]
  intro q hq
  have hd : q.val ∣ 2 ^ 3 * 3 ^ 2 := by norm_num; exact hq
  rcases q.property.dvd_mul.mp hd with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq q.property Nat.prime_two).mp
      (q.property.dvd_of_dvd_pow h))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq q.property Nat.prime_three).mp
      (q.property.dvd_of_dvd_pow h))

/-- The actual diagonal centralizer inherits its prime spectrum from the
recognized parabolic and its literal two-core quotient. -/
theorem diagonal_twoThree_of_parabolicSeed (d : CentralizerData T D s)
    (r : ParabolicSeedData T L (d.first * d.second)) :
    IsPiGroup twoThreePrimes
      (localOrbit T L ⊓ centralizer ({d.first * d.second} : Set G) : Subgroup G) := by
  have hP : IsPiGroup twoThreePrimes r.parabolic := by
    apply IsPiGroup.of_normal_subgroup_and_quotient (pCore 2 r.parabolic)
    · apply IsPiGroup.isPiSubgroup
      rw [IsPiGroup_iff]
      obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := r.parabolic)).exists_card_eq
      intro q hq
      rw [hn] at hq
      exact Or.inl ((Nat.prime_dvd_prime_iff_eq q.property Nat.prime_two).mp
        (q.property.dvd_of_dvd_pow hq))
    · obtain ⟨e⟩ := r.wreath
      exact parabolicWreath_twoThree.of_equiv e
  have hKP : localOrbit T L ⊓ centralizer ({d.first * d.second} : Set G) ≤
      r.parabolic := by
    rw [← r.seed_join_eq, Parabolic.seed_join_eq_diagonalParabolic d.central]
    exact inf_le_inf_right _ le_sup_left
  exact hP.of_injective (inclusion hKP) (inclusion_injective hKP)

/-- The original seed data suffices to show that every strict closure
escapes M; the independent full SeedAnalysis contract is unnecessary. -/
theorem span_escapes_of_parabolicSeed (d : CentralizerData T D s)
    (r : ParabolicSeedData T L (d.first * d.second))
    (hstrict : centralizerSeed T L (d.first * d.second) <
      componentSpan T L (d.first * d.second)) :
    ¬ componentSpan T L (d.first * d.second) ≤ D.maximalLocal := by
  intro hKM
  have hn := Geometry.CoreReduced.Seed.normal_in_kernel_of_twoThree s
    (diagonal_twoThree_of_parabolicSeed d r) (componentSpan T L (d.first * d.second))
    (le_inf (componentSpan_le_centralizer _) hKM)
    (le_normalizer_conjugateSpanBy _ _) (le_conjugateSpanBy _ _)
  exact hstrict.not_ge (conjugateSpanBy_le le_rfl hn)

/-- The exact strict-closure contract from the two existing parabolic and
wreath-sieve producers, with no geometry premise. -/
theorem strictClosure_of_seed_and_sieve (hseed : ParabolicSeedAt T)
    (hsieve : InvariantWreathSieveAt T) : StrictClosureAt T := by
  intro hmany L D s d hstrict
  obtain ⟨r⟩ := hseed hmany L D s d
  have hXC : centralizerSeed T L (d.first * d.second) ⊔ (T : Subgroup G) ≤
      centralizer ({d.first * d.second} : Set G) :=
    sup_le ((map_subtype_le _).trans inf_le_right) d.sylow_le_centralizer
  obtain ⟨P, hP⟩ := r.localInput hXC
  rcases normalClosure_models_of_sieve hsieve hP
      (D.simpleQTKE.involution_centralizer_sqtk d.order) r.seed_wreath with
    he | ⟨I, hI, hqs, horbit, hm⟩
  · exact (hstrict.ne he.symm).elim
  · have hout : ¬ I ≤ D.maximalLocal := by
      intro hIM
      apply span_escapes_of_parabolicSeed d r hstrict
      rw [componentSpan, horbit]
      exact iSup_conjugates_le_of_le_normalizer I (T : Subgroup G) D.maximalLocal hIM
        ((le_normalizer_componentOrbit L (T : Subgroup G)).trans D.maximalLocal.le_normalizer)
    exact ⟨I, hI, hout, hqs, horbit.symm, hm⟩

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender
