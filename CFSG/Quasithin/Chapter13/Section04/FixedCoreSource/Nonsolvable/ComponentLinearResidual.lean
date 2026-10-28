module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentLinearModule
public import Theory.Representation.PSL3Two.NaturalPointCentralizer

/-!
# Reciprocal residuals for the ordinary-original linear-three row

The constructed natural module gives the fixed-line generator an actual
S₄ point-centralizer quotient. Its cubic lies in K ∩ N_G(L); the original
ordinary-A₆ residual theorem therefore gives L₁≤K. Normal restriction
identifies the reciprocal O^{3′} residuals. The point centralizer is a
{2,3}-group, and the full central four-group has the same centralizer in K,
so the literal O² residuals agree as well.

The original five-dimensional augmentation and every ambient inclusion
are preserved. The covered-original linear-three row, selected covered-A₆
row, full reduced-module equality, and comparison/commutator/graph assembly
remain with qt-d-1341-nonsolvable-source. LargeDistanceInput and the earlier
12.2/13.3 inputs retain the producers documented in ComponentLinearModule;
final discharge remains with qt-d-1341-fixed-core-source. Nonsolvability at
both escaping weights remains required.
Source: Aschbacher–Smith 13.4.10(2–5), printed pp.908–909.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Subgroup Theory.GroupTheory Stellmacher Representation
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

private theorem linear_point_twoThree
    {A : Type*} [Group A] [Finite A]
    (f : A →* Equiv.Perm (Fin 4)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) : IsPiGroup twoThreePrimes A := by
  obtain ⟨n,hn⟩ := hk.exists_card_eq
  have hc : Nat.card A = 24 * 2 ^ n := by
    rw [card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,
      Nat.card_perm,Nat.card_fin,hn]
    norm_num [Nat.factorial]
  rw [IsPiGroup_iff]
  intro p hp
  rw [hc] at hp
  change p.val = 2 ∨ p.val = 3
  have he : 24 * 2 ^ n = 2 ^ (n+3) * 3 := by ring
  rw [he] at hp
  rcases p.property.dvd_mul.mp hp with h2 | h3
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
      (p.property.dvd_of_dvd_pow h2) |>.resolve_left p.property.ne_one)
  · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp h3 |>.resolve_left p.property.ne_one)

/-- In the original ordinary-A₆ branch, the now constructed natural
linear-three module supplies L₁ containment and both reciprocal residual
identities. No selected-module or point-centralizer witness is assumed. -/
theorem ordinary_linear_component_residuals
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    Solvable.firstCentralizerResidual L z.val ≤ K ∧
      Solvable.firstCentralizerResidual K m.constant.val =
        Solvable.firstCentralizerResidual L z.val ∧
      (pResidual 2 (K ⊓ centralizer
          (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Subgroup G)).map
          (K ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)).subtype =
        (pResidual 2 (L ⊓ centralizer ({z.val} : Set G) : Subgroup G)).map
          (L ⊓ centralizer ({z.val} : Set G)).subtype := by
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  have hTK := (h1332 K hfK).1
  obtain ⟨DK,q,e,he,_,_,_,hcard⟩ := linear_component_marking hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK
  obtain ⟨w,hw,hC⟩ := component_fixed_generator_point h₀ h structural m hzT hz1 hKz hTK hKM
  obtain ⟨f,hf,hker⟩ := BinaryLinearThree.natural_point_centralizer K _ DK.normalizes q e he w hw
  have hd := card_dvd_of_surjective f hf
  rw [Nat.card_perm,Nat.card_fin] at hd
  have hthree : 3 ∣ Nat.card (K ⊓ normalizer (L : Set G) : Subgroup G) := by
    rw [←fixed_generator_centralizer h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun hh => m.constant_ne_one (Subtype.ext hh)),hC]
    exact (by decide : 3 ∣ Nat.factorial 4).trans hd
  have hLK := ordinary_firstResidual_le_of_reciprocal_cubic h structural D m eL z hzL hKz hHN hthree
  have hrec := component_reciprocal_residual_of_containment h structural m z.val hKz hHN eL hLK
  have h23 := linear_point_twoThree f hf (by
    rw [hker]
    exact (isPGroup_pCoreIn 2 K).comap_subtype)
  rw [←hC] at h23
  refine ⟨hLK,hrec,?_⟩
  rw [component_four_seed_centralizer h structural D m hzT hz1 hKz hKM hcard,
    twoResidual_eq_primeToResidual_three h23,←Solvable.firstCentralizerResidual_eq,hrec]
  exact (core_component_point_twoResidual D m eL z hzL).symm

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
