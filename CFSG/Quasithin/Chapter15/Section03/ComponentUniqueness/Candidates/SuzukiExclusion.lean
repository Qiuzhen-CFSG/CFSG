module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SuzukiExclusion.ActionInterface
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SuzukiExclusion.LocalReduction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SuzukiExclusion.BorelConstruction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SuzukiExclusion.ConcreteAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SuzukiExclusion.ModelThreeDivisibility
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder

/-!
# Suzuki exclusion and positive three-rank: 15.3.34

For L₀ = ⟨L^S⟩, a marked Borel in one or two concrete Suzuki factors has
order prime to three. A calculation of its order-three automorphism kernel
transports through the displayed equivalence and applies to the literal
Y₊-conjugation action. Together with the local deductions of 15.3.33(1),
this rules out the Suzuki component. The Borel is constructed as the relative
normalizer of S ∩ L₀, retaining the possible permutation of two components by S.

The arithmetic conclusion is also established: three-divisibility gives
positive three-rank and excludes every Suzuki central quotient when
Z(L) = O₂(L), including the degenerate parameter Sz(2).

The final assembly supplies the invariant Borel, the concrete action kernel,
and three-divisibility from the full actual 1.1.5 model/action list. Its inputs
are the earlier local conclusions, the chosen ordinary component's conclusions
of 15.3.33(3), and the component-orbit bound of 1.2.1(3). Normalization by Y₊
follows from this bound and Y₊ = θ(M ∩ I); no normalization of L by S is assumed.
The parent component-candidates assembly supplies these earlier source inputs.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.33--34, printed p.1134; the Suzuki models and Borels are those of
F.1.3(1), printed pp.259--260, with q = 2^(2m+1).
-/

public section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SuzukiExclusion

variable {K : Type*} [Group K]

/-- A marked Suzuki orbit has order prime to three. -/
theorem IsSuzukiOrbitBorel.three_free {B : Subgroup K} (hB : IsSuzukiOrbitBorel B) :
    ¬ 3 ∣ Nat.card K := by
  obtain ⟨m, n, hm, _, e, _⟩ := hB
  rw [Nat.card_congr e.toEquiv, Nat.card_fun]
  intro hd
  exact suzukiMatrixGroup_three_free m hm (Nat.prime_three.dvd_of_dvd_pow hd)

/-- The concrete action calculation transfers through the marked Borel equivalence. -/
theorem IsSuzukiOrbitBorel.detects
    (hact : ∀ m n : ℕ, 0 < m → (n = 1 ∨ n = 2) →
      DetectsThreeAutomorphisms (Subgroup.pi Set.univ
        (fun _ : Fin n => SuzukiBorelSubgroup m)))
    {B : Subgroup K} (hB : IsSuzukiOrbitBorel B) : DetectsThreeAutomorphisms B := by
  obtain ⟨m, n, hm, hn, e, he⟩ := hB
  exact (hact m n hm hn).of_mulEquiv e he

variable {G : Type*} [Group G] [Finite G]

/-- Conditional local assembly, with the detector tied to concrete Suzuki matrix Borels.
Existence of the invariant marked Borel and the concrete action calculation
remain obligations; this is not the numbered source lemma. -/
theorem false_of_suzuki_borel_model
    (hact : ∀ m n : ℕ, 0 < m → (n = 1 ∨ n = 2) →
      DetectsThreeAutomorphisms (Subgroup.pi Set.univ
        (fun _ : Fin n => SuzukiBorelSubgroup m)))
    {Yplus S M I L B : Subgroup G}
    (hI : I ∈ outsideFamily Yplus S M)
    (hSylow : OutsideSylowControl Yplus S M)
    (h25 : ∀ J ∈ outsideFamily Yplus S M, generalizedFitting J ≠ pCore 2 J)
    (hodd : ∀ J ∈ outsideFamily Yplus S M, pPrimeCore 2 J = ⊥)
    (hSM : S ≤ M) (hMI : I ⊓ normalizer (Yplus : Set G) = M ⊓ I)
    (hY : IsPGroup 3 (Yplus ⧸ pCore 2 Yplus))
    (htheta : Yplus = theta (M ⊓ I))
    (hLI : L ≤ I) (hLM : ¬ L ≤ M)
    (hL0N : Yplus ≤ normalizer (localSpan L S : Set G))
    (hBL : B ≤ localSpan L S)
    (hBN : Yplus ⊔ S ≤ normalizer (B : Set G))
    (hBF : generalizedFitting B = pCore 2 B)
    (hmax : ∀ D : Subgroup G, B ≤ D → D ≤ localSpan L S →
      S ≤ normalizer (D : Set G) → D = B ∨ D = localSpan L S)
    (hmodel : IsSuzukiOrbitBorel (B.subgroupOf (localSpan L S))) : False := by
  have hthree : ¬ 3 ∣ Nat.card B := fun hd =>
    hmodel.three_free (hd.trans (card_dvd_of_le hBL))
  apply false_of_borel_detection hI hSylow h25 hodd hSM hMI hY htheta hLI hLM
    hBL hBN hBF hmax hthree
  intro y hy hy3 hc
  exact centralizes_of_borel_detector hBL (hmodel.detects hact) (hL0N hy) hy3 hc

/-- With center equal to the two-core, even the degenerate Suzuki quotient
forces order prime to three. -/
theorem three_free_of_suzuki_central_quotient
    (hZ : center G = pCore 2 G) (m : ℕ)
    (e : (G ⧸ center G) ≃* SuzukiMatrixGroup m) : ¬ 3 ∣ Nat.card G := by
  let e' : (G ⧸ pCore 2 G) ≃* SuzukiMatrixGroup m :=
    (QuotientGroup.quotientMulEquivOfEq hZ.symm).trans e
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hq : ¬ 3 ∣ Nat.card (G ⧸ pCore 2 G) := by
      rw [Nat.card_congr e'.toEquiv, suzukiZero_card]
      decide
    intro hd
    rw [← (pCore 2 G).card_mul_index] at hd
    rcases Nat.prime_three.dvd_mul.mp hd with hc | hi
    · obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
      rw [hn] at hc
      exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hc)
    · exact hq ((pCore 2 G).index_eq_card ▸ hi)
  · exact three_free_of_suzuki_core_quotient m hm e'

/-- The final arithmetic step, after three-divisibility has been established
from the remaining actual component models. -/
theorem quotient_exclusion_and_rank_of_three_dvd
    (hZ : center G = pCore 2 G) (hthree : 3 ∣ Nat.card G) :
    (∀ m : ℕ, ¬ Nonempty ((G ⧸ center G) ≃* SuzukiMatrixGroup m)) ∧
      1 ≤ primeRank 3 G := by
  refine ⟨?_, positive_three_rank_of_dvd_card hthree⟩
  rintro m ⟨e⟩
  exact three_free_of_suzuki_central_quotient hZ m e hthree

/-- The Suzuki model is excluded by the constructed Borel and its proved
order-three detector. The index bound is precisely the orbit-size consequence
of 1.2.1(3); all normalization and Borel premises are discharged here. -/
theorem not_suzuki_component_of_local
    {Yplus S M I L : Subgroup G}
    (hI : I ∈ outsideFamily Yplus S M)
    (hSylow : OutsideSylowControl Yplus S M)
    (h25 : ∀ J ∈ outsideFamily Yplus S M, generalizedFitting J ≠ pCore 2 J)
    (hodd : ∀ J ∈ outsideFamily Yplus S M, pPrimeCore 2 J = ⊥)
    (hSM : S ≤ M) (hMI : I ⊓ normalizer (Yplus : Set G) = M ⊓ I)
    (hY : IsPGroup 3 (Yplus ⧸ pCore 2 Yplus))
    (htheta : Yplus = theta (M ⊓ I))
    (hLI : L ≤ I) (hLM : ¬ L ≤ M)
    (hL : IsComponent I (L.subgroupOf I))
    (hindex : (normalizer (L : Set G)).relIndex I ≤ 2)
    (m : ℕ) (hm : 0 < m) : ¬ Nonempty (L ≃* SuzukiMatrixGroup m) := by
  rintro ⟨e⟩
  obtain ⟨P, hP⟩ := hSylow I hI
  have hSY : S ≤ normalizer (Yplus : Set G) :=
    (le_inf hSM (le_sup_right.trans hI.1.2)).trans
      (hMI.symm.le.trans inf_le_right)
  have hYL := ComponentIntersection.normalizes_of_index_le_two
    (le_sup_left.trans hI.1.2)
    (htheta.symm ▸ ComponentIntersection.theta_isPPerfect (M ⊓ I)) hindex
  have hindex' : (normalizer (L.subgroupOf I : Set I)).index ≤ 2 := by
    rwa [← subgroupOf_normalizer_eq hLI]
  obtain ⟨hL0N, B, hBL, hBN, hBF, hmodel, hmax⟩ :=
    exists_invariant_suzuki_orbit_borel hLI hI.1.2 P hP hL m hm e hSY hY hYL hindex'
  exact false_of_suzuki_borel_model suzukiBorel_pi_detectsThreeAutomorphisms
    hI hSylow h25 hodd hSM hMI hY htheta hLI hLM hL0N hBL hBN hBF hmax hmodel

/-- Source 15.3.34 for the chosen ordinary component, from the earlier local
conclusions and its actual 15.3.33(3) model/action alternatives. The orbit bound
is the earlier 1.2.1(3) input. The conclusion excludes every Suzuki central
quotient, including Sz(2), and establishes the positive three-rank consumed
by 15.3.37. No Borel, automorphism detector, or divisibility premise remains. -/
theorem lemma_15_3_34
    {Yplus S M I L : Subgroup G} {z : G}
    (hI : I ∈ outsideFamily Yplus S M)
    (hSylow : OutsideSylowControl Yplus S M)
    (h25 : ∀ J ∈ outsideFamily Yplus S M, generalizedFitting J ≠ pCore 2 J)
    (hodd : ∀ J ∈ outsideFamily Yplus S M, pPrimeCore 2 J = ⊥)
    (hSM : S ≤ M) (hMI : I ⊓ normalizer (Yplus : Set G) = M ⊓ I)
    (hY : IsPGroup 3 (Yplus ⧸ pCore 2 Yplus))
    (htheta : Yplus = theta (M ⊓ I))
    (hLI : L ≤ I) (hL : IsComponent I (L.subgroupOf I))
    (h33 : ComponentStructure.Conclusions (L.subgroupOf I) M z)
    (hindex : (normalizer (L : Set G)).relIndex I ≤ 2) :
    (∀ m : ℕ, ¬ Nonempty ((L ⧸ center L) ≃* SuzukiMatrixGroup m)) ∧
      1 ≤ primeRank 3 L := by
  have hLM : ¬ L ≤ M := by
    simpa only [map_subgroupOf_eq_of_le hLI] using h33.outside
  let eL := subgroupOfEquivOfLe hLI
  obtain ⟨α, _, hmodel⟩ := h33.model_action
  have hthree : 3 ∣ Nat.card L := by
    rcases ModelThreeDivisibility.suzuki_or_three_dvd α hmodel with
      ⟨m, hm, ⟨e⟩⟩ | hd
    · exact (not_suzuki_component_of_local hI hSylow h25 hodd hSM hMI hY htheta
        hLI hLM hL hindex m hm ⟨eL.symm.trans e⟩).elim
    · rwa [Nat.card_congr eL.toEquiv] at hd
  have hc : (center (L.subgroupOf I)).map eL.toMonoidHom = center L := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.centerCongr eL ⟨x, hx⟩).property
    · intro x hx
      exact ⟨eL.symm x, ((Subgroup.centerCongr eL).symm ⟨x, hx⟩).property,
        eL.apply_symm_apply x⟩
  have hZ : center L = pCore 2 L := by
    rw [← hc, component_center_eq_twoCore hL (hodd I hI), pCore_map_iso]
  exact quotient_exclusion_and_rank_of_three_dvd hZ hthree
end CFSG.Quasithin.Chapter15.Section03.Candidates.SuzukiExclusion
