module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.ActorKernel
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Catalogue
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.GlobalPrimes
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateStructure
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.ThreeStructure
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.GroupTheory.CComponent.RadicalFreeProduct
public import Theory.GroupTheory.PrimeRankZero

/-!
# The two-factor structure before Suzuki uniqueness

The candidate excludes the three-core, and source13.6.26 excludes every
larger prime core. Hence F(H/O₂(H))=1. Every component other than the
candidate is Suzuki by the three-rank bound and the actual A.3.6 catalogue.
Three distinct factors would each contribute a five-element, contradicting
five-rank at most two. The two surviving images therefore fill F*.

Source: Aschbacher–Smith13.6.26–27, printed pp.934–935. No uniqueness
assumption or5.2.3 classification is used.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.ActorKernel
universe u
variable {H : Type u} [Group H] [Finite H]
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Source prime-core exclusions give trivial Fitting before uniqueness. -/
theorem fitting_bot_of_candidate {S K : Subgroup H}
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hK : K.IsCComponent)
    (hc : Candidate S K)
    (hlarge : ∀ p : ℕ, p.Prime → 3 < p → pCore p (H ⧸ pCore 2 H) = ⊥) :
    fittingSubgroup (H ⧸ pCore 2 H) = ⊥ := by
  let := hc.quotient_isQuasisimple hK
  exact fitting_twoCore_quotient_eq_bot
    (hK.threeCore_twoCore_quotient_eq_bot (ThreeStructure.candidate_center_eq_bot hK hc)
      (ThreeStructure.candidate_three_rank_ge_two hc)
      (hH.stronglyQuasithin 3 (by decide) (by decide))) hlarge

/-- A centerless quotient carrying the full three-rank leaves only Suzuki
quotients for the other components. -/
theorem other_suzuki_of_centerless_threeRank {K D : Subgroup H}
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hz : center (K ⧸ pCore 2 K) = ⊥) (hr : 2 ≤ primeRank 3 (K ⧸ pCore 2 K))
    (hD : D.IsCComponent) (hne : D ≠ K) :
    ∃ m : ℕ, 1 ≤ m ∧
      Nonempty ((D ⧸ pCore 2 D) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  have hQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    refine ⟨?_, hH.isKGroup.quotient (pCore 2 H)⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hH.stronglyQuasithin p hp ho)
  exact Catalogue.component_suzuki_quotient
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)) hQ hD
    (hK.other_coprime_three_of_rank hz hr
      (hH.stronglyQuasithin 3 (by decide) (by decide)) hD hne)

/-- Every other original component has its genuine Suzuki quotient. -/
theorem other_suzuki {S K D : Subgroup H}
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hK : K.IsCComponent)
    (hc : Candidate S K) (hD : D.IsCComponent) (hne : D ≠ K) :
    ∃ m : ℕ, 1 ≤ m ∧
      Nonempty ((D ⧸ pCore 2 D) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  let := hc.quotient_isQuasisimple hK
  exact other_suzuki_of_centerless_threeRank hH hK
    (ThreeStructure.candidate_center_eq_bot hK hc)
    (ThreeStructure.candidate_three_rank_ge_two hc) hD hne

/-- The literal image marking in H/O₂(H), with no lift of the actor. -/
noncomputable def suzukiImageEquiv {D : Subgroup H} (hD : D.IsCComponent)
    {m : ℕ} (e : (D ⧸ pCore 2 D) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    D.map (QuotientGroup.mk' (pCore 2 H)) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m :=
  (cComponentTwoCoreQuotientEquiv hD).symm.trans e

private theorem suzuki_five_dvd (m : ℕ) (hm : 0 < m) :
    5 ∣ Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  rw [BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card m hm]
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_left
  rw [Nat.dvd_iff_mod_eq_zero]
  have he : (2 ^ (2 * m + 1)) ^ 2 = 4 * 16 ^ m := by
    rw [← pow_mul]
    have h : (2 * m + 1) * 2 = 2 + 4 * m := by omega
    rw [h, pow_add, pow_mul]
    norm_num
  rw [he, Nat.add_mod, Nat.mul_mod]
  have h16 : 16 ^ m % 5 = 1 := by
    change Nat.ModEq 5 (16 ^ m) 1
    simpa using (show Nat.ModEq 5 16 1 by decide).pow m
  rw [h16]

private theorem three_factors_rank {G : Type*} [Group G] [Finite G]
    (hR : solvableRadical G = ⊥) {K D E : Subgroup G}
    (hK : K.IsCComponent) (hD : D.IsCComponent) (hE : E.IsCComponent)
    (hKD : K ≠ D) (hKE : K ≠ E) (hDE : D ≠ E)
    (hk : 5 ∣ Nat.card K) (hd : 5 ∣ Nat.card D) (he : 5 ∣ Nat.card E) :
    3 ≤ primeRank 5 G := by
  have hkd := hK.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hR hD hKD
  have hke := hK.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hR hE hKE
  have hde := hD.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hR hE hDE
  have hc : K ⊔ D ≤ centralizer (E : Set G) :=
    sup_le (commutator_eq_bot_iff_le_centralizer.mp hke)
      (commutator_eq_bot_iff_le_centralizer.mp hde)
  have hpair := primeRank_sup_eq_add_of_disjoint_commuting K D
    (hK.disjoint_of_commutator_eq_bot_of_solvableRadical_eq_bot hR hkd)
    (commutator_eq_bot_iff_le_centralizer.mp hkd) 5
  have hadd := ResidualCentralizerRank.primeRank_add_le_of_center_coprime (K ⊔ D) E hc
    (show Nat.Coprime 5 (Nat.card (center E)) by
      rw [center_eq_bot_of_isSubnormal_of_solvableRadical_eq_bot hR hE.subnormal]
      simp)
  have hk' : primeRank 5 K ≠ 0 := fun h => PrimeRank.eq_zero_iff_not_dvd_card.mp h hk
  have hd' : primeRank 5 D ≠ 0 := fun h => PrimeRank.eq_zero_iff_not_dvd_card.mp h hd
  have he' : primeRank 5 E ≠ 0 := fun h => PrimeRank.eq_zero_iff_not_dvd_card.mp h he
  omega

/-- The rank and prime-divisor argument applies to any centerless
quasisimple quotient, including the original Janko-four row. -/
theorem generalizedFitting_eq_pair_of_centerless_threeRank {K D : Subgroup H}
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hz : center (K ⧸ pCore 2 K) = ⊥) (hthree : 2 ≤ primeRank 3 (K ⧸ pCore 2 K))
    (hfive : 5 ∣ Nat.card (K ⧸ pCore 2 K))
    (hD : D.IsCComponent) (hne : D ≠ K)
    (hlarge : ∀ p : ℕ, p.Prime → 3 < p → pCore p (H ⧸ pCore 2 H) = ⊥) :
    generalizedFitting (H ⧸ pCore 2 H) =
      K.map (QuotientGroup.mk' (pCore 2 H)) ⊔
        D.map (QuotientGroup.mk' (pCore 2 H)) := by
  let := pCore_isNilpotent (p := 2) (G := H)
  let q := QuotientGroup.mk' (pCore 2 H)
  let Kb := K.map q
  let Db := D.map q
  have hf := fitting_twoCore_quotient_eq_bot
    (hK.threeCore_twoCore_quotient_eq_bot hz hthree
      (hH.stronglyQuasithin 3 (by decide) (by decide))) hlarge
  have hR := radical_bot_of_fitting_bot hf
  have hKb : Kb.IsCComponent := hK.map_quotient _
  have hDb : Db.IsCComponent := hD.map_quotient _
  have hKD : Kb ≠ Db := fun he => hne (hD.eq_of_map_quotient_eq hK _ he.symm)
  have hk5 : 5 ∣ Nat.card Kb := by
    rw [← Nat.card_congr (cComponentTwoCoreQuotientEquiv hK).toEquiv]
    exact hfive
  have other_five (E : Subgroup H) (hE : E.IsCComponent) (hne : E ≠ K) :
      5 ∣ Nat.card (E.map q) := by
    obtain ⟨m, hm, ⟨e⟩⟩ := other_suzuki_of_centerless_threeRank hH hK hz hthree hE hne
    rw [Nat.card_congr (suzukiImageEquiv hE e).toEquiv]
    exact suzuki_five_dvd m (by omega)
  have hr : primeRank 5 (H ⧸ pCore 2 H) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 5 (by decide) _ pCore_isPGroup).trans
      (hH.stronglyQuasithin 5 (by decide) (by decide))
  rw [generalizedFitting, hf, bot_sup_eq,
    ← cComponentLayer_eq_componentLayer_of_solvableRadical_eq_bot hR]
  apply le_antisymm ?_ (sup_le (le_cComponentLayer hKb) (le_cComponentLayer hDb))
  apply sSup_le
  intro B hB
  by_cases hBK : B = Kb
  · exact hBK ▸ le_sup_left
  by_cases hBD : B = Db
  · exact hBD ▸ le_sup_right
  obtain ⟨E, hE, hEB⟩ := hB.exists_map_quotient_eq (pCore 2 H)
  have hEK : E ≠ K := fun he => hBK (hEB.symm.trans (congrArg (map q) he))
  have hb5 : 5 ∣ Nat.card B := hEB ▸ other_five E hE hEK
  have hthree := three_factors_rank hR hKb hDb hB hKD (Ne.symm hBK) (Ne.symm hBD)
    hk5 (other_five D hD hne) hb5
  omega

/-- If an extra component exists, the two actual quotient images are the
entire generalized Fitting subgroup. Uniqueness is not an input. -/
theorem generalizedFitting_eq_pair {S K D : Subgroup H}
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hK : K.IsCComponent)
    (hc : Candidate S K) (hD : D.IsCComponent) (hne : D ≠ K)
    (hlarge : ∀ p : ℕ, p.Prime → 3 < p → pCore p (H ⧸ pCore 2 H) = ⊥) :
    generalizedFitting (H ⧸ pCore 2 H) =
      K.map (QuotientGroup.mk' (pCore 2 H)) ⊔
        D.map (QuotientGroup.mk' (pCore 2 H)) := by
  let := hc.quotient_isQuasisimple hK
  exact generalizedFitting_eq_pair_of_centerless_threeRank hH hK
    (ThreeStructure.candidate_center_eq_bot hK hc)
    (ThreeStructure.candidate_three_rank_ge_two hc)
    ((by decide : 5 ∣ 35).trans (candidate_thirtyFive_dvd hc)) hD hne hlarge

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.ActorKernel
