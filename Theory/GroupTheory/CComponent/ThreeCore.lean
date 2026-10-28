module

public import Theory.GroupTheory.CComponent.ThreeResidual
public import Theory.GroupTheory.PResidual.PrimeToSubnormal
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.CComponent.UniqueResidual
public import Theory.GroupTheory.PResidual.PrimeToTransport

/-!
# Three-rank exclusions around a C-component

A centerless component containing an elementary nine has centralizer of order
prime to three in a group of three-rank at most two. Component commutator
calculus then kills the three-core and makes every other C-component a
three-prime group. The proofs pass through the literal ambient two-core
quotient, using its equivalence with each intrinsic component quotient.

A two-group outer group identifies the component with O^{3′}. With unique
component and trivial Fitting subgroup modulo O₂, an outer order dividing
twelve makes O^{3′} supplement every Sylow two-subgroup. No component
classification or model-specific outer calculation is assumed implicitly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the centerless
argument in A.3.18, pp.51–52, and the deductions in 13.6.27, pp.934–935.
-/

public section

open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Rank at least two produces an actual elementary abelian subgroup of order nine. -/
theorem exists_elementary_nine_of_three_rank (h : 2 ≤ primeRank 3 G) :
    ∃ E : Subgroup G, IsElementaryAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  let P : Sylow 3 G := Classical.choice inferInstance
  have hn : ¬ IsCyclic P := by
    intro hc
    have hr := P.primeRank_le_one_of_isCyclic hc
    omega
  obtain ⟨E, _, hcard, he⟩ :=
    P.isPGroup'.exists_normal_elementary_prime_sq_of_odd_not_isCyclic (by decide) hn
  let _ := he
  refine ⟨E.map (P : Subgroup G).subtype, IsElementaryAbelian.map_subtype, ?_⟩
  simpa only [card_map_of_injective (P : Subgroup G).subtype_injective] using hcard

/-- A centerless subgroup of full three-rank has three-prime centralizer. -/
theorem centralizer_coprime_three_of_rank (K : Subgroup G)
    (hz : center K = ⊥) (hrK : 2 ≤ primeRank 3 K) (hrG : primeRank 3 G ≤ 2) :
    Nat.Coprime 3 (Nat.card (centralizer (K : Set G))) := by
  obtain ⟨A, hA, hc⟩ := exists_elementary_nine_of_three_rank hrK
  let _ := hA
  let E := A.map K.subtype
  let _ : IsElementaryAbelian 3 E := IsElementaryAbelian.map_subtype
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  apply prime_not_dvd_card_centralizer_of_full_rank K E (map_subtype_le A) _ hrG hz
  simpa only [E, card_map_of_injective K.subtype_injective] using hc

/-- An ordinary centerless component of full three-rank excludes the three-core. -/
theorem threeCore_eq_bot_of_component_rank {K : Subgroup G}
    (hK : IsComponent G K) (hz : center K = ⊥)
    (hrK : 2 ≤ primeRank 3 K) (hrG : primeRank 3 G ≤ 2) : pCore 3 G = ⊥ := by
  have hc := centralizer_coprime_three_of_rank K hz hrK hrG
  have hcomm : ⁅K, pCore 3 G⁆ = ⊥ := by
    rcases hK.normal_dichotomy (pCore 3 G) with hle | hcomm
    · let _ := hK.2
      let _ := IsQuasisimple.simple (G := K)
      let _ : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
      let _ := (pCore_isPGroup (p := 3) (G := G)).isNilpotent
      let _ : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
        (inclusion_injective hle)
      exact (Group.IsPerfect.not_isSolvable K inferInstance).elim
    · exact hcomm
  have hle : pCore 3 G ≤ centralizer (K : Set G) := by
    rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
    exact hcomm
  have hcop := hc.coprime_dvd_right (card_dvd_of_le hle)
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 3) (G := G)).exists_card_eq
  apply (eq_bot_iff_card _).mpr
  rw [hn] at hcop ⊢
  by_cases hn0 : n = 0
  · simp [hn0]
  · have hd : 3 ∣ 3 ^ n := dvd_pow_self 3 hn0
    exact (Nat.prime_three.coprime_iff_not_dvd.mp hcop hd).elim

private theorem center_bot_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center A = ⊥) : center B = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have h : e.symm x ∈ center A := ((centerCongr e).symm ⟨x, hx⟩).property
  have he : e.symm x = 1 := by simpa only [hz, mem_bot] using h
  exact e.symm.map_eq_one_iff.mp he

variable {K : Subgroup G}

/-- The same exclusion in the actual ambient two-core quotient. -/
theorem IsCComponent.threeCore_twoCore_quotient_eq_bot (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)] (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hrK : 2 ≤ primeRank 3 (K ⧸ pCore 2 K)) (hrG : primeRank 3 G ≤ 2) :
    pCore 3 (G ⧸ pCore 2 G) = ⊥ := by
  let _ := pCore_isNilpotent (p := 2) (G := G)
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := K.map q
  let e : (K ⧸ pCore 2 K) ≃* B := cComponentTwoCoreQuotientEquiv hK
  let _ : IsQuasisimple B := IsQuasisimple.of_mulEquiv e
  exact threeCore_eq_bot_of_component_rank
    ⟨(hK.map_quotient _).subnormal, inferInstance⟩ (center_bot_transport e hz)
    ((primeRank_congr 3 e) ▸ hrK)
    ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans hrG)

/-- Every distinct C-component has order prime to three, before uniqueness is known. -/
theorem IsCComponent.other_coprime_three_of_rank (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)] (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hrK : 2 ≤ primeRank 3 (K ⧸ pCore 2 K)) (hrG : primeRank 3 G ≤ 2)
    {D : Subgroup G} (hD : D.IsCComponent) (hne : D ≠ K) :
    Nat.Coprime 3 (Nat.card D) := by
  let _ := pCore_isNilpotent (p := 2) (G := G)
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := K.map q
  let E := D.map q
  let e : (K ⧸ pCore 2 K) ≃* B := cComponentTwoCoreQuotientEquiv hK
  let _ : IsQuasisimple B := IsQuasisimple.of_mulEquiv e
  have hB : B.IsCComponent := hK.map_quotient _
  have hE : E.IsCComponent := hD.map_quotient _
  have hcomp : IsComponent (G ⧸ pCore 2 G) B := ⟨hB.subnormal, inferInstance⟩
  have hcomm : ⁅B, E⁆ = ⊥ := by
    rcases hcomp.subnormal_dichotomy E hE.subnormal with hle | hc
    · exact (hne (hD.eq_of_map_quotient_eq hK _ (hB.eq_of_le hE hle).symm)).elim
    · exact hc
  have hEC : E ≤ centralizer (B : Set (G ⧸ pCore 2 G)) := by
    rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
    exact hcomm
  have hc := centralizer_coprime_three_of_rank B (center_bot_transport e hz)
    ((primeRank_congr 3 e) ▸ hrK)
    ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans hrG)
  have hEcop := hc.coprime_dvd_right (card_dvd_of_le hEC)
  have hDcop : Nat.Coprime 3 (Nat.card (D ⧸ pCore 2 D)) := by
    rwa [Nat.card_congr (cComponentTwoCoreQuotientEquiv hD).toEquiv]
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 D)]
  apply hDcop.mul_right
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := D)).exists_card_eq
  rw [hn]
  exact (show Nat.Coprime 3 2 by decide).pow_right n

/-- Three-elements generate a C-component with simple rank-two two-core quotient. -/
theorem IsCComponent.le_primeToResidual_three (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)] (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hrK : 2 ≤ primeRank 3 (K ⧸ pCore 2 K)) : K ≤ primeToResidual 3 G := by
  let _ := hK.perfect
  let _ := IsQuasisimple.simple (G := K ⧸ pCore 2 K)
  let _ : IsSimpleGroup (K ⧸ pCore 2 K) :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  have hp : IsPPerfect 2 K := by
    intro N hN hquot
    let _ := hN
    have hsub : Subsingleton (K ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (K ⧸ N) hquot.isNilpotent
    apply eq_top_iff.mpr
    intro k _
    exact (QuotientGroup.eq_one_iff k).mp (Subsingleton.elim _ _)
  obtain ⟨E, _, hc⟩ := exists_elementary_nine_of_three_rank hrK
  have hd : 3 ∣ Nat.card (K ⧸ pCore 2 K) := by
    apply dvd_trans (show 3 ∣ Nat.card E by rw [hc]; decide) E.card_subgroup_dvd_card
  exact le_primeToResidual_of_eq_top 3 K
    (primeToResidual_eq_top_of_simple_quotient 3 2 (pCore 2 K) pCore_isPGroup hp hd)

/-- The nonexceptional residual deduction needs only the actual outer two-group bound. -/
theorem IsCComponent.eq_primeToResidual_three_of_outer_twoGroup (hK : K.IsCComponent)
    [K.Normal] [IsQuasisimple (K ⧸ pCore 2 K)]
    (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hrK : 2 ≤ primeRank 3 (K ⧸ pCore 2 K)) (hrG : primeRank 3 G ≤ 2)
    (ho : IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K))) :
    K = primeToResidual 3 G := by
  have hcop : Nat.Coprime 3 (Nat.card (MulAut.Outer (K ⧸ pCore 2 K))) := by
    obtain ⟨n, hn⟩ := ho.exists_card_dvd_pow
    exact ((show Nat.Coprime 3 2 by decide).pow_right n).coprime_dvd_right hn
  exact le_antisymm (hK.le_primeToResidual_three hz hrK)
    (primeToResidual_le K
      (cComponent_index_coprime_three_of_quotient K hK hz hrK hrG hcop))

/-- An outer group of order dividing twelve leaves a two-group quotient after
removing the three-prime residual. The Sylow subgroup therefore supplements it. -/
theorem IsCComponent.primeToResidual_three_sup_sylow (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hrK : 2 ≤ primeRank 3 (K ⧸ pCore 2 K))
    (hu : ∀ D : Subgroup G, D.IsCComponent → D = K)
    (hf : fittingSubgroup (G ⧸ pCore 2 G) = ⊥)
    (ho : Nat.card (MulAut.Outer (K ⧸ pCore 2 K)) ∣ 12) (S : Sylow 2 G) :
    primeToResidual 3 G ⊔ (S : Subgroup G) = ⊤ := by
  let _ := pCore_isNilpotent (p := 2) (G := G)
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := K.map q
  let R := primeToResidual 3 (G ⧸ pCore 2 G)
  have hB : B.IsCComponent := hK.map_quotient _
  have huB : ∀ D : Subgroup (G ⧸ pCore 2 G), D.IsCComponent → D = B :=
    fun _ hD => hK.unique_map_quotient hu _ hD
  let _ := hB.normal_of_unique huB
  have hBi : B.index ∣ Nat.card (MulAut.Outer B) := by
    rw [index_eq_card]
    exact card_dvd_of_injective (MulAut.outerAction B)
      (MulAut.outerAction_injective B (hB.centralizer_bot_of_unique_of_fitting_bot huB hf))
  have hBR : B ≤ R := by
    have hm := map_mono (f := q) (hK.le_primeToResidual_three hz hrK)
    rwa [map_primeToResidual_of_surjective 3 q (QuotientGroup.mk'_surjective _)] at hm
  have hi : R.index ∣ 12 := by
    have he := Nat.card_congr
      (MulAut.outerCongr (cComponentTwoCoreQuotientEquiv hK)).toEquiv
    exact (index_dvd_of_le hBR).trans (hBi.trans (he ▸ ho))
  have hc : Nat.Coprime R.index 3 := (primeToResidual_index_coprime 3).symm
  have hi4 : R.index ∣ 4 := hc.dvd_of_dvd_mul_right (by simpa using hi)
  have hp : IsPGroup 2 ((G ⧸ pCore 2 G) ⧸ R) :=
    IsPGroup.of_card_dvd_pow (n := 2) (by rwa [← index_eq_card])
  let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G))
  have hg : R ⊔ (Sbar : Subgroup (G ⧸ pCore 2 G)) = ⊤ := by
    apply top_unique
    rw [← pResidual_sup_sylow_eq_top Sbar]
    exact sup_le_sup (sInf_le ⟨inferInstance, hp⟩) le_rfl
  have hm : (primeToResidual 3 G ⊔ (S : Subgroup G)).map q = ⊤ := by
    rw [map_sup, map_primeToResidual_of_surjective 3 q (QuotientGroup.mk'_surjective _)]
    exact hg
  have hc2 : pCore 2 G ≤ (S : Subgroup G) := pCore_isPGroup.le_sylow_of_normal S
  have he := congrArg (comap q) hm
  rw [comap_map_eq, QuotientGroup.ker_mk', comap_top] at he
  rwa [sup_assoc, sup_eq_left.mpr hc2] at he
end Subgroup
