module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.RankOneTerminalDistance
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.RadiusThreeUnitary
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.UnitaryCoreOmega

/-!
# The proper-core-product case of nonlinear critical distance five

A larger unitary starting quotient with a proper adjacent-core product
has critical distance three. The preceding omega theorem places the
entire terminal core over the moving Sylow omega-center. DGS 8.3 and
relative normality then bound its commutator with the whole neighboring
span by H. Consequently the literal residual denominator has fixed index
strictly below the terminal field size, contradicting residual movement.

The proof includes every terminal model, with the two small unitary covers
handled by the established small-terminal distance theorem. The action is
on the original W/V_beta; no elementary or faithful-section assumption is
added. A common edge conjugator transports the original cores and unitary
quotient to the actual moving neighbor. The resulting source alternative
is b = 3 or the full original adjacent-core product.

This closes the proper-product unitary branch of DGS 8.4(3), including
b = 5. It leaves the full-product and other nonlinear branches, and the
remaining 8.5--8.7 conclusions, open. In particular no central-containment
or reverse-field-comparison hypothesis is used to establish this distance.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
5.7, 8.2--8.4, printed pp.108,134--138.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

private theorem radius_three_false_of_core_bound
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 3 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    (hcore : ⁅Q (Reduction.reducedFamily J S₀) a',V (Reduction.reducedFamily J S₀) a' 1⁆ ≤
      ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
        V (Reduction.reducedFamily J S₀) a' 1⁆) : False := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let W := V F beta 3
  let V₀ := V F beta 1
  let I := W ⊓ Q F a'
  let D := I ⊔ V₀
  let A := V F a' 1
  let L := graphLocalGroup F beta
  let L' := graphLocalGroup F a'
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let : Finite L := Finite.of_injective (inclusion (d.local_le beta)) (inclusion_injective _)
  let : Finite L' := Finite.of_injective (inclusion (d.local_le a')) (inclusion_injective _)
  change 3 < b F at hb
  have hb1 : 1 < b F := by omega
  have hWP : W ≤ stabilizer F beta := V_le_stabilizer_of_dist_add_le_b F ht.generate
    beta beta 3 (by simpa using hb.le)
  let : Finite W := Finite.of_injective (inclusion hWP) (inclusion_injective _)
  have hVW : V₀ ≤ W := V_mono F beta (by decide)
  have hnV : W ≤ normalizer (V₀ : Set (Reduction.G₀ J S₀)) :=
    hWP.trans (stabilizer_normalizes_V F beta 1)
  have hnA : A ≤ normalizer (V₀ : Set (Reduction.G₀ J S₀)) :=
    (radius_one_mutual_normalization F ht.generate beta a' hd.le).2
  have hH : ⁅V₀ ⊓ Q F a',A⁆ ≤ V₀ :=
    (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hnA)
  have hI : ⁅I,A⁆ ≤ V₀ := ((commutator_mono inf_le_right le_rfl).trans hcore).trans hH
  have hD : ⁅A,D⁆ ≤ V₀ := by
    rw [commutator_comm]
    exact commutator_sup_le_of_relative_normal W I V₀ A V₀ hnV inf_le_left hVW hI
      (le_normalizer_iff_commutator_le_left.mp hnA)
  have hpW : IsPGroup 2 W := (isPGroup_pCoreIn 2 (stabilizer F beta)).to_le
    (V_le_Q_of_dist_add_lt_b F ht.generate (fun v => (source_Z_Q_U ht v).1)
      beta beta 3 (by simpa only [SimpleGraph.dist_self,zero_add] using hb) (d.kernel_sylow beta))
  have hAp : IsPGroup 2 A := (isPGroup_pCoreIn 2 (stabilizer F a')).to_le
    (V_le_Q_of_dist_add_lt_b F ht.generate (fun v => (source_Z_Q_U ht v).1)
      a' a' 1 (by simpa using hb1) (d.kernel_sylow a'))
  have hAP : A ≤ stabilizer F beta := V_le_stabilizer_of_dist_add_le_b F ht.generate
    a' beta 1 (by rw [SimpleGraph.dist_comm]; exact hd.le)
  have hAL : A ≤ L := pGroup_le_localGroup F d beta A hAp hAP
  let π := QuotientGroup.mk' (pCore 2 L)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hk : π.ker = pCore 2 L := QuotientGroup.ker_mk' _
  have hAQ : ¬ A.subgroupOf L ≤ pCore 2 L := by
    intro hh
    apply reduced_reciprocal_escape h hob models hc hab hd hb1 hcomm hne
    rw [←localGroup_core_eq F d beta]
    intro x hx
    exact ⟨⟨x,hAL hx⟩,hh hx,rfl⟩
  have hπA : (A.subgroupOf L).map π ≠ ⊥ :=
    fun he => hAQ (hk ▸ (Subgroup.map_eq_bot_iff _).mp he)
  obtain ⟨hnW,hN,α,hα,hr,_,_,hlin⟩ := reduced_radius_three_residual_section.{_,0}
    h hob models hc hab hd hb hcomm hne
  let _ := hN
  let X := W ⧸ V₀.subgroupOf W
  let : Finite X := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  let : IsElementaryAbelian 2 A := CommutingThreeProfile.V_elementary F ht.generate
    (fun v => (source_Z_Q_U ht v).1) d.kernel_sylow (by omega) a'
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  have hfix := quotient_conjugation_fixedIndex_le L W V₀ D A hnW α hα le_sup_right hD
  obtain ⟨prev,T,_,_,_,_,_,_,_,hu⟩ := reduced_radius_three_section_index h hob models
    hc hab hd hb hcomm hne
  change Sylow 2 L' at T
  let S := T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 L'))
  have hupper (r : ℕ) (hrank : primeRank 2 (L' ⧸ pCore 2 L') ≤ r) : D.relIndex W < 2^r :=
    hu.trans_le ((primeRank_le_iff_elementary_card_le (L' ⧸ pCore 2 L')).mp hrank
      (omegaCenterIn (S : Subgroup (L' ⧸ pCore 2 L'))) inferInstance)
  have heven : Even ((graph F).dist beta a') := by
    obtain ⟨r,hr⟩ := (source_critical_geometry ht d hc hab hd hb1 hcomm).1
    change b F = 2*r+1 at hr
    change (graph F).dist beta a' + 1 = b F at hd
    refine ⟨r,?_⟩
    have he : (graph F).dist beta a' = 2*r := Nat.add_right_cancel (hd.trans hr)
    simpa only [two_mul] using he
  obtain ⟨g,hg⟩ := (same_orbit_iff F beta a').mpr ((even_dist_iff F ht.generate beta a').mp heven)
  have heq : (d.localGroup beta).map (MulAut.conj g).toMonoidHom = d.localGroup a' := by
    rw [←d.conjugate,hg]
  let f := ((d.localGroup beta).equivMapOfInjective
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr heq)
  let ef : (L ⧸ pCore 2 L) ≃* (L' ⧸ pCore 2 L') := QuotientGroup.congr _ _ f (pCore_map_iso 2 f)
  have hsmall (hs : ClassicalGroup.IsPSL (L' ⧸ pCore 2 L') 2 2 ∨
      Nonempty ((L' ⧸ pCore 2 L') ≃* DihedralGroup 5) ∨
      Nonempty ((L' ⧸ pCore 2 L') ≃* SuzukiMatrixGroup 0) ∨
      ClassicalGroup.IsPSU (L' ⧸ pCore 2 L') 3 2 ∨ IsSU (L' ⧸ pCore 2 L') 3 2) : False := by
    have he := reduced_small_terminal_distance_three h hob models hc hab hd hb1 hcomm hne hs
    change b F = 3 at he
    omega
  have hunit {K : Type} [Field K] [Finite K] (H : HermitianForm 3 K)
      {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2^n)^2)
      (hconj : ∀ x, H.conj x = x^(2^n))
      (e : Nonempty ((L' ⧸ pCore 2 L') ≃* H.specialSubgroup) ∨
        Nonempty ((L' ⧸ pCore 2 L') ≃* ProjectiveSpecialUnitaryMatrixGroup H)) : False := by
    have eβ : Nonempty ((L ⧸ pCore 2 L) ≃* H.specialSubgroup) ∨
        Nonempty ((L ⧸ pCore 2 L) ≃* ProjectiveSpecialUnitaryMatrixGroup H) := by
      rcases e with he | he
      · exact Or.inl ⟨ef.trans he.some⟩
      · exact Or.inr ⟨ef.trans he.some⟩
    have hlo := Representation.SU3.twoGroup_fixedIndex_lower_of_residual_moves H hn hK hconj eβ
      π hπ (by rw [hk]; exact pCore_isPGroup) (hpW.to_quotient _) α hr (A.subgroupOf L) hπA
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup H) :=
      Finite.of_surjective H.specialToProjective H.specialToProjective_surjective
    have hrank : primeRank 2 (L' ⧸ pCore 2 L') ≤ n := by
      rcases e with he | he
      · rw [primeRank_congr 2 he.some,primeRank_eq_of_surjective_of_coprime 2 H.specialToProjective
          H.specialToProjective_surjective H.odd_card_specialToProjective_ker.coprime_two_left]
        exact (HermitianForm.EvenTwoRank.two_rank H (by omega) hK hconj).le
      · rw [primeRank_congr 2 he.some]
        exact (HermitianForm.EvenTwoRank.two_rank H (by omega) hK hconj).le
    exact (not_lt_of_ge (hlo.trans hfix)) (hupper n hrank)
  cases models a' with
  | linear n hn hi =>
    obtain ⟨K,_,_,hK,⟨eK⟩⟩ := hi
    let := Fintype.ofFinite K
    let : CharP K 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hK)
    let e : (L' ⧸ pCore 2 L') ≃* SL(2,K) := eK.trans (MulEquiv.ofBijective
      (BenderSuzuki.Converse.pi K) ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
    let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
    have hcard : Nat.card S = Nat.card K := by
      calc
        Nat.card S = Nat.card S' := Nat.card_congr
          ((S : Subgroup (L' ⧸ pCore 2 L')).equivMapOfInjective e.toMonoidHom e.injective).toEquiv
        _ = Nat.card K := (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive K 2 S').toEquiv).symm
    have hO : Nat.card (omegaCenterIn (S : Subgroup (L' ⧸ pCore 2 L'))) ≤ Nat.card K := by
      rw [←hcard]
      exact Nat.card_le_card_of_injective (inclusion (map_subtype_le _)) (inclusion_injective _)
    exact (not_lt_of_ge ((hlin K n hn hK (ef.trans e)).trans hfix)) (hu.trans_le hO)
  | dihedral hi => exact hsmall (Or.inr (Or.inl hi))
  | suzuki m hi =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact hsmall (Or.inr (Or.inr (Or.inl hi)))
    let e := ef.trans hi.some
    let π' := e.toMonoidHom.comp π
    have hπ' : Function.Surjective π' := e.surjective.comp hπ
    have hk' : π'.ker = pCore 2 L := by
      ext x
      change e (π x) = 1 ↔ x ∈ pCore 2 L
      rw [←e.map_one,e.injective.eq_iff]
      exact QuotientGroup.eq_one_iff x
    have hA' : (A.subgroupOf L).map π' ≠ ⊥ :=
      fun he => hAQ (hk' ▸ (Subgroup.map_eq_bot_iff _).mp he)
    have hlo := Representation.Suzuki.twoGroup_fixedIndex_lower_of_residual_moves hm
      π' hπ' (by rw [hk']; exact pCore_isPGroup) (hpW.to_quotient _) α hr
      (A.subgroupOf L) hAp.comap_subtype hA'
    have hrank : primeRank 2 (L' ⧸ pCore 2 L') ≤ 2*m+1 := by
      rw [primeRank_congr 2 hi.some,suzuki_two_rank m hm]
    have hlo' : 2^(2*m+1) ≤ D.relIndex W := (Nat.le_self_pow (by decide : 2 ≠ 0) _).trans (hlo.trans hfix)
    exact (not_lt_of_ge hlo') (hupper (2*m+1) hrank)
  | projective_unitary n hn hi =>
    by_cases hn2 : 2 ≤ n
    · obtain ⟨K,_,_,H,hK,hconj,he⟩ := hi
      exact hunit H hn2 hK hconj (Or.inr he)
    · have hn1 : n=1 := by omega
      exact hsmall (Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [hn1,pow_one] using hi)))))
  | special_unitary n hn hi =>
    by_cases hn2 : 2 ≤ n
    · obtain ⟨K,_,_,H,hK,hconj,he⟩ := hi
      exact hunit H hn2 hK hconj (Or.inl he)
    · have hn1 : n=1 := by omega
      exact hsmall (Or.inr (Or.inr (Or.inr (Or.inr (by simpa only [hn1,pow_one] using hi)))))

/-- A proper core product at a larger unitary moving edge closes the
distance-three argument for every terminal model. The original 8.3 bound,
literal intersection placement and residual-section comparison are all
discharged; the core-product case condition is retained explicitly. -/
theorem reduced_unitary_proper_edge_distance_three
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily J S₀)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≠ ⊥)
    {n : ℕ} (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) 3 (2^n) ∨
      IsSU (graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) 3 (2^n))
    (hproper : ¬ (stabilizer (Reduction.reducedFamily J S₀) w.val ⊓
      stabilizer (Reduction.reducedFamily J S₀) a').pCoreIn 2 ≤
      Q (Reduction.reducedFamily J S₀) w.val ⊔ Q (Reduction.reducedFamily J S₀) a') :
    b (Reduction.reducedFamily J S₀) = 3 := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let H := ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆
  let := finite_endpoints ht
  obtain ⟨_,hb3,_⟩ := source_critical_geometry ht d hc hab hd hb hcomm
  by_contra he
  have hbgt : 3 < b F := by change 3 ≤ b F at hb3; change b F ≠ 3 at he; omega
  have hne : H ≠ ⊥ := by
    intro hz
    exact hm (bot_unique ((commutator_mono le_rfl (Z_neighbor_le_V F w.property)).trans hz.le))
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow ht (Reduction.reduced_borel_core_sylow h)
    d w.property.symm
  have hQ := source_unitary_neighbor_core_le_omega ht d w.property.symm
    (models w.val) R hR hn hu hproper
  obtain ⟨hnH,hHZ,_⟩ := source_critical_commutator_structure ht
    (Reduction.reduced_borel_core_sylow h) d hc hab hd hb hcomm models
  have hZL : Z F w.val ≤ d.localGroup a' :=
    ((Z_neighbor_le_V F w.property).trans
      (V_le_Q_of_dist_add_lt_b F ht.generate (fun v => (source_Z_Q_U ht v).1)
        a' a' 1 (by simpa using hb) (d.kernel_sylow a'))).trans
      ((pCoreIn_le_sylow (stabilizer F a') default).trans (d.sylow_le a' default))
  have hn' : d.localGroup a' ≤ normalizer (H : Set (Reduction.G₀ J S₀)) :=
    (normal_subgroupOf_iff_le_normalizer ((hHZ w).trans hZL)).mp hnH
  have hcore := source_core_full_span_bound ht d hb w R hQ H hn'
    (reduced_moving_omega_commutator h hob models hc hab hd hb hcomm w hm R hR)
  exact radius_three_false_of_core_bound h hob models hc hab hd hbgt hcomm hne hcore

/-- The original ordered critical configuration closes this case without
a supplied moving-neighbor witness. A common edge conjugator transports
both original cores and the actual starting unitary quotient. -/
theorem reduced_unitary_start_proper_core_product_distance_three
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    {n : ℕ} (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup (Reduction.reducedFamily J S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a)) 3 (2^n) ∨
      IsSU (graphLocalGroup (Reduction.reducedFamily J S₀) a ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a)) 3 (2^n))
    (hproper : ¬ (stabilizer (Reduction.reducedFamily J S₀) a ⊓
      stabilizer (Reduction.reducedFamily J S₀) beta).pCoreIn 2 ≤
      Q (Reduction.reducedFamily J S₀) a ⊔ Q (Reduction.reducedFamily J S₀) beta) :
    b (Reduction.reducedFamily J S₀) = 3 := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let := finite_endpoints ht
  obtain ⟨w,hm,_⟩ := exists_moving_neighbor F (fun v => (source_Z_Q_U ht v).1) beta a' hne
  have hbt : beta.type = a'.type := by
    apply (even_dist_iff F ht.generate beta a').mp
    obtain ⟨r,hr⟩ := (source_critical_geometry ht d hc hab hd hb hcomm).1
    change b F = 2*r+1 at hr
    change (graph F).dist beta a' + 1 = b F at hd
    refine ⟨r,?_⟩
    have he : (graph F).dist beta a' = 2*r := Nat.add_right_cancel (hd.trans hr)
    simpa only [two_mul] using he
  have haw : a.type = w.val.type := by
    have ha := hab.1
    have hw := w.property.1
    cases ha' : a.type <;> cases hb' : beta.type <;>
      cases hw' : w.val.type <;> cases ht' : a'.type <;> simp_all
  obtain ⟨g,hga,hgb⟩ := incident_common_translate F hab.2
  have hwa : (graph F).Adj w.val a' := w.property.symm
  obtain ⟨t,htw,hta⟩ := incident_common_translate F hwa.2
  let u := t*g⁻¹
  have hua : u • a = w.val := by
    rw [←hga]
    simp only [u,mul_smul,inv_smul_smul,haw,htw]
  have hub : u • beta = a' := by
    rw [←hgb]
    simp only [u,mul_smul,inv_smul_smul,hbt,hta]
  let e := MulAut.conj u
  have hEdge : (stabilizer F a ⊓ stabilizer F beta).map e.toMonoidHom =
      stabilizer F w.val ⊓ stabilizer F a' := by
    rw [map_inf _ _ _ e.injective]
    change (stabilizer F a).map (MulAut.conj u).toMonoidHom ⊓
      (stabilizer F beta).map (MulAut.conj u).toMonoidHom = _
    rw [←stabilizer_translate,←stabilizer_translate,hua,hub]
  have hCore : ((stabilizer F a ⊓ stabilizer F beta).pCoreIn 2).map e.toMonoidHom =
      (stabilizer F w.val ⊓ stabilizer F a').pCoreIn 2 := by
    rw [←Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _ e.injective,hEdge]
  have hp : ¬ (stabilizer F w.val ⊓ stabilizer F a').pCoreIn 2 ≤ Q F w.val ⊔ Q F a' := by
    intro hh
    apply hproper
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [hCore,Subgroup.map_sup]
    change (stabilizer F w.val ⊓ stabilizer F a').pCoreIn 2 ≤
      (Q F a).map (MulAut.conj u).toMonoidHom ⊔ (Q F beta).map (MulAut.conj u).toMonoidHom
    rwa [←Q_translate,←Q_translate,hua,hub]
  have hL : (d.localGroup a).map e.toMonoidHom = d.localGroup w.val := by
    rw [←d.conjugate,hua]
  let f := ((d.localGroup a).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr hL)
  let ef := QuotientGroup.congr _ _ f (pCore_map_iso 2 f)
  have huw : ClassicalGroup.IsPSU (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) 3 (2^n) ∨
      IsSU (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) 3 (2^n) := by
    rcases hu with hu | hu
    · obtain ⟨K,_,_,H,hK,hconj,⟨eK⟩⟩ := hu
      exact Or.inl ⟨K,inferInstance,inferInstance,H,hK,hconj,⟨ef.symm.trans eK⟩⟩
    · obtain ⟨K,_,_,H,hK,hconj,⟨eK⟩⟩ := hu
      exact Or.inr ⟨K,inferInstance,inferInstance,H,hK,hconj,⟨ef.symm.trans eK⟩⟩
  exact reduced_unitary_proper_edge_distance_three h hob models hc hab hd hb hcomm w hm hn huw hp

/-- In either original critical orientation, a larger unitary starting
quotient leaves only distance three or the full adjacent-core product.
Thus the proper-product nonlinear distance-five case is eliminated without
assuming any square bound on the literal intersection. -/
theorem reduced_unitary_start_distance_or_core_product
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    {n : ℕ} (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup (Reduction.reducedFamily J S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a)) 3 (2^n) ∨
      IsSU (graphLocalGroup (Reduction.reducedFamily J S₀) a ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a)) 3 (2^n))
 :
    b (Reduction.reducedFamily J S₀) = 3 ∨
      Q (Reduction.reducedFamily J S₀) a ⊔ Q (Reduction.reducedFamily J S₀) beta =
        (stabilizer (Reduction.reducedFamily J S₀) a ⊓
          stabilizer (Reduction.reducedFamily J S₀) beta).pCoreIn 2 := by
  by_cases hp : (stabilizer (Reduction.reducedFamily J S₀) a ⊓
      stabilizer (Reduction.reducedFamily J S₀) beta).pCoreIn 2 ≤
      Q (Reduction.reducedFamily J S₀) a ⊔ Q (Reduction.reducedFamily J S₀) beta
  · right
    refine le_antisymm (sup_le ?_ ?_) hp
    · exact Noncommuting.graph_Q_le_edgeCore (Reduction.reduced_triple h) hab
    · have hh := Noncommuting.graph_Q_le_edgeCore (Reduction.reduced_triple h) hab.symm
      rw [inf_comm] at hh
      exact fun x hx => hh hx
  · exact Or.inl (reduced_unitary_start_proper_core_product_distance_three
      h hob models hc hab hd hb hcomm hne hn hu hp)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
