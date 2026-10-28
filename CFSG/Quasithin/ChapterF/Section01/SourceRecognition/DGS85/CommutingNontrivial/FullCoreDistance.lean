module
public import Theory.SpecificGroups.Suzuki.SupplementInvariantSubgroups
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.FullCoreProduct
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.UnitaryCoreDistance

/-!
# Closing full core products and the Suzuki and larger unitary starts

The original source configuration supplies two-transitivity at every local
vertex once the already excluded dihedral orientations are removed. A full
adjacent-core product then makes W elementary by `FullCoreProduct`, giving
genuine involution generation of W intersect Q_alpha'. The marked 8.3 bound
propagates to the whole neighboring span, so the literal residual denominator
has fixed index strictly below the terminal Sylow omega-center. The proved
linear, Suzuki and unitary residual bounds contradict this in every model.

Combining this with the proper-product unitary proof establishes b = 3 for
all larger SU3 and PSU3 starting quotients. The Suzuki normalizer dichotomy
handles every proper product there; at Sz(2), a proper subgroup of the
order-four Sylow has exponent two. Thus all Suzuki starting quotients also
have b = 3. The exhaustive original catalogue leaves only SU3(2) or PSU3(2)
starting quotients with a proper adjacent-core product at b = 5.

Both critical orientations and every terminal model are retained. The
remaining small-unitary proper-product case and the 8.5--8.7 identifications
are separate obligations. The original earlier 6.5 obstruction and full
local catalogue are retained, not replaced by a square-placement or
transitivity callback.

Source: DGS, *Groups and Graphs* (1985), 5.7 and 8.2--8.4, pp.108,134--138.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G]
variable {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

private theorem radius_three_false_of_intersection_bound
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
    (hcore : ⁅V (Reduction.reducedFamily J S₀) beta 3 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≤
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
  have hI : ⁅I,A⁆ ≤ V₀ := hcore.trans hH
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

/-- The full original adjacent-core product closes b = 5 for every source
model. Both dihedral orientations are discharged by the existing distance
results, so all required local transitivity witnesses are constructed. -/
theorem reduced_full_core_product_distance_three
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
    (hprod : Q (Reduction.reducedFamily J S₀) a ⊔ Q (Reduction.reducedFamily J S₀) beta =
      (stabilizer (Reduction.reducedFamily J S₀) a ⊓ stabilizer (Reduction.reducedFamily J S₀) beta).pCoreIn 2) :
    b (Reduction.reducedFamily J S₀) = 3 := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let H := ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆
  let := finite_endpoints ht
  have hb3 := (source_critical_geometry ht d hc hab hd hb hcomm).2.1
  change 3 ≤ b F at hb3
  by_contra he
  change b F ≠ 3 at he
  have hbgt : 3 < b F := by omega
  have hb5 : b F = 5 := by
    have hh := reduced_distance_le_five h hob models hc hab hd hb hcomm hne
    change b F = 3 ∨ b F = 5 at hh
    exact hh.resolve_left he
  have transport (u v : Vertex F) (htype : u.type = v.type) :
      Nonempty ((d.localGroup u ⧸ pCore 2 (d.localGroup u)) ≃*
        (d.localGroup v ⧸ pCore 2 (d.localGroup v))) := by
    obtain ⟨g,hg⟩ := (same_orbit_iff F u v).mpr htype
    have hL : (d.localGroup u).map (MulAut.conj g).toMonoidHom = d.localGroup v := by
      rw [←d.conjugate,hg]
    let f := ((d.localGroup u).equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hL)
    exact ⟨QuotientGroup.congr _ _ f (pCore_map_iso 2 f)⟩
  have htrans (v w : Vertex F) (hvw : (graph F).Adj v w) :
      ∀ x y : Vertex F, (graph F).Adj v x → (graph F).Adj v y → x ≠ w → y ≠ w →
      ∃ g ∈ d.localGroup v ⊓ stabilizer F w, g • x = y := by
    rcases source_edge_transitive_or_dihedral ht (Reduction.reduced_borel_core_sylow h) d hvw (models v) with htr | hi
    · exact htr
    · exfalso
      by_cases hav : a.type = v.type
      · exact he (reduced_linear_start_distance_three h hob models hc hab hd hb hcomm hne
          (Or.inr ⟨(transport a v hav).some.trans hi.some⟩))
      · have haa' : a.type ≠ a'.type := (odd_dist_iff F ht.generate a a').mp
          (hc.1.symm ▸ (source_critical_geometry ht d hc hab hd hb hcomm).1)
        have ha'v : a'.type = v.type := by
          cases ha : a.type <;> cases hv : v.type <;> cases ha' : a'.type <;> simp_all
        exact he (reduced_small_terminal_distance_three h hob models hc hab hd hb hcomm hne
          (Or.inr (Or.inl ⟨(transport a' v ha'v).some.trans hi.some⟩)))
  let : IsElementaryAbelian 2 (V F beta 3) := source_full_product_radius_three_elementary ht
    (Reduction.reduced_borel_core_sylow h) d hob models hc hab hd hb5 hcomm hne hprod htrans
  let I := V F beta 3 ⊓ Q F a'
  let : IsElementaryAbelian 2 I := IsElementaryAbelian.of_le inf_le_left
  have hgen : involutionGenerated I = I := le_antisymm (involutionGenerated_le _) (by
    intro x hx
    exact subset_closure ⟨hx,elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx⟩)
  obtain ⟨w,hm,_⟩ := exists_moving_neighbor F (fun v => (source_Z_Q_U ht v).1) beta a' hne
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow ht (Reduction.reduced_borel_core_sylow h) d w.property.symm
  obtain ⟨hnH,hHZ,_⟩ := source_critical_commutator_structure ht
    (Reduction.reduced_borel_core_sylow h) d hc hab hd hb hcomm models
  have hZL : Z F w.val ≤ d.localGroup a' :=
    ((Z_neighbor_le_V F w.property).trans
      (V_le_Q_of_dist_add_lt_b F ht.generate (fun v => (source_Z_Q_U ht v).1)
        a' a' 1 (by simpa using hb) (d.kernel_sylow a'))).trans
      ((pCoreIn_le_sylow (stabilizer F a') default).trans (d.sylow_le a' default))
  have hn' : d.localGroup a' ≤ normalizer (H : Set (Reduction.G₀ J S₀)) :=
    (normal_subgroupOf_iff_le_normalizer ((hHZ w).trans hZL)).mp hnH
  have hbound := source_radius_three_full_span_bound_of_involution_generated ht d hb w
    (models w.val) R hR hgen H hn'
    (reduced_moving_omega_commutator h hob models hc hab hd hb hcomm w hm R hR)
  exact radius_three_false_of_intersection_bound h hob models hc hab hd hbgt hcomm hne hbound

/-- Every larger special or projective unitary starting quotient has
critical distance three. The full and proper adjacent-core products are
both discharged, retaining every terminal model and the original maps. -/
theorem reduced_large_unitary_start_distance_three
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
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a)) 3 (2^n)) : b (Reduction.reducedFamily J S₀) = 3 := by
  rcases reduced_unitary_start_distance_or_core_product h hob models hc hab hd hb hcomm hne hn hu with he | hp
  · exact he
  · exact reduced_full_core_product_distance_three h hob models hc hab hd hb hcomm hne hp

private theorem suzuki_invariant_dichotomy {D : Type*} [Group D] [Finite D]
    (m : ℕ) (e : D ≃* SuzukiMatrixGroup m) (S : Sylow 2 D) (A : Subgroup D)
    (hA : A ≤ S) (hN : normalizer (S : Set D) ≤ normalizer (A : Set D)) :
    A ≤ omegaCenterIn (S : Subgroup D) ∨ A = S := by
  by_cases he : A = S
  · exact Or.inr he
  left
  have hElem : IsElementaryAbelian 2 A := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hcS : Nat.card S = 4 := by
        rw [S.card_eq_multiplicity,Nat.card_congr e.toEquiv,suzukiZero_card]
        rw [show (20 : ℕ) = 2^2 * 5 from rfl,
          Nat.factorization_mul (by decide) (by decide),Nat.factorization_pow,
          Nat.prime_two.factorization,Nat.prime_five.factorization]
        norm_num
      have hdvd : Nat.card A ∣ 2^2 := by
        have hh := card_dvd_of_le hA
        rwa [hcS] at hh
      obtain ⟨k,hk,hkc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      have hsquare : ∀ a : A, a^2=1 := by
        intro a
        interval_cases k
        · have hh := pow_card_eq_one' (x := a)
          have ha : a = 1 := by simpa only [hkc,pow_zero,pow_one] using hh
          rw [ha,one_pow]
        · simpa only [hkc,pow_one] using pow_card_eq_one' (x := a)
        · exact (he (eq_of_le_of_card_ge hA (by rw [hcS,hkc]; decide))).elim
      let : IsMulCommutative A := ⟨⟨fun x y => by
        have hinv (z : A) : z⁻¹=z := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hsquare z)
        calc
          x*y = (x*y)⁻¹ := (hinv _).symm
          _ = y*x := by rw [mul_inv_rev,hinv,hinv]⟩⟩
      exact ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsquare⟩
    · rcases suzuki_supplement_invariant_dichotomy hm e S A (normalizer (S : Set D)) hA
        (sup_eq_right.mpr le_normalizer) hN with ho | hfull
      · rw [←suzukiSylow_omega_eq_center hm e S] at ho
        let := suzukiSylow_omega_elementary hm e S
        exact IsElementaryAbelian.of_le ho
      · exact (he hfull).elim
  let := hElem
  exact source_rank_one_elementary_le_sylow_omega (.suzuki m ⟨e⟩) S A hA

variable {P : Fin 2 → Subgroup G} {B : Subgroup G}
/-- A proper adjacent-core product puts the whole opposite core over the
marked Suzuki Sylow omega-center, including the order-four Sylow at Sz(2). -/
theorem source_suzuki_neighbor_core_le_omega
    (h : LocallyRankOneTriple P B) (d : EarlierLocalTheorems (family P))
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (M : IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (R : Sylow 2 (d.localGroup v))
    (hR : (R : Subgroup (d.localGroup v)).map (d.localGroup v).subtype =
      (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2)
    (m : ℕ) (e : (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* SuzukiMatrixGroup m)
    (hproper : ¬ (stabilizer (family P) v ⊓ stabilizer (family P) w).pCoreIn 2 ≤
      Q (family P) v ⊔ Q (family P) w) :
    Q (family P) w ≤ quotientSylowOmegaPreimage (d.localGroup v) R := by
  let := finite_endpoints h
  let F := family P
  let L := d.localGroup v
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  let q := QuotientGroup.mk' (pCore 2 L)
  let S := R.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let A := (Q F w).subgroupOf L
  have hQR : Q F w ≤ (R : Subgroup L).map L.subtype := by
    rw [hR]
    simpa only [inf_comm] using Noncommuting.graph_Q_le_edgeCore h hvw.symm
  have hQL : Q F w ≤ L := hQR.trans (map_subtype_le _)
  have hAR : A ≤ R := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hQR hx
    exact (Subtype.ext he : y=x) ▸ hy
  have hNA : normalizer (R : Set L) ≤ normalizer (A : Set L) := by
    apply le_normalizer_iff.mpr
    intro g hg x hx
    have hgw : (g : G) ∈ stabilizer F w := by
      have hg' : g ∈ (stabilizer F w).subgroupOf L :=
        (source_edge_local_normalizer h d hvw M R hR).2.symm ▸ hg
      exact hg'
    exact le_normalizer_iff.mp (stabilizer_normalizes_Q F w) g hgw x hx
  have hNq : normalizer (S : Set (L ⧸ pCore 2 L)) ≤
      normalizer (A.map q : Set (L ⧸ pCore 2 L)) := by
    change normalizer ((R : Subgroup L).map q : Set (L ⧸ pCore 2 L)) ≤ _
    rw [←R.normalizer_map_surjective q (QuotientGroup.mk'_surjective _)]
    exact (map_mono hNA).trans (A.le_normalizer_map q)
  have hAO : A.map q ≤ omegaCenterIn (S : Subgroup (L ⧸ pCore 2 L)) := by
    rcases suzuki_invariant_dichotomy m e S (A.map q) (map_mono hAR) hNq with ho | he
    · exact ho
    · exfalso
      apply hproper
      rw [←hR]
      rintro _ ⟨r,hr,rfl⟩
      have hqr : q r ∈ A.map q := he ▸ mem_map_of_mem q hr
      obtain ⟨x,hx,hxr⟩ := hqr
      have hk : x⁻¹*r ∈ pCore 2 L := by
        apply (QuotientGroup.eq_one_iff _).mp
        change q (x⁻¹*r) = 1
        rw [map_mul,map_inv,hxr,inv_mul_cancel]
      have hkQ : (x : G)⁻¹*(r : G) ∈ Q F v := by
        rw [←localGroup_core_eq F d v]
        exact mem_map_of_mem L.subtype hk
      have hh := (Q F v ⊔ Q F w).mul_mem
        ((show Q F w ≤ Q F v ⊔ Q F w from le_sup_right) hx)
        ((show Q F v ≤ Q F v ⊔ Q F w from le_sup_left) hkQ)
      simpa only [subtype_apply,mul_inv_cancel_left] using hh
  intro x hx
  exact ⟨⟨x,hQL hx⟩,hAO (mem_map_of_mem q hx),rfl⟩

/-- Every original Suzuki starting quotient has critical distance three.
The literal full and proper core-product cases, including Sz(2), and every
terminal model are discharged. -/
theorem reduced_suzuki_start_distance_three
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
    (m : ℕ) (e : (graphLocalGroup (Reduction.reducedFamily J S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a)) ≃* SuzukiMatrixGroup m) :
    b (Reduction.reducedFamily J S₀) = 3 := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let H := ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆
  let := finite_endpoints ht
  by_cases hprod : Q F a ⊔ Q F beta = (stabilizer F a ⊓ stabilizer F beta).pCoreIn 2
  · exact reduced_full_core_product_distance_three h hob models hc hab hd hb hcomm hne hprod
  have hb3 := (source_critical_geometry ht d hc hab hd hb hcomm).2.1
  change 3 ≤ b F at hb3
  by_contra he
  change b F ≠ 3 at he
  have hbgt : 3 < b F := by omega
  have haa' : a.type ≠ a'.type := (odd_dist_iff F ht.generate a a').mp
    (hc.1.symm ▸ (source_critical_geometry ht d hc hab hd hb hcomm).1)
  obtain ⟨w,hm,_⟩ := exists_moving_neighbor F (fun v => (source_Z_Q_U ht v).1) beta a' hne
  have haw : a.type = w.val.type := by
    have hw := w.property.1
    cases ha : a.type <;> cases hw' : w.val.type <;> cases ha' : a'.type <;> simp_all
  obtain ⟨g,hgw⟩ := (same_orbit_iff F a w.val).mpr haw
  have hL : (d.localGroup a).map (MulAut.conj g).toMonoidHom = d.localGroup w.val := by
    rw [←d.conjugate,hgw]
  let f := ((d.localGroup a).equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hL)
  let ef := QuotientGroup.congr _ _ f (pCore_map_iso 2 f)
  let ew : (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃* SuzukiMatrixGroup m := ef.symm.trans e
  have hp : ¬ (stabilizer F w.val ⊓ stabilizer F a').pCoreIn 2 ≤ Q F w.val ⊔ Q F a' := by
    intro hh
    have hp' : Q F w.val ⊔ Q F a' = (stabilizer F w.val ⊓ stabilizer F a').pCoreIn 2 := by
      apply le_antisymm (sup_le (Noncommuting.graph_Q_le_edgeCore ht w.property.symm) ?_) hh
      have hq := Noncommuting.graph_Q_le_edgeCore ht w.property
      rw [inf_comm] at hq
      exact fun x hx => hq hx
    exact hprod (source_full_core_product_all_edges F w.property.symm hp' hab)
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow ht (Reduction.reduced_borel_core_sylow h) d w.property.symm
  have hQ := source_suzuki_neighbor_core_le_omega ht d w.property.symm (models w.val) R hR m ew hp
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
  exact radius_three_false_of_intersection_bound h hob models hc hab hd hbgt hcomm hne
    ((commutator_mono inf_le_right le_rfl).trans hcore)
/-- Exhaustive distance reduction on the original source catalogue: the
only remaining distance-five case has an actual small special or projective
unitary starting quotient and a proper original adjacent-core product.
This alternative does not assert that the remaining case exists. -/
theorem reduced_distance_three_or_small_unitary_start
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
    : b (Reduction.reducedFamily J S₀) = 3 ∨
      (b (Reduction.reducedFamily J S₀) = 5 ∧
        (ClassicalGroup.IsPSU (graphLocalGroup (Reduction.reducedFamily J S₀) a ⧸
          pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a)) 3 2 ∨
        IsSU (graphLocalGroup (Reduction.reducedFamily J S₀) a ⧸
          pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a)) 3 2) ∧
        Q (Reduction.reducedFamily J S₀) a ⊔ Q (Reduction.reducedFamily J S₀) beta ≠
          (stabilizer (Reduction.reducedFamily J S₀) a ⊓
            stabilizer (Reduction.reducedFamily J S₀) beta).pCoreIn 2) := by
  by_cases he : b (Reduction.reducedFamily J S₀) = 3
  · exact Or.inl he
  right
  refine ⟨(reduced_distance_le_five h hob models hc hab hd hb hcomm hne).resolve_left he,?_,?_⟩
  · cases models a with
    | linear n hn hi =>
      exact (he (reduced_linear_start_distance_three h hob models hc hab hd hb hcomm hne
        (Or.inl ⟨n,hn,hi⟩))).elim
    | dihedral hi =>
      exact (he (reduced_linear_start_distance_three h hob models hc hab hd hb hcomm hne
        (Or.inr hi))).elim
    | suzuki m hi =>
      exact (he (reduced_suzuki_start_distance_three h hob models hc hab hd hb hcomm hne m hi.some)).elim
    | projective_unitary n hn hi =>
      by_cases hn2 : 2 ≤ n
      · exact (he (reduced_large_unitary_start_distance_three h hob models hc hab hd hb hcomm hne hn2 (Or.inl hi))).elim
      · left
        have hn1 : n=1 := by omega
        simpa only [hn1,pow_one] using hi
    | special_unitary n hn hi =>
      by_cases hn2 : 2 ≤ n
      · exact (he (reduced_large_unitary_start_distance_three h hob models hc hab hd hb hcomm hne hn2 (Or.inr hi))).elim
      · right
        have hn1 : n=1 := by omega
        simpa only [hn1,pow_one] using hi
  · intro hp
    exact he (reduced_full_core_product_distance_three h hob models hc hab hd hb hcomm hne hp)
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
