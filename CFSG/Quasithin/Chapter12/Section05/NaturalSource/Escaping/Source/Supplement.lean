module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Escaping.Source.SylowKernel
public import Theory.GroupTheory.PCoreNormalizerAction.Kernel
public import Theory.GroupTheory.PResidual.NormalizedSupplement
public import Theory.SpecificGroups.PSL3Two.OuterThreeFree

/-!
# The original point-residual supplement

The literal quotient-centralizer X of L₁/O₂(L₁) inside G₁ supplements L₁.
The marked M₁ block acts by inner automorphisms. Since the outer group has
order two and the original full Sylow is already in that inner preimage,
every G₁ actor is inner; lifting its implementer gives G₁ = L₁X.

Under the preceding point-centralizer escape, finite descent inside XT
selects an original H-star subgroup. The existing fusion source gives its
generation-two and nontrivial Hall-three conclusions, and E.3.15 supplies
an actual conjugate of V escaping its two-core. The quotient-centralizer
consumes one of the point group's two cubic ranks. Since XT/X is a
two-group, the selected H and X both have three-rank exactly one, and
the embedded O²(H) lies in X. The literal first-node residual Y also lies
in X by its previously proved commutator bound. Point escape is retained
as an explicit earlier step of this same source argument. The original
block maps place the cubic Hall subgroup in P and give its order three;
[P:T]=3 then gives P≤H and the source incidence M₁≤L₁H.

Source: Aschbacher--Smith, proof of 12.5.1, printed pp.821--822.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 Representation.SL5ExteriorSquare
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

private def pointLargeBlock : s.marking.Mi 1 →* SL(3, ZMod 2) :=
  (MonoidHom.snd _ _).comp
    (s.M₁CoreEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (s.marking.Mi 1))))

set_option backward.isDefEq.respectTransparency false in
private theorem pointLargeBlock_residual (l : s.marking.Li 1) :
    s.pointLargeBlock (inclusion (s.Li_le_Mi 1) l) =
      s.marking.LiLinearHom 1 (.inl rfl) l := by
  change (parabolicLeviHom 2 (by decide)
    (s.localJoinActor 1 (.inl rfl) (inclusion (s.Li_le_Mi 1) l))).2 = _
  change _ = parabolicTwoResidualQuotientEquiv
    (QuotientGroup.mk' _ (s.marking.residualActor 1 (.inl rfl) l))
  rw [parabolicTwoResidualQuotientEquiv_mk]
  congr 2
  apply Subtype.ext
  change s.actor ⟨l,_⟩ = (s.marking.residualActor 1 (.inl rfl) l : Representation.SL5TenDimensional.Group)
  rw [s.marking.residualActor_apply]
  exact s.actor_component ⟨l,s.marking.Li_le_L 1 l.property⟩

set_option backward.isDefEq.respectTransparency false in
private theorem point_normalizer_acts_inner (m : s.marking.Mi 1) :
    pCoreNormalizerAction 2 (s.marking.Li 1)
      (inclusion (s.Mi_normalizes_Li 1) m) ∈
        MulAut.innerSubgroup (s.marking.Li 1 ⧸ pCore 2 (s.marking.Li 1)) := by
  obtain ⟨l,hl⟩ := s.marking.LiLinearHom_surjective 1 (.inl rfl) (s.pointLargeBlock m)
  refine ⟨QuotientGroup.mk' _ l, ?_⟩
  apply MulEquiv.ext
  intro q
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (s.marking.Li 1)) q
  rw [pCoreNormalizerAction_mk, MulAut.conj_apply, ←map_inv, ←map_mul, ←map_mul]
  apply (s.marking.LiCoreEquiv 1 (.inl rfl)).injective
  rw [s.marking.LiCoreEquiv_mk, s.marking.LiCoreEquiv_mk,
    map_mul,map_mul,map_inv,hl]
  simp only [←s.pointLargeBlock_residual]
  have he : inclusion (s.Li_le_Mi 1)
      ((s.marking.Li 1).normalizerMonoidHom (inclusion (s.Mi_normalizes_Li 1) m) x) =
      m * inclusion (s.Li_le_Mi 1) x * m⁻¹ := by
    apply Subtype.ext
    exact normalizerMonoidHom_apply_apply_coe _ _ _
  rw [he,map_mul,map_mul,map_inv,s.pointLargeBlock_residual]

/-- The literal centralizer of L₁/O₂(L₁) inside G₁. -/
@[expose] def pointSupplement : Subgroup G :=
  s.marking.Gi 1 ⊓ ((pCoreNormalizerAction 2 (s.marking.Li 1)).ker).map
    (normalizer (s.marking.Li 1 : Set G)).subtype

omit [Finite G] in
theorem pointSupplement_le_point : s.pointSupplement ≤ s.marking.Gi 1 := inf_le_left

variable (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
  (structural : Structural1222At KnownSimple.IsKnownSimple T)
include h structural

set_option backward.isDefEq.respectTransparency false in
/-- The full point group acts innerly on the intrinsic point-residual quotient. -/
theorem point_group_acts_inner (x : s.marking.Gi 1) :
    ∃ y : normalizer (s.marking.Li 1 : Set G), (y : G) = x ∧
      pCoreNormalizerAction 2 (s.marking.Li 1) y ∈
        MulAut.innerSubgroup (s.marking.Li 1 ⧸ pCore 2 (s.marking.Li 1)) := by
  have hn := (normal_subgroupOf_iff_le_normalizer (s.marking.Li_le_Gi 1)).mp
    (s.point_component_normal_from_source h structural).2
  let f := (pCoreNormalizerOuterAction 2 (s.marking.Li 1)).comp (inclusion hn)
  let S := T.subtype s.sylow_le_G₁
  have hSK : (S : Subgroup (s.marking.Gi 1)) ≤ f.ker := by
    intro t ht
    apply (QuotientGroup.eq_one_iff _).mpr
    exact s.point_normalizer_acts_inner ⟨t,le_inf le_sup_right s.sylow_le_G₁ ht⟩
  have hc : Nat.card (MulAut.Outer (s.marking.Li 1 ⧸ pCore 2 (s.marking.Li 1))) = 2 := by
    rw [Nat.card_congr (MulAut.outerCongr (s.marking.LiCoreEquiv 1 (.inl rfl))).toEquiv]
    exact Matrix.PSL3Two.card_outer_of_card_two (by simp)
  have hd : f.ker.index ∣ 2 := by
    rw [index_ker]
    have hd := card_subgroup_dvd_card f.range
    rw [hc] at hd
    exact hd
  have hk : f.ker = ⊤ := by
    apply index_eq_one.mp
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
    · exact he
    · have hd := index_dvd_of_le hSK
      rw [he] at hd
      exact (S.not_dvd_index hd).elim
  refine ⟨inclusion hn x,rfl,?_⟩
  apply (QuotientGroup.eq_one_iff _).mp
  exact (show x ∈ f.ker from hk ▸ mem_top x)

/-- The source factorization G₁=L₁X, with X the actual quotient centralizer. -/
theorem point_group_eq_residual_sup_supplement :
    s.marking.Gi 1 = s.marking.Li 1 ⊔ s.pointSupplement := by
  apply le_antisymm _ (sup_le (s.marking.Li_le_Gi 1) s.pointSupplement_le_point)
  intro x hx
  obtain ⟨y,hy,hinner⟩ := s.point_group_acts_inner h structural ⟨x,hx⟩
  obtain ⟨q,hq⟩ := hinner
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (s.marking.Li 1)) q
  let lN : normalizer (s.marking.Li 1 : Set G) :=
    ⟨l,(s.marking.Li 1).le_normalizer l.property⟩
  have he : pCoreNormalizerAction 2 (s.marking.Li 1) lN =
      pCoreNormalizerAction 2 (s.marking.Li 1) y :=
    (pCoreNormalizerAction_on_component 2 (s.marking.Li 1) l).trans hq
  have hk : lN⁻¹ * y ∈ (pCoreNormalizerAction 2 (s.marking.Li 1)).ker := by
    rw [MonoidHom.mem_ker,map_mul,map_inv,he,inv_mul_cancel]
  have hc : (l : G)⁻¹ * x ∈ s.pointSupplement := by
    refine ⟨(s.marking.Gi 1).mul_mem ((s.marking.Gi 1).inv_mem
      (s.marking.Li_le_Gi 1 l.property)) hx,?_⟩
    exact ⟨lN⁻¹*y,hk,by change (l : G)⁻¹ * (y : G) = _; rw [hy]⟩
  have hm := (s.marking.Li 1 ⊔ s.pointSupplement).mul_mem
    (mem_sup_left l.property) (mem_sup_right hc)
  simpa only [mul_inv_cancel_left] using hm

/-- Point escape passes to the source's centralizer-modulo-core supplement. -/
theorem pointSupplement_not_le_M (hout : ¬ s.marking.Gi 1 ≤ s.marking.M) :
    ¬ s.pointSupplement ≤ s.marking.M := by
  intro hh
  apply hout
  rw [s.point_group_eq_residual_sup_supplement h structural]
  exact sup_le ((s.marking.Li_le_L 1).trans L.le_normalizer) hh

/-- Finite descent selects the original H-star member inside XT. -/
theorem exists_HStar_in_pointSupplement
    (hout : ¬ s.marking.Gi 1 ≤ s.marking.M) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M ∧
      H ≤ s.pointSupplement ⊔ (T : Subgroup G) ∧ H ≤ s.marking.Gi 1 := by
  let J := s.pointSupplement ⊔ (T : Subgroup G)
  have hJG : J ≤ s.marking.Gi 1 := sup_le s.pointSupplement_le_point s.sylow_le_G₁
  have h1J : s.marking.Vi 1 ≤ J :=
    ((s.marking.subspace_le _).trans D.le_sylow).trans le_sup_right
  let := D.elementary
  let : IsElementaryAbelian 2 (s.marking.Vi 1) :=
    IsElementaryAbelian.of_le (s.marking.subspace_le _)
  have hJcore : J ∈ Chapter1.H G := by
    intro hb
    have hc := le_pCoreIn_of_normalizes
      (IsElementaryAbelian.isPGroup 2 (s.marking.Vi 1)) h1J hJG
    change J.pCoreIn 2 = ⊥ at hb
    have he := bot_unique (hb ▸ hc)
    have hn := s.marking.card_V₁
    rw [he,card_bot] at hn
    contradiction
  have hJM : ¬ J ≤ s.marking.M := fun hh =>
    s.pointSupplement_not_le_M h structural hout (le_sup_left.trans hh)
  obtain ⟨H,hHJ,hH⟩ := exists_minimal_le_of_wellFoundedLT
    (fun A : Subgroup G => A ∈ Chapter1.HOver G (T : Set G) ∧ ¬ A ≤ s.marking.M)
    J ⟨⟨hJcore,show (T : Subgroup G) ≤ J from le_sup_right⟩,hJM⟩
  exact ⟨H,hH,hHJ,hHJ.trans hJG⟩

/-- The same selected H has the source generation and Hall-three conclusions,
and an actual conjugate of the original V escapes its two-core. -/
theorem exists_pointSupplement_HStar_with_source_data
    (hout : ¬ s.marking.Gi 1 ≤ s.marking.M) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M ∧
      H ≤ s.pointSupplement ⊔ (T : Subgroup G) ∧ H ≤ s.marking.Gi 1 ∧
      ChapterE.generationParameter H = 2 ∧
      (∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ H ⊓ s.marking.M ∧
        IsHallSubgroup oddPrimes (C.subgroupOf (H ⊓ s.marking.M)) ∧ IsPGroup 3 C) ∧
      ∃ g : G, V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
        V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) ∧
        ¬ V.map (MulAut.conj g).toMonoidHom ≤ H.pCoreIn 2 := by
  obtain ⟨H,hH,hHX,hHG⟩ := s.exists_HStar_in_pointSupplement h structural hout
  have hd := (s.exteriorFusion_from_source h structural).generation_two_hall_three H hH hHG
  obtain ⟨g,hAT,_,hAC,hescape⟩ := s.exists_conjugate_escaping_HStar_core h structural hH
  exact ⟨H,hH,hHX,hHG,hd.1,hd.2,g,hAT,hAC,hescape⟩

/-- The source quotient-centralizer is normal in the original point group. -/
theorem point_group_normalizes_supplement :
    s.marking.Gi 1 ≤ normalizer (s.pointSupplement : Set G) := by
  have hn := (normal_subgroupOf_iff_le_normalizer (s.marking.Li_le_Gi 1)).mp
    (s.point_component_normal_from_source h structural).2
  let f := (pCoreNormalizerAction 2 (s.marking.Li 1)).comp (inclusion hn)
  have he : s.pointSupplement = f.ker.map (s.marking.Gi 1).subtype :=
    pCoreActionKernelIn_eq_map_ker 2 (s.marking.Li 1) (s.marking.Gi 1) hn
  have hnormal : (s.pointSupplement.subgroupOf (s.marking.Gi 1)).Normal := by
    rw [he]
    change ((f.ker.map (s.marking.Gi 1).subtype).comap (s.marking.Gi 1).subtype).Normal
    rw [comap_map_eq_self_of_injective (s.marking.Gi 1).subtype_injective]
    infer_instance
  exact (normal_subgroupOf_iff_le_normalizer s.pointSupplement_le_point).mp hnormal

set_option backward.isDefEq.respectTransparency false in
omit structural in
/-- The quotient-centralizer consumes at most one of the point group's two odd ranks. -/
theorem pointSupplement_three_rank_le_one : primeRank 3 s.pointSupplement ≤ 1 := by
  have hz : Nat.card (center (s.marking.Li 1 ⧸ pCore 2 (s.marking.Li 1))) = 1 := by
    rw [Nat.card_congr (centerCongr (s.marking.LiCoreEquiv 1 (.inl rfl))).toEquiv]
    change Nat.card (center SL(3, ZMod 2)) = 1
    rw [Matrix.PSL3Two.center_eq_bot,card_bot]
  have hr := pCoreActionKernelIn_rank_add_le (s.marking.Li 1) (s.marking.Gi 1)
    (by decide : Odd 3) (s.marking.Li_le_Gi 1) (by rw [hz]; exact Nat.coprime_one_right 3)
  have hL : 0 < primeRank 3 (s.marking.Li 1) := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup,
      primeRank_congr 3 (s.marking.LiCoreEquiv 1 (.inl rfl))]
    apply Nat.pos_of_ne_zero
    intro he
    have hh := PrimeRank.eq_zero_iff_not_dvd_card.mp he
    exact hh (by change 3 ∣ Nat.card SL(3, ZMod 2); rw [Matrix.PSL3Two.card_SL]; decide)
  have hG := (h.simpleQTKE.twoLocal_sqtk (s.marking.Gi_twoLocal 1 (.inl rfl))).stronglyQuasithin
    3 (by decide) (by decide)
  change primeRank 3 s.pointSupplement + primeRank 3 (s.marking.Li 1) ≤ _ at hr
  omega

/-- The original H inside XT has its whole embedded two-residual inside X. -/
theorem HStar_residual_le_pointSupplement {H : Subgroup G}
    (hHX : H ≤ s.pointSupplement ⊔ (T : Subgroup G)) :
    (pResidual 2 H).map H.subtype ≤ s.pointSupplement := by
  apply le_of_isPPerfect_of_le_sup_of_normalizes _ _ (T : Subgroup G)
    (isPPerfect_embedded_pResidual_of_finite 2 H) T.isPGroup'
    (s.sylow_le_G₁.trans (s.point_group_normalizes_supplement h structural))
  exact (map_subtype_le _).trans hHX

/-- Adjoining the original Sylow adds no odd rank to the selected H. -/
theorem HStar_in_pointSupplement_three_rank_le_one {H : Subgroup G}
    (hHX : H ≤ s.pointSupplement ⊔ (T : Subgroup G)) : primeRank 3 H ≤ 1 := by
  have hr : primeRank 3 ((pResidual 2 H).map H.subtype) = primeRank 3 H := by
    rw [←primeRank_congr 3 ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective),
      ResidualCentralizerRank.primeRank_residual (by decide : Nat.Coprime 2 3)]
  rw [←hr]
  exact (primeRank_mono 3 (s.HStar_residual_le_pointSupplement h structural hHX)).trans
    (s.pointSupplement_three_rank_le_one h)

/-- The nontrivial source Hall three-group makes both of these bounds exact. -/
theorem HStar_in_pointSupplement_three_ranks {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHX : H ≤ s.pointSupplement ⊔ (T : Subgroup G)) :
    primeRank 3 H = 1 ∧ primeRank 3 s.pointSupplement = 1 := by
  have hHG : H ≤ s.marking.Gi 1 := hHX.trans
    (sup_le s.pointSupplement_le_point s.sylow_le_G₁)
  obtain ⟨_,C,hC,hCH,_,hC3⟩ :=
    (s.exteriorFusion_from_source h structural).generation_two_hall_three H hH hHG
  have hc : 3 ∣ Nat.card C := hC3.card_eq_or_dvd.resolve_left
    (fun he => hC ((eq_bot_iff_card C).mpr he))
  have hHpos : 0 < primeRank 3 H := by
    apply Nat.pos_of_ne_zero
    intro he
    exact PrimeRank.eq_zero_iff_not_dvd_card.mp he
      (hc.trans (card_dvd_of_le (hCH.trans inf_le_left)))
  have hrH := s.HStar_in_pointSupplement_three_rank_le_one h structural hHX
  have heH : primeRank 3 H = 1 := by omega
  have hRX := primeRank_mono 3 (s.HStar_residual_le_pointSupplement h structural hHX)
  rw [←primeRank_congr 3 ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective),
    ResidualCentralizerRank.primeRank_residual (by decide : Nat.Coprime 2 3),heH] at hRX
  exact ⟨heH,Nat.le_antisymm (s.pointSupplement_three_rank_le_one h) hRX⟩

omit h structural in
/-- The original first-node residual is in this same quotient-centralizer. -/
theorem Y_le_pointSupplement : s.Y ≤ s.pointSupplement := by
  have hYM : s.Y ≤ s.marking.Mi 1 := (map_subtype_le _).trans s.P_le_M₁
  exact le_pCoreActionKernelIn_of_commutator 2 (s.marking.Li 1) (s.marking.Gi 1) s.Y
    (hYM.trans inf_le_right) (hYM.trans (s.Mi_normalizes_Li 1))
    ((commutator_comm _ _).le.trans s.Y_point_commutator_le_point_core)

/-- Apply the rank calculation to the actual H selected by point escape. -/
theorem exists_rank_one_HStar_in_pointSupplement
    (hout : ¬ s.marking.Gi 1 ≤ s.marking.M) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M ∧
      H ≤ s.pointSupplement ⊔ (T : Subgroup G) ∧ H ≤ s.marking.Gi 1 ∧
      primeRank 3 H = 1 ∧ primeRank 3 s.pointSupplement = 1 ∧
      (pResidual 2 H).map H.subtype ≤ s.pointSupplement := by
  obtain ⟨H,hH,hHX,hHG⟩ := s.exists_HStar_in_pointSupplement h structural hout
  obtain ⟨hrH,hrX⟩ := s.HStar_in_pointSupplement_three_ranks h structural hH hHX
  exact ⟨H,hH,hHX,hHG,hrH,hrX,s.HStar_residual_le_pointSupplement h structural hHX⟩

omit structural in
/-- Full cubic rank and the literal outer group give the original L prime-to-three index in M. -/
theorem component_index_coprime_three_in_M :
    Nat.Coprime 3 (L.subgroupOf s.marking.M).index := by
  let N := s.marking.M
  let A := L.subgroupOf N
  let : A.Normal := (normal_subgroupOf_iff_le_normalizer
    (show L ≤ N from L.le_normalizer)).mpr le_rfl
  let e : (A ⧸ pCore 2 A) ≃* SL(5, ZMod 2) :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe L.le_normalizer)
      (pCore_map_iso 2 _)).trans s.marking.quotientEquiv
  have hA := h.toHypothesis1221.sylow_normalized_component D.sylow_normalizes_component
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hz : center (A ⧸ pCore 2 A) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have he : e x = 1 :=
      (BinaryLinear.OuterCyclic.binary_center_eq_bot (by decide : 0 < 5)).le
        ((centerCongr e) ⟨x,hx⟩).property
    exact e.map_eq_one_iff.mp he
  have hr : 2 ≤ primeRank 3 (A ⧸ pCore 2 A) := by
    rw [primeRank_congr 3 e]
    exact BinaryLinear.SmallCubicRank.five
  have ho : IsPGroup 2 (MulAut.Outer (A ⧸ pCore 2 A)) :=
    (BinaryLinear.OuterCyclic.sl_outer_isTwoGroup (.inr rfl)).of_equiv
      (MulAut.outerCongr e).symm
  apply cComponent_index_coprime_three_of_quotient A hA hz hr
    ((h.simpleQTKE.twoLocal_sqtk (h.toHypothesis1221.sylow_normalized_maximal_unique D.sylow_normalizes_component
        (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
        (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))).1.1).stronglyQuasithin
      3 (by decide) (by decide))
  obtain ⟨n,hn⟩ := ho.exists_card_eq
  rw [hn]
  exact (by decide : Nat.Coprime 3 2).pow_right n

omit structural in
/-- Every actual three-subgroup in M lies in the original component L. -/
theorem three_subgroup_le_component {C : Subgroup G}
    (hCM : C ≤ s.marking.M) (hC : IsPGroup 3 C) : C ≤ L := by
  let N := s.marking.M
  let A := L.subgroupOf N
  let : A.Normal := (normal_subgroupOf_iff_le_normalizer
    (show L ≤ N from L.le_normalizer)).mpr le_rfl
  have hres : primeToResidual 3 N ≤ A :=
    primeToResidual_le A (s.component_index_coprime_three_in_M h)
  intro c hc
  obtain ⟨n,hn⟩ := hC ⟨c,hc⟩
  have hp : (⟨c,hCM hc⟩ : N) ^ (3^n) = 1 := by
    apply Subtype.ext
    exact congrArg (fun x : C => (x : G)) hn
  exact hres (mem_primeToResidual_of_pow hp)

/-- The source Hall subgroup of the selected H lies in the actual M₁. -/
theorem exists_pointSupplement_HStar_hall_in_point_normalizer
    (hout : ¬ s.marking.Gi 1 ≤ s.marking.M) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M ∧
      H ≤ s.pointSupplement ⊔ (T : Subgroup G) ∧ H ≤ s.marking.Gi 1 ∧
      primeRank 3 H = 1 ∧ ChapterE.generationParameter H = 2 ∧
      ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ H ⊓ s.marking.M ∧ C ≤ s.marking.Mi 1 ∧
        IsHallSubgroup oddPrimes (C.subgroupOf (H ⊓ s.marking.M)) ∧ IsPGroup 3 C := by
  obtain ⟨H,hH,hHX,hHG⟩ := s.exists_HStar_in_pointSupplement h structural hout
  obtain ⟨hrH,_⟩ := s.HStar_in_pointSupplement_three_ranks h structural hH hHX
  obtain ⟨hgen,C,hC,hCH,hHall,hC3⟩ :=
    (s.exteriorFusion_from_source h structural).generation_two_hall_three H hH hHG
  have hCL : C ≤ L := s.three_subgroup_le_component h (hCH.trans inf_le_right) hC3
  have hCG : C ≤ s.marking.Gi 1 := (hCH.trans inf_le_left).trans hHG
  exact ⟨H,hH,hHX,hHG,hrH,hgen,C,hC,hCH,le_inf (hCL.trans le_sup_left) hCG,hHall,hC3⟩

/-- A three-subgroup of XT has trivial two-group quotient image and lies in X. -/
theorem three_subgroup_le_pointSupplement {C : Subgroup G}
    (hCX : C ≤ s.pointSupplement ⊔ (T : Subgroup G)) (hC : IsPGroup 3 C) :
    C ≤ s.pointSupplement := by
  have hp : IsPPerfect 2 C := by
    apply (pResidual_eq_top_iff 2 C).mp
    apply top_unique
    intro c _
    obtain ⟨n,hn⟩ := hC c
    exact mem_pResidual_of_orderOf_coprime
      (((by decide : Nat.Coprime 2 3).pow_right n).of_dvd_right
        (orderOf_dvd_of_pow_eq_one hn))
  exact le_of_isPPerfect_of_le_sup_of_normalizes C s.pointSupplement (T : Subgroup G)
    hp T.isPGroup' (s.sylow_le_G₁.trans (s.point_group_normalizes_supplement h structural)) hCX

omit h structural in
set_option backward.isDefEq.respectTransparency false in
private theorem pointLargeBlock_conjugation (m : s.marking.Mi 1) (l : s.marking.Li 1) :
    s.pointLargeBlock (inclusion (s.Li_le_Mi 1)
      ((s.marking.Li 1).normalizerMonoidHom (inclusion (s.Mi_normalizes_Li 1) m) l)) =
      s.pointLargeBlock m * s.pointLargeBlock (inclusion (s.Li_le_Mi 1) l) *
        (s.pointLargeBlock m)⁻¹ := by
  have he : inclusion (s.Li_le_Mi 1)
      ((s.marking.Li 1).normalizerMonoidHom (inclusion (s.Mi_normalizes_Li 1) m) l) =
      m * inclusion (s.Li_le_Mi 1) l * m⁻¹ := by
    apply Subtype.ext
    exact normalizerMonoidHom_apply_apply_coe _ _ _
  rw [he,map_mul,map_mul,map_inv]

omit h structural in
set_option backward.isDefEq.respectTransparency false in
private theorem pointLargeBlock_eq_one_of_mem_supplement
    (m : s.marking.Mi 1) (hm : (m : G) ∈ s.pointSupplement) : s.pointLargeBlock m = 1 := by
  obtain ⟨y,hy,he⟩ := hm.2
  have he' : y = inclusion (s.Mi_normalizes_Li 1) m := Subtype.ext he
  have ha : pCoreNormalizerAction 2 (s.marking.Li 1)
      (inclusion (s.Mi_normalizes_Li 1) m) = 1 := he' ▸ hy
  apply (show center SL(3, ZMod 2) = ⊥ from Matrix.PSL3Two.center_eq_bot).le
  apply mem_center_iff.mpr
  intro a
  obtain ⟨l,rfl⟩ := s.marking.LiLinearHom_surjective 1 (.inl rfl) a
  have heq := DFunLike.congr_fun ha (QuotientGroup.mk' (pCore 2 (s.marking.Li 1)) l)
  rw [pCoreNormalizerAction_mk] at heq
  have hh := congrArg (s.marking.LiCoreEquiv 1 (.inl rfl)) heq
  change s.marking.LiCoreEquiv 1 (.inl rfl) (QuotientGroup.mk' _
    ((s.marking.Li 1).normalizerMonoidHom (inclusion (s.Mi_normalizes_Li 1) m) l)) =
    s.marking.LiCoreEquiv 1 (.inl rfl) (QuotientGroup.mk' _ l) at hh
  rw [s.marking.LiCoreEquiv_mk,s.marking.LiCoreEquiv_mk] at hh
  simp only [←s.pointLargeBlock_residual] at hh ⊢
  rw [s.pointLargeBlock_conjugation] at hh
  have hc := congrArg (fun x => x * s.pointLargeBlock m) hh
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hc.symm

omit h structural in
/-- The original M₁ block map embeds every cubic subgroup in X into SL₂(2). -/
theorem three_subgroup_card_dvd_three_of_point_supplement {C : Subgroup G}
    (hCM : C ≤ s.marking.Mi 1) (hCX : C ≤ s.pointSupplement) (hC : IsPGroup 3 C) :
    Nat.card C ∣ 3 := by
  let q := s.M₁CoreEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (s.marking.Mi 1)))
  let f : C →* SL(2, ZMod 2) := (MonoidHom.fst _ _).comp (q.comp (inclusion hCM))
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro c hc
    have hlarge : (q (inclusion hCM c)).2 = 1 :=
      s.pointLargeBlock_eq_one_of_mem_supplement (inclusion hCM c) (hCX c.property)
    have hq : q (inclusion hCM c) = 1 := Prod.ext hc hlarge
    have hcore : inclusion hCM c ∈ pCore 2 (s.marking.Mi 1) := by
      apply (QuotientGroup.eq_one_iff _).mp
      apply s.M₁CoreEquiv.injective
      exact hq.trans (map_one _).symm
    have hx : (c : G) ∈ (s.marking.Mi 1).pCoreIn 2 := ⟨inclusion hCM c,hcore,rfl⟩
    exact Subtype.ext (disjoint_def.mp
      (hC.disjoint_of_coprime (isPGroup_pCoreIn 2 (s.marking.Mi 1)) (by decide)) c.property hx)
  have hd := card_dvd_of_injective f hf
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  rw [Nat.card_congr e.toEquiv] at hd
  have he : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  rw [he] at hd
  obtain ⟨n,hn⟩ := hC.exists_card_eq
  have hcop : Nat.Coprime (Nat.card C) 2 := by
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_left n
  exact hcop.dvd_mul_left.mp hd

/-- The actual Hall subgroup in the chosen supplement has order exactly three. -/
theorem pointSupplement_HStar_hall_card_three {H C : Subgroup G}
    (hHX : H ≤ s.pointSupplement ⊔ (T : Subgroup G))
    (hC : C ≠ ⊥) (hCH : C ≤ H ⊓ s.marking.M) (hC3 : IsPGroup 3 C) : Nat.card C = 3 := by
  have hCX := s.three_subgroup_le_pointSupplement h structural
    ((hCH.trans inf_le_left).trans hHX) hC3
  have hCL := s.three_subgroup_le_component h (hCH.trans inf_le_right) hC3
  have hCM : C ≤ s.marking.Mi 1 :=
    le_inf (hCL.trans le_sup_left) (hCX.trans s.pointSupplement_le_point)
  rcases (Nat.dvd_prime Nat.prime_three).mp
    (s.three_subgroup_card_dvd_three_of_point_supplement hCM hCX hC3) with he | he
  · exact (hC ((eq_bot_iff_card C).mpr he)).elim
  · exact he

omit h structural in
/-- The supplement's elements in M₁ lie in the original first-node parabolic. -/
theorem pointSupplement_inf_point_normalizer_le_P :
    s.pointSupplement ⊓ s.marking.Mi 1 ≤ s.P := by
  intro x hx
  let m : s.marking.Mi 1 := ⟨x,hx.2⟩
  have he := s.pointLargeBlock_eq_one_of_mem_supplement m hx.1
  apply (s.mem_P_iff_actor ⟨x,hx.2.1⟩).mpr
  apply (mem_firstNode_iff_large_upper (s.localJoinActor 1 (.inl rfl) m)).mpr
  change (s.pointLargeBlock m).val.IsUpperTriangular
  rw [he]
  exact Matrix.blockTriangular_one

/-- A selected H contains P: its nontrivial cubic Hall subgroup escapes T,
whose index in the same P is three. -/
theorem P_le_HStar_in_pointSupplement {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHX : H ≤ s.pointSupplement ⊔ (T : Subgroup G)) : s.P ≤ H := by
  have hHG : H ≤ s.marking.Gi 1 := hHX.trans
    (sup_le s.pointSupplement_le_point s.sylow_le_G₁)
  obtain ⟨_,C,hC,hCH,_,hC3⟩ :=
    (s.exteriorFusion_from_source h structural).generation_two_hall_three H hH hHG
  have hCX := s.three_subgroup_le_pointSupplement h structural
    ((hCH.trans inf_le_left).trans hHX) hC3
  have hCL := s.three_subgroup_le_component h (hCH.trans inf_le_right) hC3
  have hCP : C ≤ s.P := (le_inf hCX
    (le_inf (hCL.trans le_sup_left) (hCX.trans s.pointSupplement_le_point))).trans
      s.pointSupplement_inf_point_normalizer_le_P
  let S := T.subtype s.sylow_le_P
  let B := H.subgroupOf s.P
  have hSB : (S : Subgroup s.P) ≤ B := fun x hx => hH.1.1.2 hx
  have hi : (S : Subgroup s.P).relIndex B * B.index = 3 :=
    (relIndex_mul_index hSB).trans s.sylow_relIndex_P
  rcases Nat.prime_mul_iff.mp (hi ▸ Nat.prime_three) with ⟨_,hb⟩ | ⟨_,hr⟩
  · exact subgroupOf_eq_top.mp (index_eq_one.mp hb)
  · have hBS : B ≤ (S : Subgroup s.P) := relIndex_eq_one.mp hr
    have hCT : C ≤ (T : Subgroup G) := by
      intro x hx
      exact hBS (show (⟨x,hCP hx⟩ : s.P) ∈ B from hCH hx |>.1)
    have hd := hC3.disjoint_of_coprime T.isPGroup' (by decide)
    exact (hC (bot_unique (fun x hx => disjoint_def.mp hd hx (hCT hx)))).elim

/-- The source point-parabolic incidence is now derived for the selected H. -/
theorem point_parabolic_le_residual_sup_HStar {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHX : H ≤ s.pointSupplement ⊔ (T : Subgroup G)) :
    s.marking.Mi 1 ≤ s.marking.Li 1 ⊔ H := by
  rw [s.M₁_eq_P_sup_point_residual]
  exact sup_le ((s.P_le_HStar_in_pointSupplement h structural hH hHX).trans le_sup_right)
    le_sup_left

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
