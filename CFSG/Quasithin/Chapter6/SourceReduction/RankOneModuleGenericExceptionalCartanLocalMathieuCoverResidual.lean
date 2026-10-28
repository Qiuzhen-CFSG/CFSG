module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalMathieu
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicJankoMathieu
public import CFSG.Quasithin.ChapterF.Section01.RankOneMathieuCover
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicFiniteContainers

/-!
# The original residual inside the central triple cover of M₂₂

The five-square-free order of the actual containing quotient forces the
selected seed to be the whole residual. The original E.2.2 alternatives,
restricted to the same full Sylow, leave a rank-one quotient: the diagram
SL₃(4) row is excluded by its actual local embedding in the central M₂₂
cover. The central-cover Mathieu theorem then gives PSL₂(4), and the
original right Hall subgroup has order three.

The central cubic kernel and both original Hall conditions are retained.
The companion action argument uses these conclusions to exclude this
containing row; no exhaustive component classification is asserted here.
Source: Aschbacher--Smith 5.1.12--13, printed pp.635--637, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Chapter1.Section02.LocalModels
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

private theorem mathieu_cover_transport {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (hm : IsM22Cover Y) : IsM22Cover X := by
  let := hm.1
  let ec := QuotientGroup.congr (center X) (center Y) e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)
  exact ⟨IsQuasisimple.of_mulEquiv e.symm,
    ⟨(centerCongr e).trans hm.2.1.some⟩,⟨ec.trans hm.2.2.some⟩⟩

private theorem sl_transport {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) {d q : ℕ} (h : IsSL Y d q) : IsSL X d q := by
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := h
  exact ⟨F,inferInstance,inferInstance,hF,⟨e.trans a⟩⟩

/-- The literal residual quotient in a central M₂₂ covering container is PSL₂(4). -/
theorem residual_section_of_mathieu_cover
    {T : Sylow 2 G} {L W H A Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (hR : residual H ∈ Chapter1.L G (T : Subgroup G))
    (C : Subgroup Y) (hC : C.IsCComponent)
    (hRC : residual H ≤ C.map Y.subtype)
    (hm : IsM22Cover (C ⧸ pCore 2 C)) :
    ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 := by
  have hR' : (pResidual 2 H).IsCComponent := by
    have hh := hR.1
    rw [residual_sup_sylow T H hH.1.1.2] at hh
    simpa only [residual,subgroupOf,comap_map_eq_self_of_injective H.subtype_injective] using hh
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hY.2
  have hTY := hH.1.1.2.trans hY.2
  let q := QuotientGroup.mk' (pCore 2 Y)
  let S := T.subtype hTY
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))
  let Rbar := ((residual H).subgroupOf Y).map q
  let Cbar := C.map q
  have hl : (residual H).subgroupOf Y ∈ Chapter1.L Y (S : Subgroup Y) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTY hRY).mp ⟨hRY,hR⟩
  have hlq : Rbar ∈ ChapterA.Section03.localCComponents P :=
    Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hl
  have hRC' : (residual H).subgroupOf Y ≤ C := by
    have hh := comap_mono (f := Y.subtype) hRC
    simpa only [subgroupOf,comap_map_eq_self_of_injective Y.subtype_injective] using hh
  have hle : Rbar ≤ Cbar := map_mono hRC'
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isNilpotent
  obtain ⟨Q,hQ,hU⟩ := ChapterA.Section03.SourceEmbeddings.exists_local_sylow_restriction
    P hlq hle (hC.map_quotient (pCore 2 Y)).subnormal
  let U := Rbar.subgroupOf Cbar
  have hn : (P : Subgroup (Y ⧸ pCore 2 Y)) ≤ normalizer (Rbar : Set _) := by
    apply (map_mono (f := q) ?_).trans (le_normalizer_map q)
    rw [←subgroupOf_normalizer_eq hRY]
    exact comap_mono (hH.1.1.2.trans (le_normalizer_residual H))
  have hnU : (Q : Subgroup Cbar) ≤ normalizer (U : Set Cbar) := by
    rw [hQ,←subgroupOf_normalizer_eq hle]
    exact comap_mono hn
  let r := q.subgroupMap ((residual H).subgroupOf Y)
  have hr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let e₀ := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let e₁ := e₀.trans (subgroupOfEquivOfLe hRY).symm
  let e₂ := r.pCoreQuotientEquiv (q.subgroupMap_surjective _) hr
  let e₃ := (subgroupOfEquivOfLe hle).symm
  let eR : ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃* (U ⧸ pCore 2 U) :=
    (QuotientGroup.congr _ _ e₁ (pCore_map_iso 2 e₁)).trans
      (e₂.trans (QuotientGroup.congr _ _ e₃ (pCore_map_iso 2 e₃)))
  let eC : Cbar ≃* (C ⧸ pCore 2 C) := (cComponentTwoCoreQuotientEquiv hC).symm
  have hmC : IsM22Cover Cbar := mathieu_cover_transport eC hm
  have hd : Nat.card ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ∣ 1330560 := by
    rw [Nat.card_congr eR.toEquiv]
    have hh := (card_quotient_dvd_card (pCore 2 U)).trans U.card_subgroup_dvd_card
    rw [Nat.card_congr eC.toEquiv] at hh
    rw [card_eq_card_quotient_mul_card_subgroup (center (C ⧸ pCore 2 C)),
      Nat.card_congr hm.2.2.some.toEquiv,Sporadic.Mathieu.m22_order,
      Nat.card_congr hm.2.1.some.toEquiv] at hh
    simpa using hh
  have hmodel : ChapterF.Source.IsRankOneModel
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) := by
    rcases Global.right_source_cases h.qtke h.sylow_normalizes hH hgen with hs | hs
    · obtain ⟨K,f,hK,hqs,_,_,hc | hc⟩ := hs
      · have hKR : K = pResidual 2 H := by
          apply hK.eq_of_le hR'
          let := hK.perfect
          apply le_sInf
          rintro N ⟨hn,hN⟩
          let := hn
          let : Group.IsNilpotent (H ⧸ N) := hN.isNilpotent
          exact (le_solvableResidual_of_isPerfect K).trans (solvableResidual_le_of_solvable_quotient N)
        subst K
        obtain ⟨t,_,hne,_⟩ := hc.1.exchanged_product
        exact (hne (mem_normalizer_iff_map_conj_eq.mp
          (show t⁻¹ ∈ normalizer (pResidual 2 H : Set H) by
            rw [normalizer_eq_top]; exact mem_top _)).symm).elim
      · have he : K = pResidual 2 H :=
          BenderHall.SingleClauses.component_eq_residual (S := T.subtype hH.1.1.2) hc.1 hK
        subst K
        have hO : pCore 2 H ≤ sourceKernel ((normalizer (L : Set G)).subgroupOf H) := by
          apply normal_le_normalCore.mpr
          exact (pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2)).trans
            (comap_mono h.sylow_normalizes)
        exact Prime.single_bender_component_quotient hK hqs hO hc.1 hc.2
    · obtain ⟨K,f,hK,hqs,_,hf,hc,hm⟩ := hs
      have hmodels := Prime.diagram_source_residual_quotient h.sylow_normalizes hH.1.1.2 hK hqs hc hf hm
      have hf2 := Prime.diagram_finite_order hf (by simp [Prime.finiteOrders]) hd hmodels
      subst f
      rcases hmodels with hlin | hsl | hsp
      · exact (not_linear_four_residual_of_escape h.qtke h.sylow_normalizes hH hY hescape hlin).elim
      · exact (Prime.m22Cover_not_sl3_four Q U hU hnU
          (sl_transport eR.symm hsl) hmC).elim
      · obtain ⟨F,_,_,hF,⟨a⟩⟩ := hsp
        let : Fintype F := Fintype.ofFinite F
        let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
          (by simpa only [Nat.card_eq_fintype_card] using hF)
        let b := a.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
        rw [Nat.card_congr b.toEquiv,Theory.SpecificGroups.SymplecticFour.card_sp,hF] at hd
        norm_num at hd
  have hc : Nat.card (center Cbar) = 3 := by
    rw [Nat.card_congr hmC.2.1.some.toEquiv]
    simp
  exact (ChapterF.Source.MathieuLocal.rankOne_quotient_four_of_central_cover
    hmC.2.2.some hc Q U hU hnU (hmodel.of_equiv eR.symm)).of_mulEquiv eR

/-- On the same normal component, the seed is the residual and the right Hall is cubic. -/
theorem normal_mathieu_cover_residual_and_hall
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : IsM22Cover (C ⧸ pCore 2 C)) :
    K = residual H ∧
      ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∧
      Nat.card B = 3 := by
  have hKR : K = residual H := by
    apply seed_eq_residual_of_normal_twentyFive_free_container h.qtke hK hKT horbit
      hY hescape C hKC
    rw [card_eq_card_quotient_mul_card_subgroup (center (C ⧸ pCore 2 C)),
      Nat.card_congr hm.2.2.some.toEquiv,Sporadic.Mathieu.m22_order,
      Nat.card_congr hm.2.1.some.toEquiv]
    norm_num
  have hfour := residual_section_of_mathieu_cover h hH hgen hY hescape
    (hKR ▸ hK) C hC (hKR ▸ hKC) hm
  have hA5 : Nonempty ((residual H ⧸ pCore 2 (residual H)) ≃* alternatingGroup (Fin 5)) := by
    let a := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
    let eq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
    obtain ⟨F,_,_,hF,⟨b⟩⟩ := hfour
    exact ⟨eq.symm.trans (b.trans
      (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some)⟩
  exact ⟨hKR,hfour,right_hall_card_three_of_residual_A5 h hH hgen c hA5⟩


end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
