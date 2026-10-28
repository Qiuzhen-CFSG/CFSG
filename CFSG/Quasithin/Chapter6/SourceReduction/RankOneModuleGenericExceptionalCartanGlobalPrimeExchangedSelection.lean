module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeExchangedGeometry
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeConstructionGeometry
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeUnitarySelection
public import CFSG.Quasithin.ChapterF.Section01.CoreQuotient

/-!
# Selecting the actual exchanged right factor before normalization

The original H-component C is embedded as R = C.map H.subtype. The exchanged
source geometry gives S ∩ K = T ∩ K, S-normalization of R, the component
normalizer index and the literal right Borel. The original odd Hall B fixes
R because the component normalizer has index two. Hall restriction to the
Borel supplies its product with B ∩ R, completing every field of RightData.

The actual (DS,R) pair consequently satisfies genuine F.1.1 when its two-core
vanishes; otherwise D moves R and N_T(R) has index two in T. Combining this
with the proved single-Bender selection leaves only the diagram source row
for local-pair construction. No marked amalgam recognition, zero-core model
exclusion or final Cartan normalization is asserted here. These remaining
steps belong to qt-d-1222-rankone-cartan-local-to-global.

Source: Aschbacher–Smith 5.1.10–11 and 5.2.2,
printed pp.634–635,646–648 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

private theorem hstar_maximal_eq {T : Sylow 2 G} {L H : Subgroup G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤) :
    ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP =
      (normalizer (L : Set G)).subgroupOf H := by
  let J := ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP
  have hj := ChapterB.minimalParabolicMax_spec (T.subtype hH.1.1.2) hP
  have hTJ : (T : Subgroup G) ≤ J.map H.subtype := by
    have hh := map_mono (f := H.subtype) hj.2
    change ((T : Subgroup G).subgroupOf H).map H.subtype ≤ J.map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hJH : J.map H.subtype < H := by
    have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr hj.1.lt_top
    simpa only [← MonoidHom.range_eq_map,range_subtype] using hh
  apply ChapterE.Section06.FixedPointBounds.ParabolicCartan.maximal_eq_overlap_of_image_le
    H.subtype (T.subtype hH.1.1.2) hP
  · change ((T : Subgroup G).subgroupOf H).map H.subtype ≤ normalizer (L : Set G)
    rw [map_subgroupOf_eq_of_le hH.1.1.2]
    exact hTL
  · simpa only [range_subtype] using hH.1.2
  · exact Chapter3.HStar.proper_overgroup_le T hH hTJ hJH

/-- The original exchanged E.2.2 component supplies all right-side prime-pair geometry. -/
theorem exchanged_source_rightData
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n f : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hgen : C ⊔ (T : Subgroup G).subgroupOf H = ⊤)
    (hc : ExchangedClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    (hm : ExchangedModel ((normalizer (L : Set G)).subgroupOf H) C f) :
    RightData T L H B (C.map H.subtype) := by
  let R := C.map H.subtype
  let S := T.subtype hH.1.1.2
  let M := (normalizer (L : Set G)).subgroupOf H
  have hP := hstar_minimalParabolic_of_generation_gt_one h.sylow_normalizes hH hpar
  have hmax := hstar_maximal_eq h.sylow_normalizes hH hP
  have hX := Chapter3.sqtk_of_mem_H h.qtke hH.1.1.1
  have hc' : ExchangedClauses (ChapterB.minimalParabolicMax S hP) C S := hmax ▸ hc
  have hm' : ExchangedModel (ChapterB.minimalParabolicMax S hP) C f := hmax ▸ hm
  have hSM : (M.pCoreIn 2).map H.subtype = Global.sourceS L H := by
    rw [map_pCoreIn_of_injective 2 M H.subtype H.subtype_injective,subgroupOf_map_subtype]
    rfl
  have hST : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hH.1.1.2
  have hRK : R ≤ residual H := by
    let := hC.perfect
    let := (isPGroup_quotient_pResidual 2 (G := H)).isNilpotent
    exact map_mono ((le_solvableResidual_of_isPerfect C).trans
      (solvableResidual_le_of_solvable_quotient (pResidual 2 H)))
  have hRT : R ⊔ (T : Subgroup G) = H := by
    have hh := congrArg (map H.subtype) hgen
    rwa [Subgroup.map_sup,map_subgroupOf_eq_of_le hH.1.1.2,
      ← MonoidHom.range_eq_map,range_subtype] at hh
  have hSC : Global.sourceS L H ≤ normalizer (R : Set G) := by
    have hh := exchanged_core_normalizes hX S hP hC hgen hc' hm'
    rw [hmax] at hh
    exact hSM ▸ ((map_mono (f := H.subtype) hh).trans (C.le_normalizer_map H.subtype))
  have hSK : Global.sourceS L H ⊓ residual H = (T : Subgroup G) ⊓ residual H := by
    apply le_antisymm (inf_le_inf_right _ (Global.sourceS_le_sylow h.sylow_normalizes hH.1.1.2))
    have hh := exchanged_residual_sylow_le_core hX S hP hC hgen hc' hm'
    rw [hmax] at hh
    have hh' := map_mono (f := H.subtype) hh
    rw [Subgroup.map_inf _ _ _ H.subtype_injective,hST,hSM] at hh'
    exact le_inf hh' inf_le_right
  have hSR : Global.sourceS L H ⊓ R = (T : Subgroup G) ⊓ R := by
    calc
      _ = (Global.sourceS L H ⊓ residual H) ⊓ R := by rw [inf_assoc,inf_eq_right.mpr hRK]
      _ = _ := by rw [hSK,inf_assoc,inf_eq_right.mpr hRK]
  have hi := exchanged_normalizer_index hX S hP hC hgen hc'
  let : (normalizer (C : Set H)).Normal := normal_of_index_eq_two hi
  have hNC : (normalizer (R : Set G)).comap H.subtype = normalizer (C : Set H) := by
    rw [comap_normalizer_eq_of_le_range (by rw [range_subtype];exact map_subtype_le _),
      comap_map_eq_self_of_injective H.subtype_injective]
  have hBC : B ≤ normalizer (R : Set G) := by
    have hBH := c.right_le.trans inf_le_right
    have ho : Odd (Nat.card (B.subgroupOf H)) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hBH).toEquiv,
        ← Nat.card_congr (subgroupOfEquivOfLe c.right_le).toEquiv]
      exact OddHall.odd_hall_odd c.right_hall
    have hq : IsPGroup 2 (H ⧸ normalizer (C : Set H)) := IsPGroup.of_card
      (by rw [← index_eq_card,hi];decide : Nat.card (H ⧸ normalizer (C : Set H)) = 2^1)
    have hh := OddHall.odd_subgroup_le _ (B.subgroupOf H) hq ho
    rw [←hNC] at hh
    exact fun x hx => hh (show (⟨x,hBH hx⟩ : H) ∈ B.subgroupOf H from hx)
  have hind : (normalizingSylow T R).relIndex (T : Subgroup G) ≤ 2 := by
    change ((T : Subgroup G) ⊓ normalizer (R : Set G)).relIndex (T : Subgroup G) ≤ 2
    rw [inf_relIndex_left,←hST,←relIndex_comap,hNC]
    have hd := relIndex_dvd_index_of_normal (normalizer (C : Set H)) (S : Subgroup H)
    rw [hi] at hd
    exact Nat.le_of_dvd (by decide) hd
  obtain ⟨P,hP'⟩ := S.exists_subgroupOf_eq_of_subnormal C hC.subnormal
  have hPC : (P : Subgroup C).map C.subtype = (S : Subgroup H) ⊓ C := by
    rw [hP',subgroupOf_map_subtype]
  have hSyl : ∃ Q : Sylow 2 R, (Q : Subgroup R).map R.subtype = (T : Subgroup G) ⊓ R := by
    let e := C.equivMapOfInjective H.subtype H.subtype_injective
    refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
    change ((P : Subgroup C).map e.toMonoidHom).map R.subtype = _
    rw [map_map]
    change (P : Subgroup C).map (H.subtype.comp C.subtype) = _
    rw [←map_map,hPC,Subgroup.map_inf _ _ _ H.subtype_injective,hST]
  have hb : ChapterF.Source.borel R (Global.sourceS L H) = normalizer (L : Set G) ⊓ R := by
    have hh := congrArg (map H.subtype) (exchanged_component_borel hX S hP hC hgen hc' hm')
    rw [hmax,ChapterF.Source.borel_map_of_ker_le H.subtype C S ⟨P,hPC⟩
      (by rw [H.ker_subtype];exact bot_le),hST,
      Subgroup.map_inf _ _ _ H.subtype_injective,subgroupOf_map_subtype] at hh
    have hRH : R ≤ H := map_subtype_le _
    rw [inf_assoc,inf_eq_right.mpr hRH] at hh
    change R ⊓ normalizer ((Global.sourceS L H ⊓ R : Subgroup G) : Set G) = _
    rw [hSR]
    exact hh
  have hRC : (R.subgroupOf H).IsCComponent := by
    change ((C.map H.subtype).comap H.subtype).IsCComponent
    rwa [comap_map_eq_self_of_injective H.subtype_injective]
  refine ⟨hRK,?_,hRT,?_,hRC.subgroupOf_of_le le_sup_left
    (sup_le (map_subtype_le _) (inf_le_left.trans hH.1.1.2)),hind,hSK,hSC,hBC,?_,
    Global.exchanged_source_factor_quotient hC hc hm,?_⟩
  · exact fun hRM => hH.1.2 (hRT ▸ sup_le hRM h.sylow_normalizes)
  · intro hs
    exact hC.not_isSolvable (by
      let := hs
      exact Group.isSolvable_of_isSolvable_injective
        (f := (C.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom)
        (C.equivMapOfInjective H.subtype H.subtype_injective).injective)
  · rwa [hSR]
  · let U := normalizer (L : Set G) ⊓ R
    have hU : U ≤ Global.intersection L H := le_inf inf_le_left
      (inf_le_right.trans (map_subtype_le _))
    have hBU : B ≤ normalizer (U : Set G) :=
      (le_inf ((c.right_le.trans inf_le_left).trans (normalizer (L : Set G)).le_normalizer)
        hBC).trans inf_normalizer_le_normalizer_inf
    have hh := OddHall.hall_restrict_of_normalizes c.right_hall c.right_le hU hBU
    obtain ⟨P,hP⟩ := hSyl
    obtain ⟨Q,hQ⟩ := P.exists_map_subtype_eq_of_le (show U ≤ R from inf_le_right)
      (hP ▸ le_inf (inf_le_left.trans h.sylow_normalizes) inf_le_right)
    have he := congrArg (map U.subtype) (OddHall.sylow_complement_of_hall Q hh).sup_eq_top
    have hi : B ⊓ U = B ⊓ R := by
      dsimp [U]
      rw [← inf_assoc,inf_eq_left.mpr (c.right_le.trans inf_le_left)]
    rw [Subgroup.map_sup,hQ,hP,subgroupOf_map_subtype,hi,
      ←MonoidHom.range_eq_map,range_subtype] at he
    rw [hb,hSR]
    exact he.symm

/-- The literal exchanged pair has the genuine zero-core amalgam or the index-two moving-factor branch. -/
theorem exchanged_source_prime_pair
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p f : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hd : CartanPrimeActor A H p D)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hgen : C ⊔ (T : Subgroup G).subgroupOf H = ⊤)
    (hc : ExchangedClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    (hm : ExchangedModel ((normalizer (L : Set G)).subgroupOf H) C f) :
    let R := C.map H.subtype
    LocalData T L H B D R ∧
      (((generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) ∨
       ((generated L H D R).pCoreIn 2 ≠ ⊥ ∧ ¬ D ≤ normalizer (R : Set G) ∧
        (normalizingSylow T R).relIndex (T : Subgroup G) = 2)) := by
  let d := (exchanged_source_rightData h hH hpar c hC hgen hc hm).localData h hH c hd
  refine ⟨d,?_⟩
  by_cases hz : (generated L H D (C.map H.subtype)).pCoreIn 2 = ⊥
  · exact Or.inl ⟨hz,d.hypothesisF11 h hH c hd hz⟩
  · exact Or.inr ⟨hz,d.prime_actor_not_normalizes_right h hH c hd hz,
      d.normalizingSylow_index hH.1.1.2 c hd hz⟩

/-- Both the exchanged and single-Bender source rows construct the actual local pair. -/
theorem rankOne_source_localData
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hd : CartanPrimeActor A H p D) (hs : Global.RightRankOneSource T L H) :
    ∃ R : Subgroup G, LocalData T L H B D R := by
  obtain ⟨C,f,hC,hqs,hgen,_,hc | hc⟩ := hs
  · exact ⟨C.map H.subtype,
      (exchanged_source_rightData h hH hpar c hC hgen hc.1 hc.2).localData h hH c hd⟩
  · exact ⟨residual H,(single_bender_prime_pair h hH c hd hC hqs hc.1 hc.2).1⟩

/-- The original E.2.2 dispatcher leaves only the diagram row for prime-pair selection. -/
theorem source_prime_pair_or_diagram
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hd : CartanPrimeActor A H p D) :
    (∃ R : Subgroup G, LocalData T L H B D R) ∨ Global.RightDiagramSource T L H := by
  rcases Global.right_source_cases h.qtke h.sylow_normalizes hH hpar with hs | hs
  · exact Or.inl (rankOne_source_localData h hH hpar c hd hs)
  · exact Or.inr hs

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
