module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPair
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.OutsideParabolic
public import CFSG.Quasithin.ChapterB.Section02.BaumannFrattini
public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.ReducedSolvability
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable
open ChapterB GlaubermanNiles FixedPair
universe u
variable {G : Type u} [Group G] [Finite G]
@[expose] noncomputable def control (T : Sylow 2 G)
    (D : CharacteristicPair (baumann (T : Subgroup G))) : Subgroup G :=
  centralizer (firstSeed T D : Set G) ⊔
    normalizer (D.second.map (baumann (T : Subgroup G)).subtype : Set G)

omit [Finite G] in
theorem normalizer_le_control (T : Sylow 2 G)
    (D : CharacteristicPair (baumann (T : Subgroup G))) :
    normalizer (T : Set G) ≤ control T D := by
  let := D.second_characteristic
  exact ((normalizer_le_normalizer_baumann (T : Subgroup G)).trans
    (normalizer_le_normalizer_characteristic_image _ D.second)).trans le_sup_right

theorem exists_minimalParabolic_outside (T : Sylow 2 G)
    (D : CharacteristicPair (baumann (T : Subgroup G))) (hproper : control T D ≠ ⊤) :
    ∃ (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H),
      IsMinimalParabolicOver (T.subtype hTH) ⊤ ∧ ¬ H ≤ control T D := by
  have hex : ∃ H : Subgroup G, IsMinimalParabolicOver T H ∧ ¬ H ≤ control T D := by
    by_contra! hn
    have hh := sup_le (sSup_le hn) (normalizer_le_control T D)
    change sSup {P | IsMinimalParabolicOver T P} ⊔ normalizer (T : Set G) ≤ control T D at hh
    rw [minimalParabolics_sup_normalizer T] at hh
    exact hproper (top_unique hh)
  obtain ⟨H,hH,hout⟩ := hex
  have hTH := hH.1.1.le
  refine ⟨H,hTH,?_,hout⟩
  apply (isMinimalParabolicOver_top_iff _).mpr
  have hu := Solvable.uniqueMaximalContaining_of_minimalParabolic T H hH
  obtain ⟨N,hN,hTN,hn⟩ := (uniqueMaximalContaining_top_iff _).mp hu
  refine ⟨⟨N,⟨hN,hTN⟩,?_⟩,?_⟩
  · intro A hA
    exact hn A hA.1 hA.2
  · intro ht
    exact hH.2 ((normal_subgroupOf_iff_le_normalizer hTH).mp ht)

theorem thompson_moves_of_escape (T : Sylow 2 G)
    (D : CharacteristicPair (baumann (T : Subgroup G)))
    (H W : Subgroup G) (hTH : (T : Subgroup G) ≤ H) (hWH : W ≤ H)
    [IsElementaryAbelian 2 W] [(W.subgroupOf H).Normal]
    (hseed : firstSeed T D ≤ W) (hout : ¬ H ≤ control T D) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G) := by
  intro hJ
  let := D.second_characteristic
  have hfactor := BaumannFrattini.centralizing_characteristic_factorization T H W hTH hWH
    (le_inf ((sSup_le fun _ h => h.1).trans hTH) hJ) D.second
  apply hout
  rw [hfactor]
  exact sup_le ((inf_le_right.trans (centralizer_le hseed)).trans le_sup_left)
    (inf_le_right.trans le_sup_right)

theorem omegaClosure_moves_of_escape (T : Sylow 2 G)
    (D : CharacteristicPair (baumann (T : Subgroup G)))
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hchar : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hout : ¬ H ≤ control T D) :
    ¬ elementaryAbelianMaxJ (T.subtype hTH : Subgroup H) ≤ centralizer
      (normalClosure (omegaOneCenterAmbient (T.subtype hTH : Subgroup H) : Set H) : Set H) := by
  let S := T.subtype hTH
  let U := normalClosure (omegaOneCenterAmbient (S : Subgroup H) : Set H)
  have hU := omegaCenter_normalClosure_reduced S hchar
  let := hU.elementary
  let W := U.map H.subtype
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map H.subtype
  let : (W.subgroupOf H).Normal := by
    change ((U.map H.subtype).comap H.subtype).Normal
    rw [comap_map_eq_self_of_injective H.subtype_injective]
    infer_instance
  have hseed : firstSeed T D ≤ W := by
    have hm := map_mono (f := H.subtype)
      (le_normalClosure : omegaOneCenterAmbient (S : Subgroup H) ≤ U)
    rw [←omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] at hm
    exact inf_le_left.trans hm
  have hm := thompson_moves_of_escape T D H W hTH (map_subtype_le _) hseed hout
  intro hj
  apply hm
  have hh := map_mono (f := H.subtype) hj
  rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,map_centralizer_subtype] at hh
  exact hh.trans inf_le_right
omit [Finite G] in
theorem solvable_local_action (V H : Subgroup G) [V.Normal]
    (U : Subgroup H) [U.Normal] (hUV : U.map H.subtype ≤ V)
    (hs : Group.IsSolvable (G ⧸ centralizer (V : Set G))) :
    Group.IsSolvable (H ⧸ centralizer (U : Set H)) := by
  let C := centralizer (V : Set G)
  let f := (QuotientGroup.mk' C).comp H.subtype
  let q := QuotientGroup.mk' (centralizer (U : Set H))
  let : Group.IsSolvable (G ⧸ C) := hs
  let : Group.IsSolvable (H ⧸ f.ker) :=
    Group.isSolvable_of_isSolvable_injective (QuotientGroup.quotientKerEquivRange f).injective
  have hk : f.ker ≤ q.ker := by
    intro h hh
    rw [QuotientGroup.ker_mk']
    intro v hv
    apply Subtype.ext
    have hc : (h : G) ∈ C := (QuotientGroup.eq_one_iff _).mp hh
    exact hc v (hUV (mem_map_of_mem H.subtype hv))
  let g := QuotientGroup.lift f.ker q hk
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective (centralizer (U : Set H)) a
    exact ⟨QuotientGroup.mk' f.ker h,rfl⟩
  exact Group.isSolvable_of_surjective hg

omit [Finite G] in
theorem omegaClosure_map_le (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) :
    (normalClosure (omegaOneCenterAmbient (T.subtype hTH : Subgroup H) : Set H)).map
      H.subtype ≤ normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  apply map_le_iff_le_comap.mpr
  apply normalClosure_le_normal
  apply map_le_iff_le_comap.mp
  rw [←omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]
  exact le_normalClosure

theorem exists_moving_solvable_minimalParabolic (T : Sylow 2 G)
    (hf : generalizedFitting G = pCore 2 G)
    (D : CharacteristicPair (baumann (T : Subgroup G))) (hproper : control T D ≠ ⊤)
    (hs : Group.IsSolvable (G ⧸ centralizer
      (normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Set G))) :
    ∃ (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H),
      IsMinimalParabolicOver (T.subtype hTH) ⊤ ∧ ¬ H ≤ control T D ∧
      generalizedFitting H = pCore 2 H ∧ Group.IsSolvable H ∧
      ¬ elementaryAbelianMaxJ (T.subtype hTH : Subgroup H) ≤ centralizer
        (normalClosure (omegaOneCenterAmbient (T.subtype hTH : Subgroup H) : Set H) : Set H) := by
  obtain ⟨H,hTH,hP,hout⟩ := exists_minimalParabolic_outside T D hproper
  have hc := centralizer_pCore_le_of_pCore_le H
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hf)
    ((pCore_isPGroup.le_sylow_of_normal T).trans hTH)
  have hJ := omegaClosure_moves_of_escape T D H hTH hc hout
  let S := T.subtype hTH
  let U := normalClosure (omegaOneCenterAmbient (S : Subgroup H) : Set H)
  have hU := omegaCenter_normalClosure_reduced S hc
  have hsU := solvable_local_action _ H U (omegaClosure_map_le T H hTH) hs
  have hsH := solvable_of_reduced_minimalParabolic_action S hP U hU hJ
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hsU
  exact ⟨H,hTH,hP,hout,(ChapterA.generalizedFitting_eq_pCore_iff 2).mpr hc,hsH,hJ⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable
