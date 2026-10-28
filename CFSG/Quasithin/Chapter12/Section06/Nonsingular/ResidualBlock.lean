module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.LocalBlock

/-!
# Constructing the original residual block and its canonical moved module

O2(K_v S) normalizes the literal A6-block L_v by the original selected
Sylow geometry. The short-seed propagation theorem therefore makes K_v
short: the nontrivial A6 image normally generates its simple two-core
quotient. Subnormality is asserted in G_v, where K_v is actually normal.

The same two-core centralizes U(L_v)=V_v. Characteristic two puts V_v
in that core, and elementary abelianness puts it in U=Omega1 Z(O2(K_v S)).
Its full L_v-movement gives V_v <= [U,K_v]. Normalizer escape constructs
all block inputs under actual nonquasisimplicity, so this containment
requires neither R=R_v nor an ambient Sylow assumption.

The A7 model identification, remaining HS/J4 exclusions, splitting and
fixed-space elimination still belong to the same source assembly; neither
12.6.2 nor 12.6.23 is asserted here. Source: Aschbacher--Smith 12.6.13(3)
and 12.6.18, printed pp.826--827, using C.1.21's short-seed argument,
combined manuscript of 1 March 2004.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation BinaryPermutation BinaryPermutation.EightNonsingular
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The actual local short seed normally generates the nonquasisimple residual. -/
theorem SourceHypothesis.nonsingular_residual_short_of_local_block
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hnot : ¬ IsQuasisimple (Kv (v : G)))
    (hb : ChapterC.IsShort (Lv L (v : G)))
    (S : Sylow 2 (Gv (v : G)))
    (hRN : R L (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) (v : G) ≤
      normalizer (Lv L (v : G) : Set G)) :
    ChapterC.IsShort (Kv (v : G)) := by
  let C := Kv (v : G)
  let A := (Lv L (v : G)).subgroupOf C
  let P := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  have hAC : Lv L (v : G) ≤ C := (H.nonsingular_canonical_component D v hv).2.1
  let a : A ≃* Lv L (v : G) := subgroupOfEquivOfLe hAC
  have hA : ChapterC.IsShort A := hb.of_mulEquiv a.symm
  have hPC : P ≤ normalizer (C : Set G) := (map_subtype_le _).trans
    ((normal_subgroupOf_iff_le_normalizer (Kv_le_Gv (v : G))).mp (Kv_normalIn_Gv _))
  have hQ : C.pCoreIn 2 ≤ R L C P (v : G) :=
    (pCoreIn_mono_of_normalizes (show C ≤ C ⊔ P from le_sup_left)
      (sup_le C.le_normalizer hPC)).trans (core_le_R_of_sylow L C (v : G) S (Kv_le_Gv _))
  have hQA : pCore 2 C ≤ normalizer (A : Set C) := by
    apply le_normalizer_iff.mpr
    intro x hx y hy
    exact le_normalizer_iff.mp hRN x (hQ (mem_map_of_mem C.subtype hx)) y hy
  obtain ⟨_,_,_,hq,hsimple⟩ := H.nonsingular_canonical_component D v hv
  let : IsQuasisimple (Star C) := hq
  let : IsSimpleGroup (Star C) := hsimple
  have hz : center (Star C) = ⊥ := by
    rcases (inferInstance : (center (Star C)).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hz)).elim
  have hnoncentral : ¬ A.map (QuotientGroup.mk' (pCore 2 C)) ≤ center (Star C) := by
    intro hcent
    have hAp : A ≤ pCore 2 C := by
      simpa only [hz,le_bot_iff,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] using hcent
    have hpp : IsPGroup 2 (Lv L (v : G)) := (pCore_isPGroup.to_le hAp).of_equiv a
    obtain ⟨n,hn⟩ := hpp.exists_card_eq
    obtain ⟨e⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
    have hd : 3 ∣ 2 ^ n := by
      rw [←hn]
      apply dvd_trans _ (card_quotient_dvd_card (pCore 2 (Lv L (v : G))))
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
      decide
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  have hf := (H.nonsingular_nonquasisimple_signalizer D v hv hnot).2.2
  exact ChapterC.RankOne.GlaubermanArgument.isShort_of_normal_generation A hA
    (Kv_isPPerfect (v : G)) hf (Or.inl hq) hQA
    (ChapterC.RankOne.GlaubermanArgument.normal_generation_of_noncentral_core_image A
      (Kv_isPPerfect (v : G)) hnoncentral)

/-- Local shortness puts the original V_v in the canonical moved module, with no R=R_v premise. -/
theorem SourceHypothesis.nonsingular_moved_le_canonical_of_local_block
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hshort : ChapterC.IsShort L)
    (S : Sylow 2 (Gv (v : G)))
    (hRN : R L (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) (v : G) ≤
      normalizer (Lv L (v : G) : Set G))
    (hF : generalizedFitting (Kv (v : G) ⊔
      (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G) =
      pCore 2 (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)) :
    Vv L V (v : G) ≤ ⁅U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map
      (Gv (v : G)).subtype),Kv (v : G)⁆ := by
  let C := Kv (v : G)
  let P := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let J := C ⊔ P
  let A := Lv L (v : G)
  let W := Vv L V (v : G)
  have hAJ : A ≤ J := (H.nonsingular_canonical_component D v hv).2.1.trans le_sup_left
  have hWA : W ≤ A := Vv_le_Lv H.chosen v
  have hWJ : W ≤ J := hWA.trans hAJ
  have hb := (H.nonsingular_local_alternating_block D hshort v hv).2.1
  have hQn : J.pCoreIn 2 ≤ normalizer (A : Set G) :=
    (core_le_R_of_sylow L C (v : G) S (Kv_le_Gv _)).trans hRN
  have hAn : A ≤ normalizer (J.pCoreIn 2 : Set G) :=
    hAJ.trans (J.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
  have hc := hb.normalizing_twoGroup_centralizes_blockU (isPGroup_pCoreIn 2 J) hAn hQn
  rw [H.nonsingular_local_block_layer D hshort v hv] at hc
  have hWcore : W ≤ J.pCoreIn 2 := by
    intro w hw
    have hh : (⟨w,hWJ hw⟩ : J) ∈ centralizer (pCore 2 J : Set J) := by
      intro x hx
      exact Subtype.ext ((le_centralizer_iff.mp hc) hw x (mem_map_of_mem J.subtype hx))
    rw [←hF] at hh
    have hx := centralizer_generalizedFitting_le J hh
    rw [hF] at hx
    exact mem_map_of_mem J.subtype hx
  have hWU : W ≤ U C P := by
    rw [U_eq_omegaCenter]
    intro w hw
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    exact ⟨hWcore hw,
      elemPow_eq_one_of_isElementaryAbelian w (Vv_le_V H.chosen.normalizes _ hw),
      fun r hr => (le_centralizer_iff.mp hc) hw r hr⟩
  exact (D.local_moved_generated H.chosen v hv).symm.le.trans
    (commutator_mono hWU (H.nonsingular_canonical_component D v hv).2.1)

/-- Normalizer escape constructs the local and residual blocks and the literal
canonical-module containment under actual nonquasisimplicity. -/
theorem SourceHypothesis.nonsingular_residual_block_of_not_quasisimple
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnot : ¬ IsQuasisimple (Kv (v : G)))
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (he : ¬ Kv (v : G) ≤ M L) :
    ChapterC.IsAlternatingBlock L 8 ∧
      ChapterC.IsAlternatingBlock (Lv L (v : G)) 6 ∧
      (ChapterC.blockU (Lv L (v : G))).map (Lv L (v : G)).subtype = Vv L V (v : G) ∧
      ChapterC.IsShort (Kv (v : G)) ∧
      ChapterC.IsBlock ((Kv (v : G)).subgroupOf (Gv (v : G))) ∧
      ∃ S : Sylow 2 (Gv (v : G)),
        let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
        let J := Kv (v : G) ⊔ S₀
        Tv T (v : G) ≤ S₀ ∧
        Chapter1.IsSylowIn 2 (S₀ ⊓ normalizer (Lv L (v : G) : Set G))
          (Gv (v : G) ⊓ normalizer (Lv L (v : G) : Set G)) ∧
        R L (Kv (v : G)) S₀ (v : G) = S₀ ⊓ coreQuotientCentralizer (Lv L (v : G)) ∧
        generalizedFitting J = pCore 2 J ∧
        centralizer ((U (Kv (v : G)) S₀).subgroupOf J : Set J) = pCore 2 J ∧
        U (Kv (v : G)) S₀ = (reducedTwoSubgroup J).map J.subtype ∧
        Vv L V (v : G) ≤ ⁅U (Kv (v : G)) S₀,Kv (v : G)⁆ := by
  have hn := H.nonsingular_normalizer_escape_of_not_quasisimple D v hv hTV hnot hs hi he
  have hL := (H.nonsingular_original_alternating_block D hTV v hv hn).1
  have hA := H.nonsingular_local_alternating_block D hL.2.1 v hv
  obtain ⟨S,hTS,hN,hRN,_,hReq,_,hF,hker,hred⟩ :=
    H.nonsingular_nonquasisimple_canonical_module D v hv hnot hs hi
  have hC := H.nonsingular_residual_short_of_local_block D v hv hnot hA.2.1 S hRN
  have hCB : ChapterC.IsBlock ((Kv (v : G)).subgroupOf (Gv (v : G))) := {
    finite := inferInstance
    short := hC.of_mulEquiv (subgroupOfEquivOfLe (Kv_le_Gv (v : G))).symm
    subnormal := (Kv_normalIn_Gv (v : G)).isSubnormal }
  exact ⟨hL,hA,H.nonsingular_local_block_layer D hL.2.1 v hv,hC,hCB,
    S,hTS,hN,hReq,hF,hker,hred,
    H.nonsingular_moved_le_canonical_of_local_block D v hv hL.2.1 S hRN hF⟩

end CFSG.Quasithin.Chapter12.Section06
