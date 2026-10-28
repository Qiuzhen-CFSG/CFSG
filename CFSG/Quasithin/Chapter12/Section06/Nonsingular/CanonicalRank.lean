module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.CanonicalFixedSpace
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleRudvalis
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.SmallThompsonExclusion
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.FixedFreeRank
public import CFSG.Quasithin.ChapterB.InternalThompsonRank

/-!
# Closing the nonquasisimple nonsingular-centralizer branch

The fixed-free rank comparison puts J(T_v) inside J(S) for the same
selected Sylow S of G_v. Local Thompson generation and V_v <= [U,K_v]
therefore make the actual canonical centralizer-quotient action FF,
discharging the fixed-free case of 12.6.15. The existing A7, SL4(2), and
SL5(2) module exclusions then contradict an escaping nonquasisimple K_v.

At the unchanged preferred nonsingular point, an escaping centralizer
therefore has a genuinely quasisimple residual, with the actual HS or J4
central-quotient model. The HS covering map, original fixed line and
original V of order 64 are retained. Those two model exclusions and the
later fusion, weak-closure and fixed-space arguments remain unfinished;
this does not assert full 12.6.2 or 12.6.23. Earlier invariance/TI inputs
retain their source owner qt-d-1222-source and final source discharge
remains with qt-d-12634-source.

Source: Aschbacher--Smith, 12.6.12--15 and 12.6.18, combined manuscript of
1 March 2004, printed pp.825--827.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

theorem SourceHypothesis.nonsingular_canonical_ff_of_equal_two_rank
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hgen : Lv L (v : G) = ⁅Lv L (v : G),elementaryAbelianMaxJ (Tv T (v : G))⁆)
    (S : Sylow 2 (Gv (v : G)))
    (hTS : Tv T (v : G) ≤ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype)
    (hrank : primeRank 2 (Tv T (v : G)) =
      primeRank 2 ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype))
    (hred : U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) =
      (reducedTwoSubgroup (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)).map
        (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G).subtype)
    (hm : Vv L V (v : G) ≤ ⁅U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype),Kv (v : G)⁆) :
    let J := Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
    let E := reducedTwoSubgroup J
    letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
    IsFFModule (ChapterB.InternalThompsonAction.action E) := by
  let C := Kv (v : G)
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let J := C ⊔ S₀
  let E := reducedTwoSubgroup J
  let B := (Lv L (v : G)).subgroupOf J
  let P := (Tv T (v : G)).subgroupOf J
  let S₁ := S₀.subgroupOf J
  let : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
  have hBJ : Lv L (v : G) ≤ J := (H.nonsingular_canonical_component D v hv).2.1.trans le_sup_left
  have hPJ : Tv T (v : G) ≤ J := hTS.trans le_sup_right
  have hSJ : S₀ ≤ J := le_sup_right
  have hB : B.map J.subtype = Lv L (v : G) := map_subgroupOf_eq_of_le hBJ
  have hES : E.map J.subtype ≤ S₀ :=
    ((map_mono (reducedPSubgroup_le_pCore 2 J)).trans
      (core_le_R_of_sylow L C (v : G) S (Kv_le_Gv _))).trans (R_le_S L C S₀ _)
  have hr : primeRank 2 P = primeRank 2 S₁ := by
    rw [primeRank_equiv 2 (subgroupOfEquivOfLe hPJ),
      primeRank_equiv 2 (subgroupOfEquivOfLe hSJ)]
    exact hrank
  have hg : B = ⁅B,elementaryAbelianMaxJ P⁆ := by
    apply map_injective J.subtype_injective
    rw [map_commutator,hB,←elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective,
      map_subgroupOf_eq_of_le hPJ]
    exact hgen
  have hJE : J ≤ normalizer (E.map J.subtype : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      E.le_normalizer_map J.subtype
  have hWU : Vv L V (v : G) ≤ E.map J.subtype := by
    rw [hred] at hm
    exact hm.trans (le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans hJE))
  have hmove : ⁅E,B⁆ ≠ ⊥ := by
    intro hz
    have hc : E.map J.subtype ≤ centralizer (Lv L (v : G) : Set G) := by
      apply commutator_eq_bot_iff_le_centralizer.mp
      rw [←hB,←map_commutator,hz,Subgroup.map_bot]
    have hw : Vv L V (v : G) = ⊥ := by
      rw [←D.local_moved_generated H.chosen v hv]
      exact commutator_eq_bot_iff_le_centralizer.mpr (hWU.trans hc)
    have hcard := D.nonsingular_moved_card H.chosen v hv
    rw [hw,card_bot] at hcard
    norm_num at hcard
  exact ChapterB.ff_of_thompson_generated_movement_of_primeRank_eq E B P S₁
    (fun e he => hES (mem_map_of_mem J.subtype he)) (comap_mono hTS) hr hg hmove
end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

theorem SourceHypothesis.nonsingular_canonical_ff_of_fixed_free
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hz : ZV L V = ⊥)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hgen : Lv L (v : G) = ⁅Lv L (v : G),elementaryAbelianMaxJ (Tv T (v : G))⁆)
    (S : Sylow 2 (Gv (v : G)))
    (hTS : Tv T (v : G) ≤ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype)
    (hred : U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) =
      (reducedTwoSubgroup (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)).map
        (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G).subtype)
    (hm : Vv L V (v : G) ≤ ⁅U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype),Kv (v : G)⁆) :
    let J := Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
    let E := reducedTwoSubgroup J
    letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
    IsFFModule (ChapterB.InternalThompsonAction.action E) := by
  have hr := H.nonsingular_two_rank_eq_of_fixed_free D hTV hz v hv hs
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  have hl : primeRank 2 (Tv T (v : G)) ≤ primeRank 2 S₀ :=
    Theory.GroupTheory.primeRank_le_of_injective 2 (inclusion hTS) (inclusion_injective hTS)
  have hu : primeRank 2 S₀ ≤ primeRank 2 T := by
    rw [←T.primeRank_eq]
    exact Theory.GroupTheory.primeRank_le_of_injective 2 S₀.subtype S₀.subtype_injective
  exact H.nonsingular_canonical_ff_of_equal_two_rank D v hv hgen S hTS
    (le_antisymm hl (hu.trans_eq hr.symm)) hred hm

theorem SourceHypothesis.nonsingular_quasisimple_of_escape
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (he : ¬ Kv (v : G) ≤ M L) : IsQuasisimple (Kv (v : G)) := by
  by_contra hnot
  obtain ⟨hz,_,S,hTS,_,_,_,hred,hm,hnff⟩ :=
    H.nonsingular_escaping_canonical_nonff D v hv hTV hTI hnot hs hi he
  have hgen := H.local_thompson_generation D v hv hTV hs
    (H.nonsingular_thompson_not_le_core_of_not_quasisimple D v hv hTV hnot hs hi he)
  exact hnff (H.nonsingular_canonical_ff_of_fixed_free D v hv hTV hz hs hgen S hTS hred hm)

theorem SourceHypothesis.exists_preferred_nonsingular_quasisimple_escape
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ZV L V = ⊥ ∧ Nat.card V = 64 ∧
      ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
        Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
        (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
        Lv L (w : G) < Kv (w : G) ∧ ¬ Kv (w : G) ≤ M L ∧
        V ⊓ centralizer (Kv (w : G) : Set G) = zpowers (w : G) ∧
        ZV (Lv L (w : G)) (Vv L V (w : G)) = zpowers (w : G) ∧
        (w : G) ∈ Vv L V (w : G) ∧ IsQuasisimple (Kv (w : G)) ∧
        NonsingularHSJankoCoverModels (Kv (w : G)) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,_,_,_,hline,_,hmodels⟩ :=
    SourceHypothesis.exists_preferred_nonsingular_hs_or_jankoFour.{_,0} H D hTV hTI v hv he
  have hquasi := H.nonsingular_quasisimple_of_escape D w hw hTV hTI hs hi hnot
  obtain ⟨hz,hmodel,hl,hwV,hcard,_⟩ := hmodels hquasi
  exact ⟨hz,hcard,w,hw,he,hs,hi,hlt,hnot,hline,hl,hwV,hquasi,hmodel⟩

end CFSG.Quasithin.Chapter12.Section06
