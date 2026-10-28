module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleDoubleCovers

/-!
# The original local Sylow bound in every quotient model

Intersect a selected Sylow subgroup of G_v with the relatively normal K_v.
The original T_v normalizes both L_v and V_v and has index at most four in
that selected Sylow. Restriction to K_v, followed by any surjective model
map, therefore gives the same bound for the simultaneous normalizer of the
two literal images. No full-Sylow normalization is assumed.

The central-quotient specialization uses the canonical projection. The
preferred-point consumer attaches this bound to the marked HS/Ru double
covers and J4 catalogue, retaining the original V and C_V(L). The native
local exclusions, blocks, splitting and fixed-space elimination remain
required. Earlier invariance and TI retain producer qt-d-1222-source and
final discharge owner qt-d-12634-source.

Source: Aschbacher--Smith, 12.6.4 and the proof of 12.6.12, pp.824--826.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The simultaneous normalizer of the actual local images has Sylow index
at most four under any surjective map out of the original K_v. -/
theorem SourceHypothesis.nonsingular_local_model_sylow_index
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    {F : Type*} [Group F] [Finite F]
    (f : Kv (v : G) →* F) (hf : Function.Surjective f) :
    let B := ((Lv L (v : G)).subgroupOf (Kv (v : G))).map f
    let W := ((Vv L V (v : G)).subgroupOf (Kv (v : G))).map f
    ∃ P : Sylow 2 F,
      (normalizer (B : Set F) ⊓ normalizer (W : Set F)).relIndex
        (P : Subgroup F) ≤ 4 := by
  let C := Kv (v : G)
  let B := (Lv L (v : G)).subgroupOf C
  let W := (Vv L V (v : G)).subgroupOf C
  let N := normalizer (B.map f : Set F) ⊓ normalizer (W.map f : Set F)
  obtain ⟨S,hTS,_⟩ := exists_sylow_with_Lv_normalizer T L
    H.chosen.sylow_normalizes_component (v : G)
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  have hSi : (Tv T (v : G)).relIndex S₀ ≤ 4 := by
    simpa only [hi] using Tv_relIndex_le T (v : G) S₀ (S.isPGroup'.map _) hTS
  have hSyl : Chapter1.IsSylowIn 2 S₀ (Gv (v : G)) := ⟨S,rfl⟩
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSyl
    (Kv_le_Gv (v : G)) (Kv_normalIn_Gv (v : G)).isSubnormal
  have hBC : Lv L (v : G) ≤ C := Lv_le_Kv_of_A6 L (v : G)
    (Classical.choice (D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv))
  have hWC : Vv L V (v : G) ≤ C := (H.nonsingular_component_rank D v hv).1
  have hnB : Tv T (v : G) ≤ normalizer (Lv L (v : G) : Set G) :=
    (inf_le_inf H.chosen.sylow_normalizes_component le_rfl).trans
      (Mv_le_normalizer_Lv L (v : G))
  have hnW : Tv T (v : G) ≤ normalizer (Vv L V (v : G) : Set G) :=
    normalizes_Vv_of_normalizes _ _ (inf_le_left.trans hTV) hnB
  have hnBC : (Tv T (v : G)).subgroupOf C ≤ normalizer (B : Set C) := by
    rw [←subgroupOf_normalizer_eq hBC]
    exact comap_mono hnB
  have hnWC : (Tv T (v : G)).subgroupOf C ≤ normalizer (W : Set C) := by
    rw [←subgroupOf_normalizer_eq hWC]
    exact comap_mono hnW
  have hn : (Tv T (v : G)).subgroupOf C ≤ N.comap f := by
    apply map_le_iff_le_comap.mp
    exact le_inf ((map_mono hnBC).trans (le_normalizer_map f))
      ((map_mono hnWC).trans (le_normalizer_map f))
  refine ⟨P.mapSurjective hf,?_⟩
  change N.relIndex ((P : Subgroup C).map f) ≤ 4
  rw [←relIndex_comap]
  apply (relIndex_le_of_le_left hn index_ne_zero_of_finite).trans
  change ((Tv T (v : G)).comap C.subtype).relIndex (P : Subgroup C) ≤ 4
  rw [relIndex_comap,hP]
  exact (relIndex_le_of_le_right inf_le_left index_ne_zero_of_finite).trans hSi

end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Source 12.6.4's bound survives the literal central projection. -/
theorem SourceHypothesis.nonsingular_centralQuotient_local_sylow_index
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4) :
    let C := Kv (v : G)
    let q := QuotientGroup.mk' (center C)
    let B := ((Lv L (v : G)).subgroupOf C).map q
    let W := ((Vv L V (v : G)).subgroupOf C).map q
    ∃ P : Sylow 2 (C ⧸ center C),
      (normalizer (B : Set (C ⧸ center C)) ⊓
        normalizer (W : Set (C ⧸ center C))).relIndex (P : Subgroup (C ⧸ center C)) ≤ 4 :=
  H.nonsingular_local_model_sylow_index D v hv hTV hi
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)

/-- The marked covering catalogue and its genuine local Sylow bound at the
same preferred escaping point. -/
theorem SourceHypothesis.exists_preferred_nonsingular_cover_models_sylow
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      Lv L (w : G) < Kv (w : G) ∧ ¬ Kv (w : G) ≤ M L ∧
      ((Kv (w : G)).subgroupOf (Gv (w : G))).IsCComponent ∧
      IsQuasisimple (Star (Kv (w : G))) ∧ IsSimpleGroup (Star (Kv (w : G))) ∧
      (let C := Kv (w : G)
       let q := QuotientGroup.mk' (center C)
       let B := ((Lv L (w : G)).subgroupOf C).map q
       let W := ((Vv L V (w : G)).subgroupOf C).map q
       ∃ P : Sylow 2 (C ⧸ center C),
         (normalizer (B : Set (C ⧸ center C)) ⊓
           normalizer (W : Set (C ⧸ center C))).relIndex (P : Subgroup (C ⧸ center C)) ≤ 4) ∧
      (IsQuasisimple (Kv (w : G)) →
        NonsingularRemainingCoverModels (Kv (w : G)) ∧
        (Stellmacher.elementaryAbelianMaxJ (Tv T (w : G)) ≤ Q T L →
          Nonempty (((Kv (w : G)) ⧸ center (Kv (w : G))) ≃* Janko4.Model))) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,hc,hq,hsimple,hmodels⟩ :=
    H.exists_preferred_nonsingular_marked_cover_models D hTV hTI v hv he
  exact ⟨w,hw,he,hs,hi,hlt,hnot,hc,hq,hsimple,
    H.nonsingular_centralQuotient_local_sylow_index D w hw hTV hi,hmodels⟩

end CFSG.Quasithin.Chapter12.Section06
