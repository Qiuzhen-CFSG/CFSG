module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleStrictSylow
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.SylowIndex

/-!
# Placing the original fixed line in the J₄ row

The simultaneous normalizer of L_v and V_v fixes their unique nonidentity
fixed vector v₀. Thus the original T_v centralizes v₀. Intersecting its
selected Sylow overgroup with the relatively normal K_v and applying the
literal central projection gives one model Sylow in which the simultaneous
normalizer and C(v₀) have common intersection of index at most two.

If v₀ survives the projection, its image is an involution in the first J₄
class: the second centralizer has insufficient two-part. The projection is
then injective on the entire original V_v, since its kernel lies in the
fixed line, so the moved image still has order 32. Both local images lie
in this same native first centralizer. All maps and subgroups are literal.

The final application constructs this alternative at the original preferred
escaping point. It excludes the smaller J₄ centralizer branch; the central
fixed-line and first-centralizer branches, HS/Ru exclusions, blocks,
splitting and fixed-space elimination remain. Neither 12.6.2 nor 12.6.23
is asserted. Earlier invariance and TI retain producer qt-d-1222-source
and final discharge owner qt-d-12634-source.

Source: Aschbacher--Smith, paragraph preceding 12.6.6 and proof of 12.6.12,
printed pp.824--826; GLS3 Table 5.3i for the native J₄ centralizers.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

omit [IsElementaryAbelian 2 V] in
/-- The original T_v fixes the generator of the actual L_v-fixed line. -/
theorem Tv_centralizes_local_fixed_generator
    (chosen : Section02.ChosenModule T L V)
    (v : V) (z : G) (hz : orderOf z = 2)
    (hline : ZV (Lv L (v : G)) (Vv L V (v : G)) = zpowers z)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    Tv T (v : G) ≤ centralizer ({z} : Set G) := by
  have hB : Tv T (v : G) ≤ normalizer (Lv L (v : G) : Set G) :=
    (inf_le_inf chosen.sylow_normalizes_component le_rfl).trans (Mv_le_normalizer_Lv L _)
  have hW : Tv T (v : G) ≤ normalizer (Vv L V (v : G) : Set G) :=
    normalizes_Vv_of_normalizes _ _ (inf_le_left.trans hTV) hB
  have hZ : Tv T (v : G) ≤ normalizer (ZV (Lv L (v : G)) (Vv L V (v : G)) : Set G) :=
    (le_inf hW (hB.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  rwa [hline,normalizer_zpowers_eq_centralizer_of_order_two z hz] at hZ

/-- The same model Sylow controls both literal local normalizers and the image of the original fixed involution. -/
theorem SourceHypothesis.nonsingular_fixed_generator_model_sylow_index
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (z : Kv (v : G)) (hz : orderOf (z : G) = 2)
    (hline : ZV (Lv L (v : G)) (Vv L V (v : G)) = zpowers (z : G))
    {F : Type*} [Group F] [Finite F]
    (f : Kv (v : G) →* F) (hf : Function.Surjective f) :
    let B := ((Lv L (v : G)).subgroupOf (Kv (v : G))).map f
    let W := ((Vv L V (v : G)).subgroupOf (Kv (v : G))).map f
    ∃ P : Sylow 2 F,
      (normalizer (B : Set F) ⊓ normalizer (W : Set F) ⊓
        centralizer ({f z} : Set F)).relIndex (P : Subgroup F) ≤ 2 := by
  let C := Kv (v : G)
  let B := (Lv L (v : G)).subgroupOf C
  let W := (Vv L V (v : G)).subgroupOf C
  let N := normalizer (B.map f : Set F) ⊓ normalizer (W.map f : Set F) ⊓
    centralizer ({f z} : Set F)
  obtain ⟨S,hTS,_⟩ := exists_sylow_with_Lv_normalizer T L
    H.chosen.sylow_normalizes_component (v : G)
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  have hSi := H.nonsingular_quasisimple_sylow_index_le_two D v hv hK hi S hTS
  have hSyl : Chapter1.IsSylowIn 2 S₀ (Gv (v : G)) := ⟨S,rfl⟩
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSyl
    (Kv_le_Gv (v : G)) (Kv_normalIn_Gv (v : G)).isSubnormal
  have hcent := Tv_centralizes_local_fixed_generator H.chosen v (z : G) hz hline hTV
  have hBC : Lv L (v : G) ≤ C := Lv_le_Kv_of_A6 L (v : G)
    (Classical.choice (D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv))
  have hWC : Vv L V (v : G) ≤ C := (H.nonsingular_component_rank D v hv).1
  have hnB : Tv T (v : G) ≤ normalizer (Lv L (v : G) : Set G) :=
    (inf_le_inf H.chosen.sylow_normalizes_component le_rfl).trans (Mv_le_normalizer_Lv L _)
  have hnW : Tv T (v : G) ≤ normalizer (Vv L V (v : G) : Set G) :=
    normalizes_Vv_of_normalizes _ _ (inf_le_left.trans hTV) hnB
  have hnBC : (Tv T (v : G)).subgroupOf C ≤ normalizer (B : Set C) := by
    rw [←subgroupOf_normalizer_eq hBC]
    exact comap_mono hnB
  have hnWC : (Tv T (v : G)).subgroupOf C ≤ normalizer (W : Set C) := by
    rw [←subgroupOf_normalizer_eq hWC]
    exact comap_mono hnW
  have hn : (Tv T (v : G)).subgroupOf C ≤ N.comap f := by
    intro x hx
    refine ⟨⟨le_normalizer_map f (mem_map_of_mem f (hnBC hx)),
      le_normalizer_map f (mem_map_of_mem f (hnWC hx))⟩,?_⟩
    apply mem_centralizer_singleton_iff.mpr
    rw [←map_mul,←map_mul]
    exact congrArg f (Subtype.ext (mem_centralizer_singleton_iff.mp (hcent hx)))
  refine ⟨P.mapSurjective hf,?_⟩
  change N.relIndex ((P : Subgroup C).map f) ≤ 2
  rw [←relIndex_comap]
  apply (relIndex_le_of_le_left hn index_ne_zero_of_finite).trans
  change ((Tv T (v : G)).comap C.subtype).relIndex (P : Subgroup C) ≤ 2
  rw [relIndex_comap,hP]
  exact (relIndex_le_of_le_right inf_le_left index_ne_zero_of_finite).trans hSi
end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
open scoped IsMulCommutative

private theorem mem_involution_line {i x : G} (hi : orderOf i = 2)
    (hx : x ∈ zpowers i) : x = 1 ∨ x = i := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf,hi] at hx
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hx
  have hn2 : n < 2 := Finset.mem_range.mp hn
  interval_cases n <;> simp

/-- If the original fixed line survives the central projection, the entire moved group retains its order 32. -/
theorem SourceHypothesis.nonsingular_moved_image_card_of_noncentral_fixed_generator
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (z : Kv (v : G)) (hz : orderOf (z : G) = 2)
    (hline : ZV (Lv L (v : G)) (Vv L V (v : G)) = zpowers (z : G))
    (hzc : z ∉ center (Kv (v : G)))
    {F : Type*} [Group F]
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* F) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center (Kv (v : G))))
    Nat.card (((Vv L V (v : G)).subgroupOf (Kv (v : G))).map f) = 32 := by
  let C := Kv (v : G)
  let W := (Vv L V (v : G)).subgroupOf C
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
  let g := f.comp W.subtype
  have hLC : Lv L (v : G) ≤ C := Lv_le_Kv_of_A6 L (v : G)
    (Classical.choice (D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv))
  have hg : Function.Injective g := by
    apply (MonoidHom.ker_eq_bot_iff g).mp
    apply bot_unique
    intro x hx
    have hxc : (x : C) ∈ center C := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact e.injective ((show g x = 1 from hx).trans e.map_one.symm)
    have hxline : ((x : C) : G) ∈ zpowers (z : G) := by
      rw [←hline]
      refine ⟨x.property,?_⟩
      intro b hb
      exact congrArg C.subtype (mem_center_iff.mp hxc ⟨b,hLC hb⟩)
    rcases mem_involution_line hz hxline with hxone | hxz
    · exact mem_bot.mpr (Subtype.ext (Subtype.ext hxone))
    · exact (hzc ((show (x : C) = z from Subtype.ext hxz) ▸ hxc)).elim
  have hc : Nat.card g.range = 32 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hg).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe (H.nonsingular_component_rank D v hv).1).toEquiv,
      D.nonsingular_moved_card H.chosen v hv]
    norm_num
  simpa only [g,MonoidHom.range_comp,range_subtype] using hc

/-- In the J₄ row the original fixed line is central in K_v, or its image lies in the first native involution class, retaining the local images and their common Sylow bound. -/
theorem SourceHypothesis.nonsingular_jankoFour_fixed_line_placement
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Janko4.Model) :
    let C := Kv (v : G)
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
    let B := ((Lv L (v : G)).subgroupOf C).map f
    let W := ((Vv L V (v : G)).subgroupOf C).map f
    ∃ z : C, orderOf (z : G) = 2 ∧
      ZV (Lv L (v : G)) (Vv L V (v : G)) = zpowers (z : G) ∧
      (z ∈ center C ∨
        (orderOf (f z) = 2 ∧
          Nonempty (centralizer ({f z} : Set Janko4.Model) ≃*
            Janko4.InvolutionCentralizers.First.centralizer) ∧
          B ≤ centralizer ({f z} : Set Janko4.Model) ∧
          W ≤ centralizer ({f z} : Set Janko4.Model) ∧ Nat.card W = 32 ∧
          ∃ P : Sylow 2 Janko4.Model,
            (normalizer (B : Set Janko4.Model) ⊓ normalizer (W : Set Janko4.Model) ⊓
              centralizer ({f z} : Set Janko4.Model)).relIndex (P : Subgroup Janko4.Model) ≤ 2)) := by
  let C := Kv (v : G)
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
  let B := ((Lv L (v : G)).subgroupOf C).map f
  let W := ((Vv L V (v : G)).subgroupOf C).map f
  obtain ⟨v₀,hv₀,hne,_,hline,_⟩ := D.nonsingular_moved_fixed_line H.chosen v hv
  let z : C := ⟨(v₀ : G),(H.nonsingular_component_rank D v hv).1 hv₀⟩
  have hz : orderOf (z : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian _ v₀.property)
    (fun hh => hne (Subtype.ext hh))
  refine ⟨z,hz,hline,?_⟩
  by_cases hzc : z ∈ center C
  · exact .inl hzc
  right
  have hfne : f z ≠ 1 := by
    intro hh
    exact hzc ((QuotientGroup.eq_one_iff _).mp
      (e.injective (hh.trans e.map_one.symm)))
  have hzsq : z^2=1 := Subtype.ext (by
    change (v₀:G)^2=1
    exact elemPow_eq_one_of_isElementaryAbelian _ v₀.property)
  have hft : orderOf (f z) = 2 := orderOf_eq_prime (by rw [←map_pow,hzsq,map_one]) hfne
  obtain ⟨P,hP⟩ := H.nonsingular_fixed_generator_model_sylow_index D v hv hK hTV hi
    z hz hline f (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hzline : (z : G) ∈ ZV (Lv L (v : G)) (Vv L V (v : G)) :=
    hline.symm ▸ mem_zpowers (z : G)
  have hBC : B ≤ centralizer ({f z} : Set Janko4.Model) := by
    rintro _ ⟨b,hb,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    rw [←map_mul,←map_mul]
    exact congrArg f (Subtype.ext (mem_centralizer_iff.mp hzline.2 (b : G) hb))
  have hWC : W ≤ centralizer ({f z} : Set Janko4.Model) := by
    let := Vv_elementary H.chosen.normalizes (v : G)
    rintro _ ⟨w,hw,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    rw [←map_mul,←map_mul]
    exact congrArg f (Subtype.ext (congrArg (Vv L V (v : G)).subtype
      (mul_comm (⟨(w:G),hw⟩ : Vv L V (v : G)) ⟨(z:G),hzline.1⟩)))
  exact ⟨hft,Janko4.InvolutionCentralizers.centralizer_equiv_first_of_sylow_index_le_two
    (f z) hft P
    ((relIndex_le_of_le_left inf_le_right index_ne_zero_of_finite).trans hP),hBC,hWC,
    H.nonsingular_moved_image_card_of_noncentral_fixed_generator D v hv z hz hline hzc e,
    P,hP⟩
end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Construct the marked J₄ fixed-line alternative at the actual preferred
escaping point. Its original residual, moved group and quotient projection
are retained. The central-line and first-centralizer alternatives still
require exclusion before 12.6.12, 12.6.2 and 12.6.23 can be concluded. -/
theorem SourceHypothesis.exists_preferred_nonsingular_jankoFour_fixed_line
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
      (IsQuasisimple (Kv (w : G)) →
        NonsingularRemainingCoverModels (Kv (w : G)) ∧
        ∀ e : ((Kv (w : G)) ⧸ center (Kv (w : G))) ≃* Janko4.Model,
          let C := Kv (w : G)
          let f := e.toMonoidHom.comp (QuotientGroup.mk' (center C))
          let B := ((Lv L (w : G)).subgroupOf C).map f
          let W := ((Vv L V (w : G)).subgroupOf C).map f
          ∃ z : C, orderOf (z : G) = 2 ∧
            ZV (Lv L (w : G)) (Vv L V (w : G)) = zpowers (z : G) ∧
            (z ∈ center C ∨
              (orderOf (f z) = 2 ∧
                Nonempty (centralizer ({f z} : Set Janko4.Model) ≃*
                  Janko4.InvolutionCentralizers.First.centralizer) ∧
                B ≤ centralizer ({f z} : Set Janko4.Model) ∧
                W ≤ centralizer ({f z} : Set Janko4.Model) ∧ Nat.card W = 32 ∧
                ∃ P : Sylow 2 Janko4.Model,
                  (normalizer (B : Set Janko4.Model) ⊓ normalizer (W : Set Janko4.Model) ⊓
                    centralizer ({f z} : Set Janko4.Model)).relIndex
                      (P : Subgroup Janko4.Model) ≤ 2))) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,hc,hq,hsimple,hmodels⟩ :=
    H.exists_preferred_nonsingular_quasisimple_strict_sylow D hTV hTI v hv he
  exact ⟨w,hw,he,hs,hi,hlt,hnot,hc,hq,hsimple,fun hK =>
    ⟨(hmodels hK).1,fun e => H.nonsingular_jankoFour_fixed_line_placement D w hw hK hTV hi e⟩⟩
end CFSG.Quasithin.Chapter12.Section06
