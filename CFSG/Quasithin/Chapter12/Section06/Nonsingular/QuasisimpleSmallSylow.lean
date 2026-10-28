module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleMathieu
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowNormalElementary
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.TwoLocalOrder

/-!
# The small-Thompson HS and Ru exclusions at the original nonsingular point

Source 12.6.8 makes the original T_v a full Sylow subgroup of G_v when
J(T_v) lies in Q. Intersect it with the relatively normal K_v and pass
through the canonical central quotient. The resulting full Sylow normalizes
the image of the original moved subgroup V_v. That image has order at least
sixteen: its central kernel lies in the original fixed line of order two.

The native HS normal-elementary bound and the native Ru two-local three-part
obstruction exclude those two rows in this subcase. Thus either row forces
both original Thompson commutator identities. The last theorem applies the
four-row small-Thompson catalogue to the actual preferred escaping point.
The general six-row catalogue, blocks, splitting and fixed-space elimination
remain open; this module does not assert 12.6.2 or 12.6.23. Earlier invariance
and TI retain producer qt-d-1222-source and discharge owner qt-d-12634-source.

Source: Aschbacher--Smith, Lemmas 12.6.8--9 and 12.6.12, pp.824--826.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The actual moved image has at least sixteen elements. -/
theorem SourceHypothesis.nonsingular_centralQuotient_moved_card
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v) :
    let C := Kv (v : G)
    let W := (Vv L V (v : G)).subgroupOf C
    let q := QuotientGroup.mk' (center C)
    16 ≤ Nat.card (W.map q) := by
  let C := Kv (v : G)
  let W := Vv L V (v : G)
  have hWC : W ≤ C := (H.nonsingular_component_rank D v hv).1
  have hBC : Lv L (v : G) ≤ C := Lv_le_Kv_of_A6 L (v : G)
    (Classical.choice (D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv))
  let f : W →* C ⧸ center C := (QuotientGroup.mk' (center C)).comp (inclusion hWC)
  let j : f.ker → ZV (Lv L (v : G)) W := fun x => ⟨x.val.val, x.val.property, by
    have hz : inclusion hWC x.val ∈ center C := (QuotientGroup.eq_one_iff _).mp x.property
    intro b hb
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨b,hBC hb⟩)⟩
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ZV (Lv L (v : G)) W => (z : G)) h
  have hk : Nat.card f.ker ≤ 2 := (Nat.card_le_card_of_injective j hj).trans_eq
    (D.nonsingular_moved_fixed_card H.chosen v hv)
  have hc := f.ker.card_mul_index
  rw [index_ker,D.nonsingular_moved_card H.chosen v hv] at hc
  have hi : 16 ≤ Nat.card f.range := by nlinarith
  simpa only [f,MonoidHom.range_comp,inclusion_range] using hi

/-- In the small-Thompson branch, a full Sylow of the literal central quotient
normalizes the image of the original V_v. -/
theorem SourceHypothesis.small_thompson_centralQuotient_moved_normalizer
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTv : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L) :
    let C := Kv (v : G)
    let W := (Vv L V (v : G)).subgroupOf C
    let q := QuotientGroup.mk' (center C)
    ∃ S : Sylow 2 (C ⧸ center C),
      (S : Subgroup (C ⧸ center C)) ≤ normalizer (W.map q : Set (C ⧸ center C)) := by
  let C := Kv (v : G)
  let W := Vv L V (v : G)
  obtain ⟨S,hTS,_⟩ := exists_sylow_with_Lv_normalizer T L
    H.chosen.sylow_normalizes_component (v : G)
  have hS := (H.nonsingular_small_thompson D v hv hTv hJ S hTS).1
  have hSyl : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Gv (v : G)) := ⟨S,hS⟩
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hSyl
    (Kv_le_Gv (v : G)) (Kv_normalIn_Gv (v : G)).isSubnormal
  have hWC : W ≤ C := (H.nonsingular_component_rank D v hv).1
  have hn : Tv T (v : G) ≤ normalizer (W : Set G) :=
    normalizes_Vv_of_normalizes _ _ (inf_le_left.trans hTV)
      ((inf_le_inf H.chosen.sylow_normalizes_component le_rfl).trans (Mv_le_normalizer_Lv L _))
  have hPN : (P : Subgroup C) ≤ normalizer (W.subgroupOf C : Set C) := by
    rw [←subgroupOf_normalizer_eq hWC]
    intro p hp
    exact hn ((hP ▸ mem_map_of_mem C.subtype hp).1)
  let q := QuotientGroup.mk' (center C)
  refine ⟨P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _),?_⟩
  exact (map_mono hPN).trans (le_normalizer_map q)

/-- HS is impossible in the small-Thompson branch, since its full Sylow
normalizes no elementary subgroup of order at least sixteen. -/
theorem SourceHypothesis.small_thompson_not_hs_centralQuotient
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTv : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L) :
    ¬ Nonempty (((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier) := by
  rintro ⟨e⟩
  let C := Kv (v : G)
  let W := ((Vv L V (v : G)).subgroupOf C).map (QuotientGroup.mk' (center C))
  obtain ⟨_,_,_,_,he,_,_⟩ := H.nonsingular_centralQuotient_local_marking D v hv
  let : IsElementaryAbelian 2 W := he
  obtain ⟨S,hS⟩ := H.small_thompson_centralQuotient_moved_normalizer D v hv hTV hTv hJ
  have hN : ((S.mapSurjective (f := e.toMonoidHom) e.surjective) : Subgroup Sporadic.LeechRelated.HS.Carrier) ≤
      normalizer (W.map e.toMonoidHom : Set Sporadic.LeechRelated.HS.Carrier) :=
    (map_mono hS).trans (le_normalizer_map e.toMonoidHom)
  have hu := Sporadic.LeechRelated.HS.normal_elementary_card_le_eight
    (S.mapSurjective (f := e.toMonoidHom) e.surjective) (W.map e.toMonoidHom) (IsElementaryAbelian.map e.toMonoidHom) hN
  rw [card_map_of_injective e.injective] at hu
  have hl := H.nonsingular_centralQuotient_moved_card D v hv
  change 16 ≤ Nat.card W at hl
  exact (by decide : ¬ (16 : ℕ) ≤ 8) (hl.trans hu)

/-- Ru is impossible in the small-Thompson branch: the actual local normalizer
contains a Sylow and has order divisible by nine through its A₆ section. -/
theorem SourceHypothesis.small_thompson_not_ru_centralQuotient
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTv : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L) :
    ¬ Nonempty (((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Rudvalis.Model) := by
  rintro ⟨e⟩
  let C := Kv (v : G)
  let q := QuotientGroup.mk' (center C)
  let B := ((Lv L (v : G)).subgroupOf C).map q
  let W := ((Vv L V (v : G)).subgroupOf C).map q
  obtain ⟨_,⟨eB⟩,_,hne,he,_,hn⟩ := H.nonsingular_centralQuotient_local_marking D v hv
  let : IsElementaryAbelian 2 W := he
  let E := W.map e.toMonoidHom
  have hEne : E ≠ ⊥ := fun hh => hne ((map_eq_bot_iff_of_injective _ e.injective).mp hh)
  have h9 : 9 ∣ Nat.card B := by
    apply dvd_trans _ (card_quotient_dvd_card (pCore 2 B))
    rw [Nat.card_congr eB.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hBE : B.map e.toMonoidHom ≤ normalizer (E : Set Rudvalis.Model) :=
    (map_mono hn).trans (le_normalizer_map e.toMonoidHom)
  have hN9 : 9 ∣ Nat.card (normalizer (E : Set Rudvalis.Model)) := by
    apply dvd_trans _ (card_dvd_of_le hBE)
    rwa [card_map_of_injective e.injective]
  obtain ⟨S,hS⟩ := H.small_thompson_centralQuotient_moved_normalizer D v hv hTV hTv hJ
  have hN : ((S.mapSurjective (f := e.toMonoidHom) e.surjective) : Subgroup Rudvalis.Model) ≤
      normalizer (E : Set Rudvalis.Model) :=
    (map_mono hS).trans (le_normalizer_map e.toMonoidHom)
  exact Rudvalis.SylowOvergroups.not_nine_dvd_card_twoLocal
    (S.mapSurjective (f := e.toMonoidHom) e.surjective) _
    ⟨E,hEne,(IsElementaryAbelian.isPGroup 2 W).map e.toMonoidHom,rfl⟩ hN hN9

/-- The small-Thompson subcase of the remaining central-quotient catalogue. -/
theorem SourceHypothesis.nonsingular_quasisimple_models_small_thompson
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTv : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L)
    (hK : IsQuasisimple (Kv (v : G))) :
    let C := (Kv (v : G)) ⧸ center (Kv (v : G))
    ClassicalGroup.IsPSL C 5 2 ∨
      (∃ name : ClassificationModels.SporadicName,
        (name = .m24 ∨ name = .he ∨ name = .j4) ∧ Nonempty (C ≃* name.Carrier)) := by
  rcases H.nonsingular_quasisimple_models_after_mathieu22 D v hv hK with h | ⟨name,hn,he⟩
  · exact .inl h
  · right
    refine ⟨name,?_,he⟩
    rcases hn with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact (H.small_thompson_not_hs_centralQuotient D v hv hTV hTv hJ he).elim
    · exact Or.inr (Or.inl rfl)
    · exact (H.small_thompson_not_ru_centralQuotient D v hv hTV hTv hJ he).elim
    · exact Or.inr (Or.inr rfl)

/-- Either remaining HS/Ru central quotient forces both original Thompson
commutator identities. There is no assumed Thompson movement. -/
theorem SourceHypothesis.nonsingular_hs_ru_thompson_generation
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTv : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hmodel : Nonempty (((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.HS.Carrier) ∨
      Nonempty (((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Rudvalis.Model)) :
    ¬ elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L ∧
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ Q T L ∧
      Lv L (v : G) = ⁅Lv L (v : G),elementaryAbelianMaxJ (Tv T (v : G))⁆ ∧
      L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  have hJ : ¬ elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L := by
    intro hJ
    rcases hmodel with h | h
    · exact H.small_thompson_not_hs_centralQuotient D v hv hTV hTv hJ h
    · exact H.small_thompson_not_ru_centralQuotient D v hv hTV hTv hJ h
  exact ⟨hJ,H.nonsingular_thompson_generation D v hv hTV hTv hJ⟩

/-- At the actual preferred escaping point the small-Thompson catalogue has
four rows. The original V, its fixed space, local residual and central quotient
are unchanged. Earlier invariance and TI have producer qt-d-1222-source and
final discharge owner qt-d-12634-source. -/
theorem SourceHypothesis.exists_preferred_nonsingular_small_thompson_models
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
        elementaryAbelianMaxJ (Tv T (w : G)) ≤ Q T L →
        let C := (Kv (w : G)) ⧸ center (Kv (w : G))
        ClassicalGroup.IsPSL C 5 2 ∨
          (∃ name : ClassificationModels.SporadicName,
            (name = .m24 ∨ name = .he ∨ name = .j4) ∧ Nonempty (C ≃* name.Carrier))) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,hc,hq,hsimple⟩ :=
    H.exists_preferred_nonsingular_component_escape D hTV hTI v hv he
  exact ⟨w,hw,he,hs,hi,hlt,hnot,hc,hq,hsimple,fun hK hJ =>
    H.nonsingular_quasisimple_models_small_thompson D w hw hTV hs hJ hK⟩

end CFSG.Quasithin.Chapter12.Section06
