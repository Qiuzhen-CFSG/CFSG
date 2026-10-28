module

public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleExclusions
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleBender
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleRankTwo
public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.TwoRank

/-!
# Quasisimple catalogue reduction at the preferred escaping point

The original preferred-point construction supplies strict enlargement, escape,
and the actual Sylow position. Rank bounds, the surviving two-local marking,
and the Bender and rank-two exclusions reduce the quasisimple central quotient
to PSL₅(2), M₂₂, M₂₄, HS, He, Ru or J₄ at this same point. The original
V, its fixed space C_V(L), and all quotient maps are retained.

This is an application of the partial 12.6.12 reduction, not a proof that K_v
is not quasisimple. The remaining model exclusions, blocks, splitting and
fixed-space elimination belong to this source branch. Earlier T-invariance
and TI have producer qt-d-1222-source and final owner qt-d-12634-source.

Source: Aschbacher--Smith, Lemmas 12.6.11--12, printed pp.825--826.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The actual J₂ automorphism group has insufficient two-rank. -/
theorem SourceHypothesis.nonsingular_not_jankoTwo_centralQuotient
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G))) :
    ¬ Nonempty (((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Sporadic.LeechRelated.J2.Carrier) := by
  let := hK
  rintro ⟨e⟩
  have hauto := automorphism_primeRank_le_quotient_center (E := Kv (v : G)) 2
  rw [primeRank_equiv 2 (MulAut.congr e)] at hauto
  have hu := hauto.trans Sporadic.LeechRelated.J2.automorphism_primeRank_le_four
  have hl := H.nonsingular_automorphism_rank D v hv
  omega

/-- The rank-one, rank-two and J₂ exclusions leave these seven finite models. -/
theorem SourceHypothesis.nonsingular_quasisimple_finite_models
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G))) :
    let C := (Kv (v : G)) ⧸ center (Kv (v : G))
    ClassicalGroup.IsPSL C 5 2 ∨
      (∃ name : ClassificationModels.SporadicName,
        (name = .m22 ∨ name = .m24 ∨ name = .hs ∨
          name = .he ∨ name = .ru ∨ name = .j4) ∧ Nonempty (C ≃* name.Carrier)) := by
  rcases H.nonsingular_quasisimple_remaining_models D v hv hK with h | ⟨f,h⟩ | h | ⟨name,hn,he⟩
  · exact (H.nonsingular_not_bender_centralQuotient D v hv h).elim
  · exact (H.nonsingular_not_rankTwo_centralQuotient D v hv h).elim
  · exact .inl h
  · right
    refine ⟨name,?_,he⟩
    rcases hn with h | h | rfl | h | h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact (H.nonsingular_not_jankoTwo_centralQuotient D v hv hK he).elim
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inr (.inl h))))
    · exact .inr (.inr (.inr (.inr (.inr h))))

/-- The partial quasisimple catalogue on the actual preferred escaping point,
including its source Sylow position and canonical component. -/
theorem SourceHypothesis.exists_preferred_nonsingular_quasisimple_reduction
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
        let C := (Kv (w : G)) ⧸ center (Kv (w : G))
        ClassificationModels.IsBenderModel C ∨
          (∃ f, ChapterA.Section02.IsTheoremCRankTwoModel C f) ∨
          ClassicalGroup.IsPSL C 5 2 ∨
          (∃ name : ClassificationModels.SporadicName,
            (name = .m22 ∨ name = .m24 ∨ name = .j2 ∨ name = .hs ∨
              name = .he ∨ name = .ru ∨ name = .j4) ∧ Nonempty (C ≃* name.Carrier))) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,hc,hq,hsimple⟩ :=
    H.exists_preferred_nonsingular_component_escape D hTV hTI v hv he
  exact ⟨w,hw,he,hs,hi,hlt,hnot,hc,hq,hsimple,
    H.nonsingular_quasisimple_remaining_models D w hw⟩

/-- The finite-model reduction at the same original preferred escaping point. -/
theorem SourceHypothesis.exists_preferred_nonsingular_quasisimple_finite_models
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
        let C := (Kv (w : G)) ⧸ center (Kv (w : G))
        ClassicalGroup.IsPSL C 5 2 ∨
          (∃ name : ClassificationModels.SporadicName,
            (name = .m22 ∨ name = .m24 ∨ name = .hs ∨
              name = .he ∨ name = .ru ∨ name = .j4) ∧ Nonempty (C ≃* name.Carrier))) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,hc,hq,hsimple⟩ :=
    H.exists_preferred_nonsingular_component_escape D hTV hTI v hv he
  exact ⟨w,hw,he,hs,hi,hlt,hnot,hc,hq,hsimple,
    H.nonsingular_quasisimple_finite_models D w hw⟩

end CFSG.Quasithin.Chapter12.Section06
