module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleSmallSylow
public import Theory.SpecificGroups.BinaryLinear.FiveTwoLocalFive
public import Theory.SpecificGroups.PSL5Two.UniversalCover
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient

/-!
# Excluding the binary five-dimensional central quotient

The literal central quotient of K_v cannot be PSL₅(2). The constructed
universal projection of that matrix group has trivial kernel, so the center
of the perfect K_v is trivial. The original moved group V_v therefore keeps
its order 32 under the canonical projection. Its actual L_v normalizer has
an A₆ two-core quotient, hence order divisible by five. Transport through the
field-induced matrix equivalence contradicts the order-sixteen bound for
two-subgroups of GL₅(2) with such a normalizer.

The final application retains the original preferred escaping point, V,
C_V(L), conjugation and quotient maps. Five sporadic rows remain in general;
M₂₄, He and J₄ remain under the original small-Thompson hypothesis.
These reductions do not yet establish 12.6.2 or 12.6.23. Earlier invariance
and TI retain producer qt-d-1222-source and discharge owner qt-d-12634-source.

Source: Aschbacher--Smith, Lemma 12.6.12, printed pp.825--826; the multiplier
input is the proved PSL₅(2) case of I.1.3, printed p.407.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Triviality of the multiplier preserves the original order-32 moved group.
Its A₆ normalizer contradicts the binary five-dimensional two-local bound. -/
theorem SourceHypothesis.nonsingular_not_psl_five_two_centralQuotient
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G))) :
    ¬ ClassicalGroup.IsPSL ((Kv (v : G)) ⧸ center (Kv (v : G))) 5 2 := by
  let C := Kv (v : G)
  let := hK
  rintro ⟨F,hF,hfin,hcard,⟨e⟩⟩
  let eB := e.trans (Theory.SpecificGroups.PSL5Two.UniversalCover.fieldEquiv F hcard)
  have hz : center C = ⊥ :=
    PerfectCentralCovering.center_eq_bot_of_centralQuotientEquiv
      Theory.SpecificGroups.PSL5Two.UniversalCover.universalProjection_ker_eq_bot eB
  let eGL := eB.trans (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 5))
  let : Finite (BinaryLinear.OuterCyclic.LinearGroup 5) :=
    Finite.of_equiv (C ⧸ center C) eGL.toEquiv
  let q := QuotientGroup.mk' (center C)
  have hq : Function.Injective q := by
    apply (MonoidHom.ker_eq_bot_iff q).mp
    rw [QuotientGroup.ker_mk',hz]
  let B := ((Lv L (v : G)).subgroupOf C).map q
  let W := ((Vv L V (v : G)).subgroupOf C).map q
  obtain ⟨_,⟨eA⟩,_,_,hW,_,hn⟩ := H.nonsingular_centralQuotient_local_marking D v hv
  let : IsElementaryAbelian 2 W := hW
  have h5 : 5 ∣ Nat.card B := by
    apply dvd_trans _ (card_quotient_dvd_card (pCore 2 B))
    rw [Nat.card_congr eA.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hBN : B.map eGL.toMonoidHom ≤
      normalizer (W.map eGL.toMonoidHom : Set (BinaryLinear.OuterCyclic.LinearGroup 5)) :=
    (map_mono hn).trans (le_normalizer_map eGL.toMonoidHom)
  have hN5 : 5 ∣ Nat.card (normalizer (W.map eGL.toMonoidHom : Set (BinaryLinear.OuterCyclic.LinearGroup 5))) := by
    apply dvd_trans _ (card_dvd_of_le hBN)
    rwa [card_map_of_injective eGL.injective]
  have hu := BinaryLinear.FiveTwoLocalFive.card_le_sixteen (W.map eGL.toMonoidHom)
    ((IsElementaryAbelian.isPGroup 2 W).map eGL.toMonoidHom) hN5
  have hc : Nat.card W = 32 := by
    dsimp only [W]
    rw [card_map_of_injective hq,
      Nat.card_congr (subgroupOfEquivOfLe (H.nonsingular_component_rank D v hv).1).toEquiv,
      D.nonsingular_moved_card H.chosen v hv]
    decide
  rw [card_map_of_injective eGL.injective,hc] at hu
  exact (by decide : ¬ (32 : ℕ) ≤ 16) hu

/-- Only five sporadic central quotients remain after the binary linear exclusion. -/
theorem SourceHypothesis.nonsingular_quasisimple_models_after_linear
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G))) :
    let C := (Kv (v : G)) ⧸ center (Kv (v : G))
    ∃ name : ClassificationModels.SporadicName,
      (name = .m24 ∨ name = .hs ∨ name = .he ∨ name = .ru ∨ name = .j4) ∧
        Nonempty (C ≃* name.Carrier) := by
  rcases H.nonsingular_quasisimple_models_after_mathieu22 D v hv hK with h | h
  · exact (H.nonsingular_not_psl_five_two_centralQuotient D v hv hK h).elim
  · exact h

/-- Under the original small-Thompson hypothesis only M₂₄, He and J₄ remain. -/
theorem SourceHypothesis.nonsingular_quasisimple_models_small_thompson_after_linear
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTv : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L)
    (hK : IsQuasisimple (Kv (v : G))) :
    let C := (Kv (v : G)) ⧸ center (Kv (v : G))
    ∃ name : ClassificationModels.SporadicName,
      (name = .m24 ∨ name = .he ∨ name = .j4) ∧ Nonempty (C ≃* name.Carrier) := by
  rcases H.nonsingular_quasisimple_models_small_thompson D v hv hTV hTv hJ hK with h | h
  · exact (H.nonsingular_not_psl_five_two_centralQuotient D v hv hK h).elim
  · exact h

/-- The actual preferred escaping point satisfies the five-row catalogue and
its three-row small-Thompson refinement. Earlier invariance and TI retain
producer qt-d-1222-source and final discharge owner qt-d-12634-source. -/
theorem SourceHypothesis.exists_preferred_nonsingular_models_after_linear
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
        (∃ name : ClassificationModels.SporadicName,
          (name = .m24 ∨ name = .hs ∨ name = .he ∨ name = .ru ∨ name = .j4) ∧
            Nonempty (C ≃* name.Carrier)) ∧
        (elementaryAbelianMaxJ (Tv T (w : G)) ≤ Q T L →
          ∃ name : ClassificationModels.SporadicName,
            (name = .m24 ∨ name = .he ∨ name = .j4) ∧ Nonempty (C ≃* name.Carrier))) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,hc,hq,hsimple⟩ :=
    H.exists_preferred_nonsingular_component_escape D hTV hTI v hv he
  exact ⟨w,hw,he,hs,hi,hlt,hnot,hc,hq,hsimple,fun hK =>
    ⟨H.nonsingular_quasisimple_models_after_linear D w hw hK,
      fun hJ => H.nonsingular_quasisimple_models_small_thompson_after_linear D w hw hTV hs hJ hK⟩⟩

end CFSG.Quasithin.Chapter12.Section06
