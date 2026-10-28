module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.QuasisimpleGlobalFixed
public import Theory.GroupAction.InvolutionCentralizerCongruence

/-!
# Excluding the original Rudvalis action

Every surviving quasisimple residual has original V-action image of order
32. In Ru every automorphism is inner, so this image is an actual elementary
subgroup of the specified central-quotient model. The literal L_v image
normalizes it, and its A6 quotient makes its order divisible by nine.
The three-group orbit congruence then gives a nonidentity fixed involution,
contradicting the native Ru involution-centralizer orders.

The preferred-point application now leaves only HS and J4, retaining the
original V, its component-centralizer line, the local moved subgroup, and
the compatible HS double-cover projection. These last two exclusions,
blocks, splitting and general fixed-space elimination remain open; neither
12.6.2 nor 12.6.23 is asserted. Earlier invariance/TI retain producer
qt-d-1222-source and final discharge owner qt-d-12634-source.

Source: Aschbacher--Smith, proof of 12.6.12, printed pp.825--826;
GLS3 Table 5.3r for the literal Ru involution-centralizer orders.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section06

/-- The last two actual models, retaining the compatible HS covering map. -/
@[expose] def NonsingularHSJankoCoverModels (C : Type*) [Group C] : Prop :=
  (∃ hp : Group.IsPerfect Sporadic.LeechRelated.HS.Carrier,
    letI := hp
    ∃ (e : (C ⧸ center C) ≃* Sporadic.LeechRelated.HS.Carrier)
      (f : C ≃* Theory.SpecificGroups.J2HSMultipliers.HS.DoubleCover),
      ∀ x, Theory.SpecificGroups.J2HSMultipliers.HS.projection (f x) =
        e (QuotientGroup.mk' (center C) x)) ∨
  Nonempty ((C ⧸ center C) ≃* Janko4.Model)

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The full original Ru action has order one modulo three. The bound uses its actual normalized local image. -/
theorem SourceHypothesis.nonsingular_ru_original_action_card_mod_three
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Rudvalis.Model) :
    Nat.card ((V.subgroupOf (Gv (v : G))).map
      (nonsingularModelAction (v : G) e)) % 3 = 1 := by
  let := hK
  let : IsSimpleGroup ((Kv (v : G)) ⧸ center (Kv (v : G))) := IsQuasisimple.simple
  let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
  let j : Rudvalis.Model ≃* MulAut Rudvalis.Model := MulEquiv.ofBijective MulAut.conj
    ⟨MulAut.conj_injective_of_center_eq_bot Rudvalis.LowCentralizers.model_center_eq_bot,
      Rudvalis.component_conj_surjective⟩
  let a := nonsingularModelAction (v : G) e
  let E := (V.subgroupOf (Gv (v : G))).map a
  let B := ((Lv L (v : G)).subgroupOf (Gv (v : G))).map a
  obtain ⟨he,_,_,_,_,hn,_⟩ := H.nonsingular_original_model_action D v hv hK e
  let : IsElementaryAbelian 2 E := he
  let E' := E.map j.symm.toMonoidHom
  let B' := B.map j.symm.toMonoidHom
  let : IsElementaryAbelian 2 E' := IsElementaryAbelian.map j.symm.toMonoidHom
  have hLC : Lv L (v : G) ≤ Kv (v : G) := Lv_le_Kv_of_A6 L _
    (Classical.choice (D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv))
  have hj : Function.Injective (MulAut.conj : Rudvalis.Model →* MulAut Rudvalis.Model) :=
    MulAut.conj_injective_of_center_eq_bot Rudvalis.LowCentralizers.model_center_eq_bot
  have hje : Function.Injective (MulAut.conj.comp e.toMonoidHom) := hj.comp e.injective
  have hB : 9 ∣ Nat.card B' := by
    rw [card_map_of_injective j.symm.injective]
    dsimp only [B,a]
    rw [nonsingularModelAction_map _ _ _ hLC,
      card_map_of_injective hje]
    obtain ⟨_,⟨eB⟩,_⟩ := H.nonsingular_centralQuotient_local_marking D v hv
    apply dvd_trans _ (card_quotient_dvd_card (pCore 2 _))
    rw [Nat.card_congr eB.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hN : B' ≤ normalizer (E' : Set Rudvalis.Model) :=
    (map_mono hn).trans (le_normalizer_map j.symm.toMonoidHom)
  have hm := elementary_card_mod_three_of_involution_centralizers
    Rudvalis.InvolutionCentralizers.centralizer_not_nine B' E' hB hN
  rwa [card_map_of_injective j.symm.injective] at hm

/-- The Ru row is impossible at an escaping nonsingular point in the original Sylow position. -/
theorem SourceHypothesis.nonsingular_not_rudvalis
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (hnot : ¬ Kv (v : G) ≤ M L)
    (e : ((Kv (v : G)) ⧸ center (Kv (v : G))) ≃* Rudvalis.Model) : False := by
  have hm := H.nonsingular_ru_original_action_card_mod_three D v hv hK e
  rw [(H.nonsingular_quasisimple_original_card D v hv hK hTV hi hnot).2 e] at hm
  norm_num at hm

/-- The two remaining models come with genuine central-quotient and covering identifications. -/
theorem SourceHypothesis.nonsingular_quasisimple_hs_or_jankoFour
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hK : IsQuasisimple (Kv (v : G)))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (hnot : ¬ Kv (v : G) ≤ M L) :
    NonsingularHSJankoCoverModels (Kv (v : G)) := by
  rcases H.nonsingular_quasisimple_marked_cover_models D v hv hK with h | h | h
  · exact .inl h
  · obtain ⟨e,_,_⟩ := h
    exact (H.nonsingular_not_rudvalis D v hv hK hTV hi hnot e).elim
  · exact .inr h

/-- Apply the Ru exclusion to the literal preferred point, preserving its original action and geometry. -/
theorem SourceHypothesis.exists_preferred_nonsingular_hs_or_jankoFour
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
      V ⊓ centralizer (Kv (w : G) : Set G) = zpowers (w : G) ∧
      (ZV L V ≠ ⊥ → ¬ IsQuasisimple (Kv (w : G))) ∧
      (IsQuasisimple (Kv (w : G)) → ZV L V = ⊥ ∧
        NonsingularHSJankoCoverModels (Kv (w : G)) ∧
        ZV (Lv L (w : G)) (Vv L V (w : G)) = zpowers (w : G) ∧
        (w : G) ∈ Vv L V (w : G) ∧
        Nat.card V = 64 ∧ ∀ {F : Type*} [Group F],
          ∀ e : ((Kv (w : G)) ⧸ center (Kv (w : G))) ≃* F,
            Nat.card ((V.subgroupOf (Gv (w : G))).map
              (nonsingularModelAction (w : G) e)) = 32) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,hc,hq,hsimple,hline,hfixed,hmodels⟩ :=
    H.exists_preferred_nonsingular_nontrivial_fixed_not_quasisimple D hTV hTI v hv he
  refine ⟨w,hw,he,hs,hi,hlt,hnot,hc,hq,hsimple,hline,hfixed,?_⟩
  intro hK
  obtain ⟨hz,_,hl,hwW,hV,ha⟩ := hmodels hK
  exact ⟨hz,H.nonsingular_quasisimple_hs_or_jankoFour D w hw hK hTV hi hnot,
    hl,hwW,hV,ha⟩

end CFSG.Quasithin.Chapter12.Section06
