module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.CanonicalFour
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.CanonicalFive
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.FixedFreeCanonical

/-!
# Eliminating the fixed-free canonical FF catalogue

The A7, SL4(2), and SL5(2) alternatives all force C_V(L) nontrivial:
the original local fixed line is moved in each actual canonical module.
This closes both remaining binary linear alternatives under FF.

The source consumer retains the same selected Sylow, the original
V_v <= [U,K_v], the canonical kernel and the literal action. Earlier
nonsingular-centralizer control forces C_V(L)=1, hence this action cannot
be FF. The independent proof of original 12.6.15 in the fixed-free branch
is still required; neither 12.6.2 nor 12.6.23 is asserted here. HS/J4,
fusion, weak closure and fixed-space elimination remain with this owner.
Earlier invariance/TI retain qt-d-1222-source and final source discharge
retains qt-d-12634-source.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
12.6.13, 12.6.15 and 12.6.18, printed pp.826--827.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Every actual canonical FF component model forces the original fixed
space to be nontrivial. This eliminates all three rows in the fixed-free branch. -/
theorem SourceHypothesis.nonsingular_canonical_ff_fixed_ne_bot
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (he : ¬ Kv (v : G) ≤ M L)
    (S : Sylow 2 (Gv (v : G)))
    (hRN : R L (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) (v : G) ≤
      normalizer (Lv L (v : G) : Set G))
    (hred : U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) =
      (reducedTwoSubgroup (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)).map
        (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G).subtype)
    (hm : Vv L V (v : G) ≤ ⁅U (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype),Kv (v : G)⁆)
    (hker : centralizer (reducedTwoSubgroup (Kv (v : G) ⊔
      (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G) :
      Set (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)) =
        pCore 2 (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G))
    (hff : let E := reducedTwoSubgroup (Kv (v : G) ⊔
      (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype : Subgroup G)
      letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
      IsFFModule (ChapterB.InternalThompsonAction.action E)) : ZV L V ≠ ⊥ := by
  rcases H.nonsingular_canonical_ff_models D v hv hTV hi he S hRN hker hff with h7 | h4 | h5
  · exact H.fixed_ne_bot_of_canonical_seven D v hv S hred hm
      (H.nonsingular_canonical_seven_moved D v hv S h7 hred hm hker hff)
  · exact H.fixed_ne_bot_of_canonical_four D v hv S h4 hred hm hker hff
  · exact H.fixed_ne_bot_of_canonical_five D v hv S h5 hred hm hker hff

/-- On the same selected Sylow, an escaping nonquasisimple source residual
has a canonical action that cannot be FF. Proving the source FF assertion
therefore remains the precise missing step for this branch. -/
theorem SourceHypothesis.nonsingular_escaping_canonical_nonff
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (hnot : ¬ IsQuasisimple (Kv (v : G)))
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (he : ¬ Kv (v : G) ≤ M L) :
    ZV L V = ⊥ ∧ IsSimpleGroup (Star (Kv (v : G))) ∧
    ∃ S : Sylow 2 (Gv (v : G)),
      let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
      let J := Kv (v : G) ⊔ S₀
      let E := reducedTwoSubgroup J
      letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
      Tv T (v : G) ≤ S₀ ∧
      R L (Kv (v : G)) S₀ (v : G) = S₀ ⊓ coreQuotientCentralizer (Lv L (v : G)) ∧
      generalizedFitting J = pCore 2 J ∧ centralizer (E : Set J) = pCore 2 J ∧
      U (Kv (v : G)) S₀ = E.map J.subtype ∧
      Vv L V (v : G) ≤ ⁅U (Kv (v : G)) S₀,Kv (v : G)⁆ ∧
      ¬ IsFFModule (ChapterB.InternalThompsonAction.action E) := by
  obtain ⟨hz,hsimple,S,hTS,hReq,hFit,hker,hred,hm,_⟩ :=
    H.nonsingular_escaping_canonical_linear_reduction D v hv hTV hTI hnot hs hi he
  refine ⟨hz,hsimple,S,hTS,hReq,hFit,hker,hred,hm,?_⟩
  intro hff
  exact H.nonsingular_canonical_ff_fixed_ne_bot D v hv hTV hi he S
    (hReq.le.trans (inf_le_right.trans (coreQuotientCentralizer_le_normalizer _)))
    hred hm hker hff hz

end CFSG.Quasithin.Chapter12.Section06
