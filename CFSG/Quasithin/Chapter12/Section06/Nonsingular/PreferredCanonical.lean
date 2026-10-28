module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.CanonicalLayers
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.CanonicalModels
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.PreferredResidualBlock

/-!
# Canonical layers at the unchanged preferred point

At the source-preferred escaping point with nontrivial original C_V(L),
the proved relative blocks and canonical containment now give the exact
identities [U,L_v]=V_v and [U,K_v]=U(K_v). The literal A6 image in the
simple two-core quotient is proper. The source Sylow bound remains at
most two. All these layer and section premises are discharged here.

The final model implication retains the canonical FF hypothesis explicitly.
Its proof leaves only A7, SL4(2), or SL5(2), using actual quotient
isomorphisms. Constructing that FF witness, the A7 block identification,
HS/J4 exclusions, splitting and fixed-space elimination remain in this
same owner. Earlier invariance/TI retain producer qt-d-1222-source and
final discharge remains with qt-d-12634-source. Neither 12.6.2 nor 12.6.23
is asserted. Source: Aschbacher--Smith 12.6.13--18, printed pp.826--827,
combined manuscript of 1 March 2004.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The source-preferred point carries the original canonical layers and proper
A6 section. Only the FF premise remains explicit in the model classification. -/
theorem SourceHypothesis.exists_preferred_nonsingular_canonical_layers_of_fixed
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hz : ZV L V ≠ ⊥)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      Lv L (w : G) < Kv (w : G) ∧ ¬ Kv (w : G) ≤ M L ∧
      ChapterC.IsAlternatingBlock L 8 ∧ ChapterC.IsAlternatingBlock (Lv L (w : G)) 6 ∧
      ChapterC.IsBlock ((Kv (w : G)).subgroupOf (Gv (w : G))) ∧
      ∃ S : Sylow 2 (Gv (w : G)),
        let S₀ := (S : Subgroup (Gv (w : G))).map (Gv (w : G)).subtype
        let J := Kv (w : G) ⊔ S₀
        let E := reducedTwoSubgroup J
        letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
        let A := ((Lv L (w : G)).subgroupOf (Kv (w : G))).map
          (QuotientGroup.mk' (pCore 2 (Kv (w : G))))
        Tv T (w : G) ≤ S₀ ∧ (Tv T (w : G)).relIndex S₀ ≤ 2 ∧
        generalizedFitting J = pCore 2 J ∧ centralizer (E : Set J) = pCore 2 J ∧
        U (Kv (w : G)) S₀ = E.map J.subtype ∧
        ⁅U (Kv (w : G)) S₀,Lv L (w : G)⁆ = Vv L V (w : G) ∧
        ⁅U (Kv (w : G)) S₀,Kv (w : G)⁆ =
          (ChapterC.blockU (Kv (w : G))).map (Kv (w : G)).subtype ∧
        A ≠ ⊤ ∧ Nonempty ((A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 6)) ∧
        (IsFFModule (ChapterB.InternalThompsonAction.action E) →
          Nonempty (Star (Kv (w : G)) ≃* alternatingGroup (Fin 7)) ∨
          Nonempty (Star (Kv (w : G)) ≃* SL(4,ZMod 2)) ∨
          Nonempty (Star (Kv (w : G)) ≃* SL(5,ZMod 2))) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,hL,hA,hU,hC,hCB,S,hTS,hidx,hN,hReq,hF,hker,hred,hm⟩ :=
    H.exists_preferred_nonsingular_residual_block_of_fixed D hTV hTI hz v hv he
  let P := (S : Subgroup (Gv (w : G))).map (Gv (w : G)).subtype
  let J := Kv (w : G) ⊔ P
  let E := reducedTwoSubgroup J
  let : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
  have hRN : R L (Kv (w : G)) P (w : G) ≤ normalizer (Lv L (w : G) : Set G) := by
    rw [hReq]
    exact inf_le_right.trans (coreQuotientCentralizer_le_normalizer _)
  have hk : centralizer (E : Set J) = pCore 2 J := by
    rw [hred] at hker
    change centralizer ((E.map J.subtype).comap J.subtype : Set J) = _ at hker
    rwa [comap_map_eq_self_of_injective J.subtype_injective] at hker
  obtain ⟨hproper,hmodel⟩ := H.nonsingular_canonical_proper_section D w hw hnot S hRN
  exact ⟨w,hw,he,hs,hi,hlt,hnot,hL,hA,hCB,S,hTS,hidx,hF,hk,hred,
    H.nonsingular_canonical_local_commutator D w hw hL.2.1 S hRN hred hm,
    H.nonsingular_canonical_residual_commutator D w hw hC S hred hm,
    hproper,hmodel,fun hff => H.nonsingular_canonical_ff_models D w hw hTV hi hnot S hRN hk hff⟩
end CFSG.Quasithin.Chapter12.Section06
