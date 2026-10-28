module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.CanonicalFF
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.PreferredCanonicalModule

/-!
# The preferred A7 block with its FF premise discharged

Keep the original preferred nonsingular point throughout Sylow selection,
normalizer escape and block propagation. The centralizer calculation now
places the actual canonical U in T_v and constructs its FF witness. The
relative Sylow index at most two excludes both higher binary linear rows,
so K_v is an A7-block and its full moved module is the natural six-space.
The theorem includes its order 64, zero fixed subgroup and direct module
decomposition with the original quotient/action maps.

This is the nontrivial original C_V(L) branch of 12.6.15--18. The remaining
HS/J4 exclusions, general 12.6.13(3), group splitting and fixed-space
elimination remain with this source owner. Earlier invariance/TI retain
qt-d-1222-source and final discharge retains qt-d-12634-source; neither
12.6.2 nor 12.6.23 is asserted. Source: Aschbacher--Smith, printed
pp.825--828, combined manuscript of 1 March 2004.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The same source-preferred point has its canonical FF witness and the
full natural A7 moved module. No FF or module-recognition premise remains. -/
theorem SourceHypothesis.exists_preferred_nonsingular_canonical_ff_of_fixed
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
      Gv (w : G) ⊓ centralizer (Vv L V (w : G) : Set G) ≤ M L ∧
      ChapterC.IsAlternatingBlock L 8 ∧ ChapterC.IsAlternatingBlock (Lv L (w : G)) 6 ∧
      ChapterC.IsBlock ((Kv (w : G)).subgroupOf (Gv (w : G))) ∧
      ∃ S : Sylow 2 (Gv (w : G)),
        let S₀ := (S : Subgroup (Gv (w : G))).map (Gv (w : G)).subtype
        let J := Kv (w : G) ⊔ S₀
        let E := reducedTwoSubgroup J
        letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
        Tv T (w : G) ≤ S₀ ∧ (Tv T (w : G)).relIndex S₀ ≤ 2 ∧
        generalizedFitting J = pCore 2 J ∧ centralizer (E : Set J) = pCore 2 J ∧
        U (Kv (w : G)) S₀ = E.map J.subtype ∧ U (Kv (w : G)) S₀ ≤ Tv T (w : G) ∧
        ⁅U (Kv (w : G)) S₀,Lv L (w : G)⁆ = Vv L V (w : G) ∧
        ⁅U (Kv (w : G)) S₀,Kv (w : G)⁆ =
          (ChapterC.blockU (Kv (w : G))).map (Kv (w : G)).subtype ∧
        IsFFModule (ChapterB.InternalThompsonAction.action E) ∧
        Nonempty (Star (Kv (w : G)) ≃* alternatingGroup (Fin 7)) ∧
        CanonicalSevenMoved E ((Kv (w : G)).subgroupOf J) ∧
        ChapterC.IsAlternatingBlock (Kv (w : G)) 7 ∧
        Nat.card (⁅U (Kv (w : G)) S₀,Kv (w : G)⁆ : Subgroup G) = 64 ∧
        (⁅U (Kv (w : G)) S₀,Kv (w : G)⁆ : Subgroup G) ⊓
          centralizer (Kv (w : G) : Set G) = ⊥ ∧
        U (Kv (w : G)) S₀ = ⁅U (Kv (w : G)) S₀,Kv (w : G)⁆ ⊔
          (U (Kv (w : G)) S₀ ⊓ centralizer (Kv (w : G) : Set G)) := by
  obtain ⟨F,hF,hproj⟩ := D.core_marking_of_fixed_ne_bot H.chosen hz
  obtain ⟨w,hw,hew,hs,hi,hpref,hctrl⟩ :=
    H.exists_preferred_nonsingular_core_control D hTV hTI F hF hproj v hv he
  have hlt := H.nonsingular_residual_strict_of_normalizer_control D hTV w hw hew hs hctrl
  have hnot : ¬ Kv (w : G) ≤ M L := fun h => hlt.ne (H.Kv_eq_Lv_of_le_normalizer D w hw h).symm
  have hnq : ¬ IsQuasisimple (Kv (w : G)) := fun h =>
    hz (H.nonsingular_quasisimple_fixed_eq_bot D w hw h hTV hi hnot)
  obtain ⟨hL,hA,_,hC,hCB,S,hTS,hN,hReq,hFit,hker,hred,hm⟩ :=
    H.nonsingular_residual_block_of_not_quasisimple D w hw hTV hnq hs hi hnot
  have hno : ∀ P : Sylow 2 G, (P : Subgroup G) ≤ Gv (w : G) →
      ¬ Tv T (w : G) ≤ (P : Subgroup G) := fun P hPG hTP =>
    H.nonsingular_not_short_of_preferred_ambient_sylow D hTV hz F hF hproj
      w hw hnot hs hi hpref P hPG hTP hL.2.1
  have hidx := nonsingular_sylow_index_le_two_of_no_ambient T (w : G) hi hno S hTS
  have hc := H.preferred_moved_centralizer_le D hTV F hF hproj w hw hpref
  let S₀ := (S : Subgroup (Gv (w : G))).map (Gv (w : G)).subtype
  let J := Kv (w : G) ⊔ S₀
  let E := reducedTwoSubgroup J
  let : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
  let K := (Kv (w : G)).subgroupOf J
  have hRN : R L (Kv (w : G)) S₀ (w : G) ≤ normalizer (Lv L (w : G) : Set G) := by
    rw [hReq]
    exact inf_le_right.trans (coreQuotientCentralizer_le_normalizer _)
  have hk : centralizer (E : Set J) = pCore 2 J := by
    rw [hred] at hker
    change centralizer ((E.map J.subtype).comap J.subtype : Set J) = _ at hker
    rwa [comap_map_eq_self_of_injective J.subtype_injective] at hker
  have hlocal := H.nonsingular_canonical_local_commutator D w hw hL.2.1 S hRN hred hm
  have hres := H.nonsingular_canonical_residual_commutator D w hw hC S hred hm
  have hgen := H.local_thompson_generation D w hw hTV hs
    (H.nonsingular_thompson_not_le_core_of_not_quasisimple D w hw hTV hnq hs hi hnot)
  obtain ⟨hUT,hff⟩ := H.nonsingular_canonical_ff_of_moved_control D w hw hs hc hgen S hTS hred hlocal
  have hseven := H.nonsingular_canonical_ff_seven_of_index_two D w hw hTV hi hnot S hidx hRN hk hff
  have hmod := H.nonsingular_canonical_seven_moved D w hw S hseven hred hm hk hff
  have hblock := nonsingular_canonical_seven_block (w : G) S₀ (map_subtype_le _)
    hC hk hred hres hmod
  have hp := canonical_seven_moved_properties_map E K hmod J.subtype J.subtype_injective
  rw [map_commutator,map_subgroupOf_eq_of_le (show Kv (w : G) ≤ J from le_sup_left),←hred] at hp
  exact ⟨w,hw,hew,hs,hi,hlt,hnot,hc,hL,hA,hCB,S,hTS,hidx,hFit,hk,hred,hUT,
    hlocal,hres,hff,hseven,hmod,hblock,hp⟩

end CFSG.Quasithin.Chapter12.Section06
