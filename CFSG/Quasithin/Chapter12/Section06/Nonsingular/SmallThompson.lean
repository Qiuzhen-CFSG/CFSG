module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.ThompsonModule
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.ThreeFree

/-!
# Excluding the small Thompson case in the equal-residual branch

Assume L_v=K_v and J(T_v)≤Q. The literal quotient-action centralizer
C_{G_v}(L_v/O₂(L_v)) is normal in G_v, has order prime to three, and
contains J(T_v). The G_v-conjugate span of V_v is reduced. The proved
B.5 factorization consequence makes J(T_v) centralize this span. At the
preferred escaping point, the earlier Frattini argument says that J(T_v)
moves every normal overmodule of V_v, giving the required contradiction.

Consequently the preferred point satisfies L_v<K_v in the small Thompson
branch. The other Thompson case of12.6.11, component recognition, blocks,
splitting and fixed-space elimination remain to be proved. The earlier
T-invariance and TI inputs retain producer qt-d-1222-source and final
discharge owner qt-d-12634-source. All subgroups and quotient maps remain
those of the original centralizer setup.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
the small Thompson branch of Lemma12.6.11, printed p.825.
-/

public section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

omit [Finite G] in
private theorem normalizer_normalizes_coreQuotientCentralizer (B : Subgroup G) :
    normalizer (B : Set G) ≤ normalizer (coreQuotientCentralizer B : Set G) := by
  let f := (quotientAut (pCore 2 B)).comp B.normalizerMonoidHom
  simpa only [coreQuotientCentralizer,f,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
    f.ker.le_normalizer_map (normalizer (B : Set G)).subtype

/-- The actual small-case conjugate span is centralized by the actual J(T_v). -/
theorem SourceHypothesis.small_thompson_closure_centralized
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTv : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L)
    (heq : Lv L (v : G) = Kv (v : G)) :
    elementaryAbelianMaxJ (Tv T (v : G)) ≤
      centralizer (componentOrbit (Vv L V (v : G)) (Gv (v : G)) : Set G) := by
  let A := Gv (v : G)
  let B := Lv L (v : G)
  let C := A ⊓ coreQuotientCentralizer B
  let X := componentOrbit (Vv L V (v : G)) A
  have hXA : X ≤ A := iSup_conjugates_le_of_le_normalizer _ _ _
    ((Vv_le_V H.chosen.normalizes _).trans (V_le_Gv v)) A.le_normalizer
  have hnB : A ≤ normalizer (B : Set G) := by
    rw [show B = Kv (v : G) from heq]
    exact (normal_subgroupOf_iff_le_normalizer (Kv_le_Gv _)).mp (Kv_normalIn_Gv _)
  have hnC : A ≤ normalizer (C : Set G) :=
    (le_inf A.le_normalizer
      (hnB.trans (normalizer_normalizes_coreQuotientCentralizer B))).trans
      inf_normalizer_le_normalizer_inf
  let : (C.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer hnC
  have hr : IsPReduced 2 (X.subgroupOf A) := H.small_thompson_closure_reduced D v hv hTV hTv hJ heq
  obtain ⟨S,hTS,_⟩ := exists_sylow_with_Lv_normalizer T L H.chosen.sylow_normalizes_component (v : G)
  obtain ⟨hS,_,_,_,_⟩ := H.nonsingular_small_thompson D v hv hTv hJ S hTS
  have hj : (elementaryAbelianMaxJ (S : Subgroup A)).map A.subtype =
      elementaryAbelianMaxJ (Tv T (v : G)) := by
    rw [←elementaryAbelianMaxJ_map_injective A.subtype A.subtype_injective,hS]
  have hc : Rv T L (v : G) ≤ coreQuotientCentralizer B := by
    obtain ⟨e⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
    exact (Rv_eq_inf_coreQuotientCentralizer T L H.chosen.sylow_normalizes_component _
      (Lv_coreQuotient_center_eq_bot_of_A6 L (v : G) e)).le.trans inf_le_right
  have hJC : elementaryAbelianMaxJ (S : Subgroup A) ≤ C.subgroupOf A := by
    intro x hx
    exact ⟨x.property,hc (Q_le_Rv H.chosen v (hJ (hj ▸ mem_map_of_mem A.subtype hx)))⟩
  have h3 : Nat.Coprime 3 (Nat.card (C.subgroupOf A)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show C ≤ A from inf_le_left)).toEquiv]
    exact H.nonsingular_quotient_centralizer_three_free D v hv
  have hv2 : orderOf (v : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian _ v.property)
    (fun he => nonsingular_ne_one D hv (Subtype.ext he))
  have hsq : IsSQTK KnownSimple.IsKnownSimple A := H.source.simpleQTKE.twoLocal_sqtk
    (isTwoLocal_involution_centralizer hv2)
  have hh := ChapterB.SourceInduction.thompson_centralizes_reduced_of_three_free_normal
    (X.subgroupOf A) hr hsq (S : Subgroup A) (C.subgroupOf A)
    (hr.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal S)) hJC h3
  intro j hjJ x hx
  obtain ⟨j,hjS,rfl⟩ := hj.symm ▸ hjJ
  exact congrArg A.subtype (hh hjS ⟨x,hXA hx⟩ hx)

/-- The preferred escaping source point has strict residual enlargement in the small Thompson case. -/
theorem SourceHypothesis.exists_preferred_small_thompson_residual_strict
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      (elementaryAbelianMaxJ (Tv T (w : G)) ≤ Q T L → Lv L (w : G) < Kv (w : G)) := by
  obtain ⟨w,hw,hescape,hs,hi,_,_,hm,_⟩ :=
    H.exists_preferred_nonsingular_thompson_reductions D hTV hTI v hv he
  refine ⟨w,hw,hescape,hs,hi,?_⟩
  intro hJ
  obtain ⟨_,_,_,hLK⟩ := D.nonsingular_local_structure H.chosen H.source.quasisimple w hw
  apply (lt_iff_le_and_ne).mpr
  refine ⟨hLK,?_⟩
  intro heq
  exact hm hJ heq _ (le_componentOrbit _ _) (le_normalizer_componentOrbit _ _)
    (H.small_thompson_closure_centralized D w hw hTV hs hJ heq)
end CFSG.Quasithin.Chapter12.Section06
