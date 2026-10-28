module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.ReducedComparison
public import Theory.Representation.BinaryOffender.Homogeneous.Core
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates

/-!
# Centrality of the reduced moved module in the original R_v

The action of R_v centralizes the actual A₆ image of L_v. Its two-group
image preserves the Irr⁺ moved space, so the odd centralizer theorem makes
R_v fix that space pointwise. This locates the literal [R₂(G_v),L_v] in
Ω₁(Z(R_v)). Its literal join with V_v is normal elementary in C_LT(v),
and has exactly R_v as its centralizer there. The preferred-point consumer
constructs this common module from the original source hypotheses. The
comparison [R₂(G_v),L_v]=V_v, component recognition, blocks, splitting and
fixed-space elimination are still required. T-invariance and TI retain
producer qt-d-1222-source and final discharge owner qt-d-12634-source.

Source: Aschbacher--Smith,12.6.11 and A.1.41, printed pp.825 and31.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original R_v centralizes the entire reduced moved module. -/
theorem SourceHypothesis.local_core_centralizes_reduced_moved
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hn : Gv (v : G) ≤ normalizer (Lv L (v : G) : Set G)) :
    let A := Gv (v : G)
    let U := reducedTwoSubgroup A
    letI : IsElementaryAbelian 2 U := isPReduced_reducedPSubgroup.elementary
    let ρ := ChapterB.InternalThompsonAction.action U
    let B := ((Lv L (v : G)).subgroupOf A).map
      (ChapterB.InternalThompsonAction.actionMk U)
    IsIrrPlus ρ B (subspaceCommutator ρ ⊤ B) →
    Rv T L (v : G) ≤ centralizer ((⁅U.map A.subtype,Lv L (v : G)⁆ : Subgroup G) : Set G) := by
  let A := Gv (v : G)
  let U := reducedTwoSubgroup A
  let : IsElementaryAbelian 2 U := isPReduced_reducedPSubgroup.elementary
  let ρ := ChapterB.InternalThompsonAction.action U
  let q := ChapterB.InternalThompsonAction.actionMk U
  let X := (Lv L (v : G)).subgroupOf A
  let B := X.map q
  let R := (Rv T L (v : G)).subgroupOf A
  let P := R.map q
  let : X.Normal := normal_subgroupOf_of_le_normalizer hn
  let : B.Normal := (inferInstance : X.Normal).map q (QuotientGroup.mk'_surjective _)
  change IsIrrPlus ρ B (subspaceCommutator ρ ⊤ B) → _
  intro hi
  have hX : X.map A.subtype = Lv L (v : G) := map_subgroupOf_eq_of_le (Lv_le_Gv L (v : G))
  have hRA : Rv T L (v : G) ≤ A := (pCoreIn_le 2 _).trans inf_le_right
  obtain ⟨e⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
  have hRC : Rv T L (v : G) ≤ coreQuotientCentralizer (Lv L (v : G)) := by
    rw [Rv_eq_inf_coreQuotientCentralizer T L H.chosen.sylow_normalizes_component _
      (Lv_coreQuotient_center_eq_bot_of_A6 L (v : G) e)]
    exact inf_le_right
  have hcomm : ⁅R,X⁆ ≤ X.pCoreIn 2 := by
    apply commutator_le.mpr
    intro r hr l hl
    have hh := ((mem_coreQuotientCentralizer_iff _ _).mp (hRC hr)).2 l.val hl
    rw [←hX,←map_pCoreIn_of_injective 2 X A.subtype A.subtype_injective] at hh
    obtain ⟨c,hc,he⟩ := hh
    exact (Subtype.ext he : c = ⁅r,l⁆) ▸ hc
  have hPB : P ≤ centralizer (B : Set (ChapterB.InternalThompsonAction.ActionQuotient U)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    change ⁅R.map q,X.map q⁆ = ⊥
    rw [←map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    have hk : q.ker = centralizer (U : Set A) := QuotientGroup.ker_mk' _
    rw [hk]
    exact hcomm.trans (normal_pCore_le_centralizer_reducedPSubgroup 2 X)
  have hP : IsPGroup 2 P := ((isPGroup_pCoreIn 2 (LT T L ⊓ A)).of_injective
    (subgroupOfEquivOfLe hRA).toMonoidHom (subgroupOfEquivOfLe hRA).injective).map q
  have hstable : P ≤ subspaceStabilizer ρ (subspaceCommutator ρ ⊤ B) := by
    apply subspaceCommutator_invariant_normalizer ρ
    · exact le_subspaceStabilizer ρ ⊤ (by simp)
    · exact le_normalizer_of_normal
  have hfix := Homogeneous.IsIrrPlus.le_fixedSpace_of_twoGroup_centralizes ρ hi hP hPB hstable
  have hmap : (⁅U,X⁆ : Subgroup A).map A.subtype = ⁅U.map A.subtype,Lv L (v : G)⁆ := by
    rw [map_commutator,hX]
  intro r hr w hw
  rw [←hmap] at hw
  obtain ⟨w,hwW,rfl⟩ := hw
  let u : Additive U := Additive.ofMul ⟨w,commutator_le_left U X hwW⟩
  have hu : u ∈ subspaceCommutator ρ ⊤ B := by
    change u ∈ subspaceCommutator (NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ⊤ (X.map q)
    rw [←NormalElementaryQuotient.commutatorSpace_eq U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) X]
    exact hwW
  let r' : A := ⟨r,hRA hr⟩
  have he := hfix hu (⟨q r',mem_map_of_mem q (show r' ∈ R from hr)⟩ : P)
  have he' := congrArg (fun z : Additive U => (z.toMul : A)) he
  change ((ChapterB.InternalThompsonAction.action U
    (ChapterB.InternalThompsonAction.actionMk U r') u).toMul : A) = (u.toMul : A) at he'
  rw [ChapterB.InternalThompsonAction.action_apply] at he'
  exact congrArg A.subtype (mul_inv_eq_iff_eq_mul.mp he').symm
end CFSG.Quasithin.Chapter12.Section06

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original V_v and the literal reduced commutator lie in one elementary
local module, with exactly the original kernel R_v. -/
theorem SourceHypothesis.reduced_moved_common_module
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTv : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hn : Gv (v : G) ≤ normalizer (Lv L (v : G) : Set G))
    (hc : Gv (v : G) ⊓ centralizer (Vv L V (v : G) : Set G) ≤ M L) :
    let A := Gv (v : G)
    let U := reducedTwoSubgroup A
    letI : IsElementaryAbelian 2 U := isPReduced_reducedPSubgroup.elementary
    let ρ := ChapterB.InternalThompsonAction.action U
    let B := ((Lv L (v : G)).subgroupOf A).map
      (ChapterB.InternalThompsonAction.actionMk U)
    IsIrrPlus ρ B (subspaceCommutator ρ ⊤ B) →
    let W := ⁅U.map A.subtype,Lv L (v : G)⁆
    let X := Vv L V (v : G) ⊔ W
    X ≤ Rv T L (v : G) ∧ IsElementaryAbelian 2 X ∧
      ((X.subgroupOf (LT T L ⊓ A)).Normal) ∧
      (LT T L ⊓ A) ⊓ centralizer (X : Set G) = Rv T L (v : G) := by
  let A := Gv (v : G)
  let U := reducedTwoSubgroup A
  let : IsElementaryAbelian 2 U := isPReduced_reducedPSubgroup.elementary
  let ρ := ChapterB.InternalThompsonAction.action U
  let B := ((Lv L (v : G)).subgroupOf A).map
    (ChapterB.InternalThompsonAction.actionMk U)
  change IsIrrPlus ρ B (subspaceCommutator ρ ⊤ B) → _
  intro hi
  let U₀ := U.map A.subtype
  let W := ⁅U₀,Lv L (v : G)⁆
  let X := Vv L V (v : G) ⊔ W
  let J := LT T L ⊓ A
  have hnU : A ≤ normalizer (U₀ : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      U.le_normalizer_map A.subtype
  have hWU : W ≤ U₀ := le_normalizer_iff_commutator_le_left.mp
    ((Lv_le_Gv L _).trans hnU)
  have hUR := (H.reduced_point_le_local_core v hTv hn hc).2
  have hXR : X ≤ Rv T L (v : G) := sup_le (Vv_le_Rv H.chosen v) (hWU.trans hUR)
  have hRW := H.local_core_centralizes_reduced_moved D v hv hn hi
  let : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.map A.subtype
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWU
  let := Vv_elementary H.chosen.normalizes (v : G)
  have hXV : IsElementaryAbelian 2 X := IsElementaryAbelian.sup_of_le_centralizer
    (le_centralizer_iff.mp ((Vv_le_Rv H.chosen v).trans hRW))
  have hnW : A ≤ normalizer (W : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hnU hg),mem_normalizer_iff_map_conj_eq.mp (hn hg)]
  have hnV : J ≤ normalizer (Vv L V (v : G) : Set G) :=
    normalizes_Vv_of_normalizes J _
      (inf_le_left.trans (sup_le H.chosen.normalizes hTV)) (inf_le_right.trans hn)
  have hnX : J ≤ normalizer (X : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,Subgroup.map_sup,
      mem_normalizer_iff_map_conj_eq.mp (hnV hg),
      mem_normalizer_iff_map_conj_eq.mp (hnW hg.2)]
  refine ⟨hXR,hXV,normal_subgroupOf_of_le_normalizer hnX,?_⟩
  apply le_antisymm
  · exact ((inf_le_inf le_rfl (centralizer_le (show Vv L V (v : G) ≤ X from le_sup_left))).trans
      (H.local_moved_centralizer_eq_core D v hv hTV).le)
  · apply le_inf (pCoreIn_le 2 _)
    apply le_centralizer_iff.mp
    exact sup_le (le_centralizer_iff.mp (H.Rv_centralizes_moved D v hv hTV))
      (le_centralizer_iff.mp hRW)

/-- The preferred equal-residual branch now carries the actual common
module and its faithful local quotient, with no comparison-module premise. -/
theorem SourceHypothesis.exists_preferred_reduced_common_module
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      (Lv L (w : G) = Kv (w : G) →
        let A := Gv (w : G)
        let W := ⁅(reducedTwoSubgroup A).map A.subtype,Lv L (w : G)⁆
        let X := Vv L V (w : G) ⊔ W
        ¬ ((Vv L V (w : G)).subgroupOf A).Normal ∧
        X ≤ Rv T L (w : G) ∧ IsElementaryAbelian 2 X ∧
        (X.subgroupOf (LT T L ⊓ A)).Normal ∧
        (LT T L ⊓ A) ⊓ centralizer (X : Set G) = Rv T L (w : G)) := by
  obtain ⟨w,hw,he,hs,hi,hred⟩ :=
    H.exists_preferred_nonsingular_Kv_reductions D hTV hTI v hv he
  refine ⟨w,hw,he,hs,hi,fun heq => ?_⟩
  have hn : Gv (w : G) ≤ normalizer (Lv L (w : G) : Set G) := by
    rw [heq]
    exact (normal_subgroupOf_iff_le_normalizer (Kv_le_Gv _)).mp (Kv_normalIn_Gv _)
  have hc : Gv (w : G) ⊓ centralizer (Vv L V (w : G) : Set G) ≤ M L :=
    (inf_le_inf le_rfl (Subgroup.centralizer_le_normalizer _)).trans (hred heq).2.2.1
  have hJ : ¬ Stellmacher.elementaryAbelianMaxJ (Tv T (w : G)) ≤ Q T L := by
    intro hJ
    exact H.small_thompson_moves_normal_overmodule D w hw hs hJ he hc
      (componentOrbit (Vv L V (w : G)) (Gv (w : G)))
      (le_componentOrbit _ _) (le_normalizer_componentOrbit _ _)
      (H.small_thompson_closure_centralized D w hw hTV hs hJ heq)
  have hg := (H.nonsingular_thompson_generation D w hw hTV hs hJ).2.1
  have hff := H.reduced_point_ff D w hw hs hn hc hg
  let A := Gv (w : G)
  let U := reducedTwoSubgroup A
  let : IsElementaryAbelian 2 U := isPReduced_reducedPSubgroup.elementary
  let ρ := ChapterB.InternalThompsonAction.action U
  have hsq : IsSQTK KnownSimple.IsKnownSimple A := H.source.simpleQTKE.twoLocal_sqtk
    (isTwoLocal_involution_centralizer (orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian _ w.property)
      (fun hh => nonsingular_ne_one D hw (Subtype.ext hh))))
  let c : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple
      (ChapterB.InternalThompsonAction.ActionQuotient U) := {
    Cover := A
    kernel := centralizer (U : Set A)
    sqtk := hsq
    equiv := MulEquiv.refl _ }
  have hclass := ChapterB.SourceInduction.offenderSubgroup_adequateAlternative ρ
    (ChapterB.InternalThompsonAction.action_faithful U)
    isPReduced_reducedPSubgroup.quotient_pCore_eq_bot c
  have hirr := H.reduced_point_moved_irrPlus D w hw hn hff.2 hclass
  exact ⟨(hred heq).2.2.2,H.reduced_moved_common_module D w hw hTV hs hn hc hirr⟩
end CFSG.Quasithin.Chapter12.Section06
