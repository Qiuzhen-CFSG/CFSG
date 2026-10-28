module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerResidual
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourGraphCentralizer.FixedRootAction
public import Theory.SpecificGroups.PSL3Two.AlternatingFourFixer
public import Theory.GroupTheory.PResidual.PGroupFactor
public import Theory.SpecificGroups.SymmetricFour.ResidualFactorization
/-!
# Excluding the linear residual in the graph-centralizer quotient

In the literal quotient C_G(f)/⟨f⟩, the root induces a nonidentity
conjugation automorphism of O²(C_G(f)/⟨f⟩). It fixes the actual first-endpoint
A₄ residual pointwise. The binary cubic in the second endpoint proves that
the action is nontrivial; quotient injectivity on ordinary endpoints retains
that witness. The pointwise fixer of any A₄ in Aut(PSL₃(2)) is trivial, so
this excludes PSL₃(2) and leaves A₆ in the existing recognition alternative.

Source: Aschbacher–Smith F.5.5, printed p.302.
-/
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneRadical UnitaryFourShortRoot
open UnitaryTwo.ShortRootFusion
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
local notation "C2" => Multiplicative (ZMod 2)
variable {G G0 : Type*} [Group G] [Group G0]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)
private theorem graph_not_mem_D (hi : Function.Injective i) (b : Bool) :
    Source.graphElement c i ∉ Dendpoint c i b := by
  rintro ⟨a,ha,he⟩
  have hh : ordinaryInclusion b a = modelGraph b :=
    endpointMap_injective c i hi b (he.trans (endpointMap_graph c i b).symm)
  cases b
  · have hh' := congrArg (fun x : modelEndpoint false => x.val.right) hh
    exact (by decide : (1 : UnitaryFourOuter.C2) ≠ UnitaryFourOuter.generator) hh'
  · have hh' := congrArg (fun x : modelEndpoint true => x.val.right) hh
    exact (by decide : (1 : UnitaryFourOuter.C2) ≠ UnitaryFourOuter.generator) hh'

def sourceEndpointGraphMap (b : Bool) : Dendpoint c i b →* graphCentralQuotient c i :=
  (QuotientGroup.mk' (zpowers (graphInCentralizer c i))).comp
    (inclusion ((Dendpoint_le_E c i b).trans inf_le_right))
variable [Finite G] (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)

include h in
theorem sourceEndpointGraphMap_injective (b : Bool) : Function.Injective (sourceEndpointGraphMap c i b) := by
  apply (sourceEndpointGraphMap c i b).ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro x hx
  apply mem_bot.mpr
  change QuotientGroup.mk' (zpowers (graphInCentralizer c i))
    (inclusion ((Dendpoint_le_E c i b).trans inf_le_right) x) = 1 at hx
  rcases (graph_quotient_eq_one_iff c i z h _).mp hx with hx | hx
  · exact Subtype.ext (show x.val = 1 from congrArg (fun x : C c i => x.val) hx)
  · exact False.elim (graph_not_mem_D c i h.embedding_injective b
      (by
        have he : x.val = Source.graphElement c i := congrArg Subtype.val hx
        exact he ▸ x.property))

private def cubicPlane : planeParabolic 1 hn :=
  ⟨projection 1 hn (UnitaryFourGraphCentralizer.cubicWord F σ hσ),
    ⟨_,UnitaryFourGraphCentralizer.cubicWord_plane F σ hσ,rfl⟩⟩

omit [Finite G] in
private theorem cubicPlane_fixed : cubicPlane ∈ modelFixed true := by
  change ordinaryInclusion true cubicPlane ∈ centralizer ({modelGraph true} : Set (modelEndpoint true))
  rw [mem_centralizer_singleton_iff]
  have he : Extension.projectiveAut 1 hn
      (projection 1 hn (UnitaryFourGraphCentralizer.cubicWord F σ hσ)) =
      projection 1 hn (UnitaryFourGraphCentralizer.cubicWord F σ hσ) :=
    (Extension.projectiveAut_project 1 hn _).trans
      (congrArg (projection 1 hn) (UnitaryFourGraphCentralizer.cubicWord_fixed F σ hσ))
  apply Subtype.ext
  apply SemidirectProduct.ext
  · change projection 1 hn (UnitaryFourGraphCentralizer.cubicWord F σ hσ) *
        Extension.projectiveAction 1 hn 1 1 =
      1 * Extension.projectiveAction 1 hn UnitaryFourOuter.generator
        (projection 1 hn (UnitaryFourGraphCentralizer.cubicWord F σ hσ))
    simpa only [map_one, MulAut.one_apply, one_mul, mul_one,
      Extension.projectiveAction_generator] using he.symm
  · exact one_mul _ |>.trans (mul_one _).symm

omit [Finite G] in
private theorem cubicPlane_cube : cubicPlane ^ 3 = 1 := by
  apply Subtype.ext
  change projection 1 hn (UnitaryFourGraphCentralizer.cubicWord F σ hσ) ^ 3 = 1
  rw [←map_pow, UnitaryFourGraphCentralizer.cubicWord_cube, map_one]

omit [Finite G] in
include h in
private theorem root_cubicPlane_not_commute :
    ¬ Commute (rootElement c i z) (ordinaryMap c i true cubicPlane) := by
  rw [source_root_eq_planeParameter c i z h]
  intro hc
  have he : (planeParameterMap (Multiplicative.ofAdd (longParameter F σ))) * cubicPlane =
      cubicPlane * (planeParameterMap (Multiplicative.ofAdd (longParameter F σ))) := by
    apply ordinaryMap_injective c i h.embedding_injective true
    change (ordinaryMap c i true) (_ * _) = (ordinaryMap c i true) (_ * _)
    rw [map_mul, map_mul]
    exact hc.eq
  apply UnitaryFourGraphCentralizer.longRoot_cubicWord_not_commute F σ hσ
  have hh := congrArg (fun a : planeParabolic 1 hn => a.val) he
  change projection 1 hn (unipotentSU F σ hσ (longParameter F σ)) *
      projection 1 hn (UnitaryFourGraphCentralizer.cubicWord F σ hσ) =
    projection 1 hn (UnitaryFourGraphCentralizer.cubicWord F σ hσ) *
      projection 1 hn (unipotentSU F σ hσ (longParameter F σ)) at hh
  exact projection_injective 1 hn (by simpa only [map_mul] using hh)

include h in
private theorem root_mem_D_plane : rootElement c i z ∈ Dendpoint c i true := by
  rw [Dendpoint_eq_range_inf_C c i h.embedding_injective true]
  constructor
  · refine ⟨planeParameterMap (Multiplicative.ofAdd (longParameter F σ)), ?_⟩
    exact (source_root_eq_planeParameter c i z h).symm
  · exact mem_centralizer_singleton_iff.mpr (source_graph_commutes_root c i z h).eq.symm

def sourceRootInGraphCentralizer : C c i := ⟨rootElement c i z,
  mem_centralizer_singleton_iff.mpr (source_graph_commutes_root c i z h).eq.symm⟩

def sourceEndpointResidualGraphMap (b : Bool) : pResidual 2 (Dendpoint c i b) →*
    pResidual 2 (graphCentralQuotient c i) :=
  ((sourceEndpointGraphMap c i b).comp (pResidual 2 (Dendpoint c i b)).subtype).codRestrict _
    (fun x => map_pResidual_le 2 (sourceEndpointGraphMap c i b)
      (mem_map_of_mem (sourceEndpointGraphMap c i b) x.property))

include h in
theorem sourceEndpointResidualGraphMap_injective (b : Bool) :
    Function.Injective (sourceEndpointResidualGraphMap c i b) := by
  intro a b hab
  exact Subtype.ext (sourceEndpointGraphMap_injective c i z h _ (congrArg Subtype.val hab))

def sourceEndpointResidualEquiv (b : Bool) :
    pResidual 2 (Dendpoint c i b) ≃* alternatingGroup (Fin 4) :=
  (pResidualEquivOfPGroupFactor 2 (source_Dendpoint_equiv c i h.embedding_injective b)
    (IsPGroup.of_card (n:=1) (by simp [Nat.card_eq_fintype_card]))).trans
      (MulEquiv.subgroupCongr Theory.SpecificGroups.SymmetricFourResidual.residual_eq)

def sourceRootResidualAction : MulAut (pResidual 2 (graphCentralQuotient c i)) :=
  MulAut.conjNormal (QuotientGroup.mk' (zpowers (graphInCentralizer c i)) (sourceRootInGraphCentralizer c i z h))

include h in
theorem sourceRootResidualAction_fixes_point (x : pResidual 2 (Dendpoint c i false)) :
    sourceRootResidualAction c i z h (sourceEndpointResidualGraphMap c i false x) =
      sourceEndpointResidualGraphMap c i false x := by
  apply Subtype.ext
  change QuotientGroup.mk' _ (sourceRootInGraphCentralizer c i z h) *
      QuotientGroup.mk' _ (inclusion ((Dendpoint_le_E c i false).trans inf_le_right) x.val) *
      (QuotientGroup.mk' _ (sourceRootInGraphCentralizer c i z h))⁻¹ =
    QuotientGroup.mk' _ (inclusion ((Dendpoint_le_E c i false).trans inf_le_right) x.val)
  rw [←map_inv, ←map_mul, ←map_mul]
  apply congrArg
  have hx : x.val.val ∈ centralizer ({rootElement c i z} : Set G) := by
    rw [source_root_centralizer c i z h]
    exact (Dendpoint_le_E c i false x.val.property).1
  apply Subtype.ext
  change rootElement c i z * x.val.val * (rootElement c i z)⁻¹ = x.val.val
  rw [←mem_centralizer_singleton_iff.mp hx, mul_inv_cancel_right]

include h in
theorem sourceRootResidualAction_ne_one : sourceRootResidualAction c i z h ≠ 1 := by
  let a : Dendpoint c i true := ⟨ordinaryMap c i true cubicPlane, ⟨_,cubicPlane_fixed,rfl⟩⟩
  have ha3 : a ^ 3 = 1 := by
    apply Subtype.ext
    change ordinaryMap c i true cubicPlane ^ 3 = 1
    rw [←map_pow, cubicPlane_cube, map_one]
  have haR : a ∈ pResidual 2 (Dendpoint c i true) :=
    mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one ha3))
  let r : Dendpoint c i true := ⟨rootElement c i z,root_mem_D_plane c i z h⟩
  intro h1
  have hfix := DFunLike.congr_fun h1 (sourceEndpointResidualGraphMap c i true ⟨a,haR⟩)
  have he := congrArg Subtype.val hfix
  change sourceEndpointGraphMap c i true r * sourceEndpointGraphMap c i true a *
      (sourceEndpointGraphMap c i true r)⁻¹ = sourceEndpointGraphMap c i true a at he
  have hc : r * a = a * r := sourceEndpointGraphMap_injective c i z h true (by
    simpa only [map_mul] using (mul_inv_eq_iff_eq_mul.mp he))
  exact root_cubicPlane_not_commute c i z h (congrArg Subtype.val hc)

include h in
theorem source_graph_residual_not_psl :
    ¬ Nonempty (pResidual 2 (graphCentralQuotient c i) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := by
  rintro ⟨e⟩
  let j := sourceEndpointResidualGraphMap c i false
  let U := j.range
  let eU : U ≃* alternatingGroup (Fin 4) :=
    (MonoidHom.ofInjective (sourceEndpointResidualGraphMap_injective c i z h false)).symm.trans
      (sourceEndpointResidualEquiv c i z h false)
  have hfix : sourceRootResidualAction c i z h ∈
      fixingSubgroup (MulAut (pResidual 2 (graphCentralQuotient c i)))
        (U : Set (pResidual 2 (graphCentralQuotient c i))) := by
    apply (mem_fixingSubgroup_iff _).mpr
    rintro _ ⟨x,rfl⟩
    exact sourceRootResidualAction_fixes_point c i z h x
  have hf := Matrix.PSL3Two.alternatingFour_fixer_eq_bot (U.map e.toMonoidHom)
    ((e.subgroupMap U).symm.trans eU)
  rw [←MulAut.map_fixer e U] at hf
  have hb := (map_eq_bot_iff_of_injective _ (MulAut.congr e).injective).mp hf
  rw [hb, mem_bot] at hfix
  exact sourceRootResidualAction_ne_one c i z h hfix

include h in
/-- The actual residual-fusion consumer has only the alternating-six branch. -/
theorem source_graph_residual_alternating_of_residual_fusion
    (R : Sylow 2 (C c i)) (hR : Tf c i ≤ R)
    (hf : ∀ x : sourceResidualJoinQuotient c i, orderOf x = 2 →
      IsConj (⟨sourceResidualQuotientCenter c i h.embedding_injective,
        sourceResidualJoinQuotient_le_twoResidual c i
          (sourceResidualQuotientCenter_mem c i h.embedding_injective)⟩ :
        pResidual 2 (graphCentralQuotient c i))
      ⟨x.val, sourceResidualJoinQuotient_le_twoResidual c i x.property⟩) :
    Nonempty (pResidual 2 (graphCentralQuotient c i) ≃* alternatingGroup (Fin 6)) :=
  (source_graph_residual_recognition_of_residual_fusion c i z h R hR hf).resolve_left
    (source_graph_residual_not_psl c i z h)

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
