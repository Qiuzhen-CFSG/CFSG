module
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.OrbitStabilizers
public import Theory.SpecificGroups.PSL3.UniversalProjection.Basic
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
-- Internal continuation of the compatible native inner/outer identifications.
import all Theory.Representation.MathieuCodeRestriction.M22.SourceModules.OrbitStabilizers

/-!
# The full M22 cocode point model

The linear PSL₃(4) subgroup of the field extension has trivial centralizer:
its doubly transitive projective action on 21 points forces every commuting
permutation to be trivial. Consequently the full point model has trivial
two-core, and its perfect residual is precisely the linear subgroup.

Source: Aschbacher--Smith H.15.1 and 8.1.1, pp.398,712.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace MathieuCode.NormalizedShadowRows
open Matrix.PSL3Four

/-- The full outer point model has no element centralizing its linear subgroup. -/
theorem fieldExtension_centralizer_linear :
    centralizer (linearInclusion.range : Set FieldExtension) = ⊥ := by
  classical
  apply le_bot_iff.mp
  intro u hu
  apply pointAction_injective
  rw [map_one]
  ext x
  change pointAction u x = x
  by_contra hne
  let : Fintype PG := Fintype.ofFinite PG
  have hc : Fintype.card PG = 21 := by
    rw [←Nat.card_eq_fintype_card,Projectivization.card'']
    norm_num [Nat.card_fun,card_F]
  obtain ⟨y,hyx,hyu⟩ : ∃ y : PG, y ≠ x ∧ y ≠ pointAction u x := by
    by_contra! h
    have hs : (Finset.univ : Finset PG) ⊆ {x,pointAction u x} := by
      intro y _
      simp only [Finset.mem_insert,Finset.mem_singleton]
      exact or_iff_not_imp_left.mpr (h y)
    have hh := Finset.card_le_card hs
    have ht : ({x,pointAction u x} : Finset PG).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ,hc] at hh
    omega
  obtain ⟨a,hax,hay⟩ := (MulAction.is_two_pretransitive_iff.mp
    (inferInstance : MulAction.IsMultiplyPretransitive SL PG 2))
      (show x ≠ pointAction u x from Ne.symm hne) (show x ≠ y from hyx.symm)
  have he := congrArg pointAction
    (mem_centralizer_iff.mp hu (linearInclusion (a : PSL)) ⟨(a : PSL),rfl⟩)
  have hev := Equiv.congr_fun he x
  simp only [map_mul,Equiv.Perm.mul_apply] at hev
  have ha (p : PG) : pointAction (linearInclusion (a : PSL)) p = a • p := by
    simp only [pointAction,MonoidHom.comp_apply,pairedAction_linearInclusion,
      pslCollineation_point,Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk]
  rw [ha,ha,hax,hay] at hev
  exact hyu hev

/-- The native point residual retains the actual linear inclusion. -/
theorem fieldExtension_residual : solvableResidual FieldExtension = linearInclusion.range := by
  have hle : solvableResidual FieldExtension ≤ fieldProjection.ker := by
    have hh := map_solvableResidual_le fieldProjection
    rw [solvableResidual_eq_bot (G := C2),map_le_iff_le_comap] at hh
    exact hh
  apply le_antisymm (range_linearInclusion.symm ▸ hle)
  let : Group.IsPerfect linearInclusion.range := Group.IsPerfect.ofSurjective
    linearInclusion.rangeRestrict_surjective
  exact le_solvableResidual_of_isPerfect _

/-- The full point model has trivial two-core; it is not replaced by PSL₃(4). -/
theorem fieldExtension_twoCore : pCore 2 FieldExtension = ⊥ := by
  have hPSL : pCore 2 PSL = ⊥ := by
    have hz : center PSL = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot
      (Matrix.SpecialLinearGroup (Fin 3) F)
    exact le_bot_iff.mp ((IsQuasisimple.pCore_le_center 2).trans_eq hz)
  have hpre : (pCore 2 FieldExtension).comap linearInclusion ≤ pCore 2 PSL :=
    le_sSup ⟨inferInstance,pCore_isPGroup.comap_of_injective _ linearInclusion_injective⟩
  have hdis : Disjoint (pCore 2 FieldExtension) linearInclusion.range := by
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    rintro y ⟨hy,⟨x,rfl⟩⟩
    have hx : x = 1 := mem_bot.mp (hPSL ▸ hpre hy)
    simpa only [hx,map_one] using (one_mem (⊥ : Subgroup FieldExtension))
  let : linearInclusion.range.Normal := range_linearInclusion.symm ▸ inferInstance
  have hcomm := commutator_eq_bot_of_disjoint hdis
  exact le_bot_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp hcomm).trans_eq
    fieldExtension_centralizer_linear)

/-- The entire native residual has trivial centralizer in the full model. -/
theorem fieldExtension_centralizer_residual :
    centralizer (solvableResidual FieldExtension : Set FieldExtension) = ⊥ := by
  rw [fieldExtension_residual]
  exact fieldExtension_centralizer_linear

/-- Every action image containing the linear subgroup kills the original
source two-core, even when its image is only the inner point stabilizer. -/
theorem fieldExtension_twoCore_image {C : Type*} [Group C]
    (f : C →* FieldExtension) (hlinear : linearInclusion.range ≤ f.range) :
    pCore 2 C ≤ f.ker := by
  let H := f.range
  have hH : H.Normal := by
    have he : (H.map fieldProjection).comap fieldProjection = H :=
      comap_map_eq_self (range_linearInclusion ▸ hlinear)
    rw [←he]
    infer_instance
  let := hH
  have hpH : H.pCoreIn 2 ≤ pCore 2 FieldExtension :=
    le_sSup ⟨inferInstanceAs (((pCore 2 H).map H.subtype).Normal),isPGroup_pCoreIn 2 H⟩
  have hp : pCore 2 H = ⊥ := by
    apply (pCore 2 H).eq_bot_iff_forall.mpr
    intro c hc
    apply Subtype.ext
    exact mem_bot.mp (fieldExtension_twoCore ▸ hpH (mem_map_of_mem H.subtype hc))
  have hm : (pCore 2 C).map f.rangeRestrict ≤ pCore 2 H :=
    le_sSup ⟨(inferInstance : (pCore 2 C).Normal).map _ f.rangeRestrict_surjective,
      pCore_isPGroup.map _⟩
  intro c hc
  have hy : f.rangeRestrict c = 1 :=
    mem_bot.mp (hp ▸ hm (mem_map_of_mem f.rangeRestrict hc))
  exact congrArg Subtype.val hy

/-- The inner and full vector-stabilizer markings use the same linear inclusion. -/
theorem m22_point_marking_compatible (i : Fin 22)
    (g : m22CocodeStabilizer m22CocodeRepresentation (m22WeightTwoVector i))
    (t : m22CocodeStabilizer m22OuterCocodeRepresentation (m22WeightTwoVector i))
    (h : t.val = m22ToPairStabilizer g.val) :
    m22WeightTwoVector_outer_stabilizer_equiv i t =
      linearInclusion (m22WeightTwoVector_stabilizer_equiv i g) := by
  let g' : MulAction.stabilizer Sporadic.Mathieu.M22 i :=
    MulEquiv.subgroupCongr (m22WeightTwoVector_stabilizer i) g
  let t' : m22OuterPointStabilizer i :=
    MulEquiv.subgroupCongr (m22WeightTwoVector_outer_stabilizer i) t
  have ht : t' = m22PointToOuterPoint i g' := Subtype.ext h
  change m22OuterPointStabilizerEquiv i t' = linearInclusion (m22PointStabilizerEquiv i g')
  rw [ht]
  exact m22PointStabilizerEquiv_compatible i g'

end MathieuCode.NormalizedShadowRows
