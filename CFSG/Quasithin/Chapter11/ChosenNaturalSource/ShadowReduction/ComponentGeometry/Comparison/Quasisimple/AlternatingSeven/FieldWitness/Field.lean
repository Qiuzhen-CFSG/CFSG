module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness.Seed
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldAction
public import Theory.SpecificGroups.PSL2.SemilinearCoverage
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.OuterInvolutions
public import Theory.AtlasPort.ExceptionalIsomorphisms.FieldTransportLaws
/-!
# Outer involutions on the marked seed give the literal field equation

Semilinear coverage and the involutory Hilbert--90 calculation put an outer
involution in pure field coordinates. The coordinate change is on the same
seed image: the ambient element and centralizer projection are unchanged.
Source: Aschbacher--Smith, 11.4.2, printed p.777; binary PSL2 automorphisms.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness
private theorem fieldAut_eq_atlas {F : Type*} [Field F] [CharP F 2] (σ : F ≃+* F) :
    Theory.PSL2.fieldAut σ = Atlas.fieldEquivPSL 2 σ := by
  apply MulEquiv.ext
  intro x
  obtain ⟨y,rfl⟩ := Theory.PSL2.quotientMap_surjective F x
  rw [Theory.PSL2.fieldAut_apply_quotientMap]
  exact (Atlas.fieldEquivPSL_mk 2 σ y).symm

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

theorem isFieldElement_of_outer_involution
    (e : seedImage E ≃* PSL(2,E.input.field.Carrier))
    (a : localGroup E) (ha : a ^ 2 = 1)
    (hn : projection E a ∈ normalizer (seedImage E : Set (ActionQuotient E)))
    (ho : ¬ ∃ b : seedImage E,
      (seedImage E).normalizerMonoidHom ⟨projection E a,hn⟩ = MulAut.conj b) :
    IsFieldElement E a := by
  let β := (seedImage E).normalizerMonoidHom ⟨projection E a,hn⟩
  let α := MulAut.congr e β
  have hβ : β ^ 2 = 1 := by
    rw [←map_pow]
    have hsq : (⟨projection E a,hn⟩ : normalizer (seedImage E : Set (ActionQuotient E))) ^ 2 = 1 := by
      apply Subtype.ext
      change projection E a ^ 2 = 1
      simpa only [map_pow,map_one] using congrArg (projection E) ha
    rw [hsq,map_one]
  have hα : α ^ 2 = 1 := by rw [←map_pow,hβ,map_one]
  have houter : α ∉ Theory.PSL2.inner E.input.field.Carrier := by
    intro h
    exact ho ((MulAut.congr_inner_iff e β).mp
      ((Theory.PSL2.mem_inner_iff _ α).mp h))
  obtain ⟨g,σ,hσ⟩ := Theory.PSL2.semilinear_coverage α
  obtain ⟨hs,c,hc⟩ := Theory.PSL2.outer_conjugate_field_of_semilinear α hα g σ hσ houter
  let d := e.trans (MulAut.conj c).symm
  have hne : σ ≠ 1 := by intro h; rw [h,orderOf_one] at hs; contradiction
  refine ⟨d,σ,hne,?_⟩
  intro k
  have hc' : α (e k) = (MulAut.conj c) (Theory.PSL2.fieldAut σ ((MulAut.conj c).symm (e k))) := by
    rw [←hc]
    rfl
  have heq : β k = d.symm (Atlas.fieldEquivPSL 2 σ (d k)) := by
    apply e.injective
    have hαk : α (e k) = e (β k) := by
      change e (β (e.symm (e k))) = e (β k)
      rw [e.symm_apply_apply]
    rw [←hαk,hc',fieldAut_eq_atlas]
    simp only [d,MulEquiv.trans_apply,MulEquiv.symm_trans_apply,MulEquiv.apply_symm_apply,
      MulEquiv.symm_symm]
  exact congrArg Subtype.val heq
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldWitness
