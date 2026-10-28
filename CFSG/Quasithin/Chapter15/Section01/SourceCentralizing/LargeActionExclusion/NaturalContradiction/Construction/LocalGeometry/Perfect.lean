module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Construction.LocalGeometry
public import Theory.SpecificGroups.BinaryLinear.OrderedResidualConjugators.FirstTwoPerfect
public import Theory.GroupTheory.PResidual.PerfectLift

/-!
# Perfection of the original rank-two residual join

Under the literal natural action the image of K = ⟨Y₀,Y₂⟩ is the join
of the first two binary node residuals. The matrix calculation proves
that image perfect. K is two-perfect because both generating residuals
are two-perfect, and its action kernel is a two-group. Perfection then
lifts through that kernel, with the actual ambient embedding retained.

Source: Aschbacher--Smith 15.1.29, printed pp.1103--1104.
-/

public section
open Subgroup Theory.GroupTheory
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
open BinaryLinear.OrderedResidualConjugators
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.NaturalFlag
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
variable {d : CaseIComponentData T M Mc V} {t : G}

/-- Perfection of the actual join lifts through its two-group action kernel. -/
theorem pair_perfect (a : NaturalFlag d t) : Group.IsPerfect a.parabolics.K := by
  let K := a.parabolics.K
  have h0 : a.parabolics.Y0 ≤ d.L ⊔ d.S := (map_subtype_le _).trans a.parabolics_le.1
  have h2 : a.parabolics.Y2 ≤ d.L ⊔ d.S := (map_subtype_le _).trans a.parabolics_le.2.1
  have hK : K ≤ d.L ⊔ d.S := sup_le h0 h2
  let f := a.action.comp (inclusion hK)
  have hf : f.range = nodeResidual a.basis ⟨0,by have := a.dimension; omega⟩ ⊔
      nodeResidual a.basis ⟨1,by have := a.dimension; omega⟩ := by
    have he : f.range = (K.subgroupOf (d.L ⊔ d.S)).map a.action := by
      ext g
      constructor
      · rintro ⟨k,rfl⟩
        exact mem_map_of_mem a.action k.property
      · rintro ⟨k,hk,rfl⟩
        exact ⟨⟨k,hk⟩,rfl⟩
    rw [he,show K = a.parabolics.Y0 ⊔ a.parabolics.Y2 from rfl,
      subgroupOf_sup h0 h2,Subgroup.map_sup]
    exact congrArg₂ (· ⊔ ·) (a.node_residual_image _) (a.node_residual_image _)
  have hp : IsPPerfect 2 K := by
    have hle (Y : Subgroup G) (hY : IsPPerfect 2 Y) (hYK : Y ≤ K) :
        Y ≤ (pResidual 2 K).map K.subtype := by
      have hh := embedded_pResidual_mono 2 hYK
      rw [(pResidual_eq_top_iff 2 Y).mpr hY,←MonoidHom.range_eq_map,range_subtype] at hh
      exact hh
    have he : (pResidual 2 K).map K.subtype = K := le_antisymm (map_subtype_le _)
      (sup_le (hle _ (isPPerfect_embedded_pResidual 2 _) le_sup_left)
        (hle _ (isPPerfect_embedded_pResidual 2 _) le_sup_right))
    apply (pResidual_eq_top_iff 2 K).mp
    apply map_injective K.subtype_injective
    simpa only [←MonoidHom.range_eq_map,range_subtype] using he
  let : Group.IsPerfect f.range := hf ▸ first_two_residuals_perfect
    (by have := a.dimension; omega) a.basis
  have hk : IsPGroup 2 a.action.ker := by
    rw [show a.action.ker = pCore 2 (d.L ⊔ d.S : Subgroup G) from a.kernel]
    exact pCore_isPGroup
  apply hp.isPerfect_of_surjective_pGroup_kernel f.rangeRestrict f.rangeRestrict_surjective
  rw [MonoidHom.ker_rangeRestrict]
  exact hk.comap_of_injective (inclusion hK) (inclusion_injective hK)
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.NaturalFlag
