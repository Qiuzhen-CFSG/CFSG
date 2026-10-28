module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.CoreGeneration
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.SupplementCertificate

/-!
# The short-root centralizer supplements the actual second core

The corrected two Levi generators lie in the short-root centralizer. Together
with the radical they contain the entire derived second parabolic; the outer
root q is itself in the radical and supplies its missing index-two coset.
Thus the exact short commutator centralizer supplements the original core.
Source: the model calculation used in J.4.7, printed p.444.
-/

public section
noncomputable section
namespace Tits.ExceptionalParabolics.FullRee.LongRootPaths
open Subgroup ReeF4 RootRelations
open InvolutionRootGeometry.BinaryDerivedFusion

/-- The ambient short-root centralizer together with the intrinsic core
is precisely the actual full second parabolic. -/
theorem secondCore_sup_shortCentralizer :
    secondCore ⊔ centralizer ({shortCommutator}:Set (Model 0))=second := by
  let K : Subgroup (Model 0) := secondCore ⊔ centralizer ({shortCommutator}:Set (Model 0))
  have hcore : secondCore≤K := le_sup_left
  have hc : centralizer ({shortCommutator}:Set (Model 0))≤K := le_sup_right
  have h8 : atlasEmbedding (Atlas.a .s8)∈K := by
    let b := atlasEmbedding (Atlas.a .s3)*atlasEmbedding (Atlas.a .s7)
    have hb : b∈K := hcore (secondCore.mul_mem
      (generator_mem_secondCore .s3 (by decide) (by decide) (by decide))
      (generator_mem_secondCore .s7 (by decide) (by decide) (by decide)))
    have hb8 : b*atlasEmbedding (Atlas.a .s8)∈K := by
      apply hc
      apply mem_centralizer_singleton_iff.mpr
      simpa only [b,shortCommutator,map_mul,map_inv] using
        congrArg atlasEmbedding Atlas.short_corrected_commutes.eq
    simpa only [inv_mul_cancel_left] using K.mul_mem (K.inv_mem hb) hb8
  have hr : atlasEmbedding (Atlas.a .r8)∈K := by
    apply hc
    apply mem_centralizer_singleton_iff.mpr
    simpa only [shortCommutator,map_mul,map_inv] using
      congrArg atlasEmbedding Atlas.short_reflection_commutes.eq
  have ha : ExceptionalParabolics.second.map atlasEmbedding≤K := by
    rw [ExceptionalParabolics.second,Subgroup.map_sup]
    apply sup_le
    · rw [map_le_iff_le_comap,ExceptionalParabolics.S,atlas1600SylowTwoSubgroup_eq]
      apply (closure_le _).mpr
      intro a ha
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact h8
      all_goals exact hcore (generator_mem_secondCore _ (by decide) (by decide) (by decide))
    · rw [map_le_iff_le_comap]
      apply (closure_le _).mpr
      rintro a (rfl : a=atlas1600ParrottAssignment .r8)
      exact hr
  apply le_antisymm
  · exact sup_le (map_subtype_le _) commutator_centralizer_le_second
  · intro x hx
    by_cases hd : x∈commutator (Model 0)
    · exact ha (atlas_second_map ▸ ⟨hx,hd⟩)
    · have hq : q∈second := map_subtype_le _ q_mem_secondCore
      have hD : q⁻¹*x∈commutator (Model 0) :=
        ((commutator (Model 0)).mul_mem_iff_of_index_two derived_index).mpr
          (iff_of_false (by simpa only [q,inv_mem_iff] using fixedU_zero_not_mem) hd)
      have hm : q⁻¹*x∈ExceptionalParabolics.second.map atlasEmbedding := by
        rw [atlas_second_map]
        exact ⟨second.mul_mem (second.inv_mem hq) hx,hD⟩
      have hh := ha hm
      simpa only [mul_inv_cancel_left] using K.mul_mem (hcore q_mem_secondCore) hh

end Tits.ExceptionalParabolics.FullRee.LongRootPaths
