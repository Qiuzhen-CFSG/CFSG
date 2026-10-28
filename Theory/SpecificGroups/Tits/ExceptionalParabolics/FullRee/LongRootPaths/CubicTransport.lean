module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.CubicCertificate
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.SecondCore

/-!
# The actual cubic in the short-root centralizer

The checked word is lifted to the actual full second parabolic. It has
order three, centralizes the specified short commutator, and conjugates
the left endpoint to the right endpoint. All marks are the original words.
Source: the local calculation in J.4.7, printed p.444.
-/

@[expose] public section
noncomputable section
namespace Tits.ExceptionalParabolics.FullRee.LongRootPaths
open Subgroup

/-- The literal cubic transporter, with its fixed ambient embedding. -/
def cubicTransporter : ReeF4.Model 0 := atlasEmbedding Atlas.cubicWord

theorem cubicTransporter_cube : cubicTransporter^3=1 := by
  simpa only [cubicTransporter,map_pow,map_one] using congrArg atlasEmbedding Atlas.cubic_word_cube

theorem cubicTransporter_conj_left : cubicTransporter*leftSix*cubicTransporter⁻¹=u := by
  have hh := congrArg atlasEmbedding Atlas.cubic_word_left
  have he : cubicTransporter*leftSix=u*cubicTransporter := by
    simpa only [cubicTransporter,leftSix,u,map_mul] using hh
  rw [he,mul_inv_cancel_right]

theorem cubicTransporter_order : orderOf cubicTransporter=3 := by
  apply orderOf_eq_prime cubicTransporter_cube
  intro h
  have he := cubicTransporter_conj_left
  rw [h,one_mul,inv_one,mul_one] at he
  have hu : u^2=1 := by
    have hh : (Atlas.a .s1)^2=1 := by
      simpa only [Atlas.a,parrottRelator,map_pow,FreeGroup.lift_apply_of] using
        atlas1600ParrottAssignment_relations .i_s1
    simpa only [u,map_pow,map_one] using congrArg atlasEmbedding hh
  have ho := leftSix_mul_u_order
  rw [he,←pow_two,hu,orderOf_one] at ho
  norm_num at ho

theorem cubicTransporter_centralizes : Commute cubicTransporter shortCommutator := by
  show cubicTransporter*shortCommutator=shortCommutator*cubicTransporter
  simpa only [cubicTransporter,shortCommutator,map_mul,map_inv] using
    congrArg atlasEmbedding Atlas.cubic_word_short

theorem cubicTransporter_mem_second : cubicTransporter∈second := by
  apply atlas_second_map_le
  apply mem_map_of_mem
  have hs (i:ParrottGenerator) (h1:i≠.r1) (h8:i≠.r8) : Atlas.a i∈ExceptionalParabolics.second := by
    apply ExceptionalParabolics.sylow_le_second
    rw [ExceptionalParabolics.S,atlas1600SylowTwoSubgroup_eq]
    apply Subgroup.subset_closure
    cases i <;> simp_all [Atlas.a]
  exact ExceptionalParabolics.second.mul_mem
    (ExceptionalParabolics.second.mul_mem (hs .s5 (by decide) (by decide))
      ExceptionalParabolics.reflection_mem_second)
    (hs .s8 (by decide) (by decide))

end Tits.ExceptionalParabolics.FullRee.LongRootPaths
