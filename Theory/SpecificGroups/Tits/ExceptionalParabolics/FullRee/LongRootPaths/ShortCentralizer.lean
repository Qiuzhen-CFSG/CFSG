module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.LongCentralizer
public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.BinaryDerivedFusion.Reduction

/-!
# Full binary Ree centralizers of the marked short-root elements

The third relative-root element is outside the derived subgroup, belongs to
the Borel, and centralizes the actual short root. Correcting the outer coset
by this element reduces the full centralizer to the existing derived bound.
Conjugation by the specified s₇ then proves the same bound for the literal
commutator of the two marked long-root endpoints. Source: Aschbacher--Smith
F.4.27(4)(ii) and the proof of J.4.7, printed pp.288 and 444.
-/

public section
namespace Tits.ExceptionalParabolics.FullRee.LongRootPaths
open Subgroup ReeF4
open InvolutionRootGeometry InvolutionRootGeometry.BinaryDerivedFusion

private theorem short_eq_embedding :
    (shortRoot : Model 0) = atlasEmbedding (atlas1600ParrottAssignment .s4) := by
  rw [atlasEmbedding_generator]
  exact embedding_generator .s4

private theorem outer_mem_borel : fixedU 2 ∈ S := by
  have hm : fixedU 0 * fixedU 2 = atlasEmbedding (atlas1600ParrottAssignment .s3) := by
    apply toSplitGroup_injective 0
    rw [map_mul, fixedU_matrix, fixedU_matrix, atlasEmbedding_generator_matrix]
    rfl
  have hh : atlasEmbedding (atlas1600ParrottAssignment .s3) ∈ S := by
    apply atlas_sylow_map_le
    apply mem_map_of_mem
    rw [ExceptionalParabolics.S, atlas1600SylowTwoSubgroup_eq]
    exact Subgroup.subset_closure (by simp)
  rw [← hm] at hh
  exact (mul_mem_cancel_left fixedU_zero_mem_unipotent).mp hh

private theorem outer_commutes_short : Commute (fixedU 2) (shortRoot : Model 0) := by
  apply toSplitGroup_injective 0
  simp only [map_mul, fixedU_matrix, shortRoot_matrix,
    DerivedTits.Realization.u, Matrix.cons_val_two]
  exact DerivedTits.Realization.quartet_three_commutes_pair_three.eq

private theorem derived_short_bound {x : Model 0}
    (hx : x ∈ commutator (Model 0)) (hc : x ∈ centralizer {(shortRoot : Model 0)}) :
    x ∈ second := by
  rw [← atlasEmbedding_range] at hx
  obtain ⟨y, rfl⟩ := hx
  apply atlas_second_map_le
  apply mem_map_of_mem
  apply ParabolicContainment.short_centralizer_le_second
  rw [mem_centralizer_singleton_iff]
  apply atlasEmbedding_injective
  simpa only [map_mul, short_eq_embedding] using mem_centralizer_singleton_iff.mp hc

/-- The short-root centralizer in the full Ree carrier lies in the actual
linear parabolic, without a derived-group restriction. -/
theorem short_centralizer_le_second :
    centralizer {(shortRoot : Model 0)} ≤ second := by
  intro x hx
  by_cases hd : x ∈ commutator (Model 0)
  · exact derived_short_bound hd hx
  · have hi : (fixedU 2)⁻¹ ∉ commutator (Model 0) := by
      simpa only [inv_mem_iff] using fixedU_two_not_mem
    have hh : (fixedU 2)⁻¹ * x ∈ commutator (Model 0) :=
      ((commutator (Model 0)).mul_mem_iff_of_index_two derived_index).mpr (iff_of_false hi hd)
    have hc : fixedU 2 ∈ centralizer {(shortRoot : Model 0)} :=
      mem_centralizer_singleton_iff.mpr outer_commutes_short.eq
    have hm := derived_short_bound hh
      ((centralizer {(shortRoot : Model 0)}).mul_mem
        ((centralizer {(shortRoot : Model 0)}).inv_mem hc) hx)
    simpa only [mul_inv_cancel_left] using second.mul_mem (sylow_le_second outer_mem_borel) hm

/-- The actual six-step commutator has its full centralizer in the same
linear parabolic. The short-root conjugator s₇ belongs to that parabolic. -/
theorem commutator_centralizer_le_second : centralizer {shortCommutator} ≤ second := by
  have hs : atlasEmbedding (atlas1600ParrottAssignment .s7) ∈ second := by
    apply sylow_le_second
    apply atlas_sylow_map_le
    apply mem_map_of_mem
    rw [ExceptionalParabolics.S, atlas1600SylowTwoSubgroup_eq]
    exact Subgroup.subset_closure (by simp)
  intro x hx
  let s := atlasEmbedding (atlas1600ParrottAssignment .s7)
  have hc : s⁻¹ * x * s ∈ centralizer {(shortRoot : Model 0)} := by
    rw [mem_centralizer_singleton_iff]
    have h := mem_centralizer_singleton_iff.mp hx
    change x * (s * atlasEmbedding (atlas1600ParrottAssignment .s4) * s⁻¹) =
      (s * atlasEmbedding (atlas1600ParrottAssignment .s4) * s⁻¹) * x at h
    have hh := congrArg (fun a => s⁻¹ * a * s) h
    rw [short_eq_embedding]
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left,
      inv_mul_cancel_right, mul_inv_cancel_right, inv_mul_cancel, mul_inv_cancel, mul_one] using hh
  have hm := short_centralizer_le_second hc
  have hh := second.mul_mem (second.mul_mem hs hm) (second.inv_mem hs)
  simpa only [s, mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right, mul_inv_cancel, mul_one] using hh

end Tits.ExceptionalParabolics.FullRee.LongRootPaths
