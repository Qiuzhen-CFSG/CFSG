module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.AmbientGeometry.LiteralCentralizer.SeedWitness.Octad
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.MathieuLocalSections.Placement

/-!
# Literal seed witnesses in intrinsic local L₄(2) sections

A duad in the chosen octad gives a conjugate of `(xy)^14` in the core
center of its preimage residual. Octad transitivity and the surjective
literal quotient map transport this witness to every octad. The proved
common-octad placement and relative-subnormal residual calculation then
identify each source-local section with precisely that residual.

This establishes the intrinsic witness without an ambient J₄ centralizer
bound or normality of the section in max1. The section need not equal the
whole octad preimage.

Source: Aschbacher–Smith A.3.12(17), printed pp.47–48, and the local
configuration in the proof of 1.3.9, p.514; GLS3 Tables 5.3e and 5.3i.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.AmbientGeometry
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry

attribute [local irreducible] Janko4.modelGroup certifiedMathieuSubgroup

private theorem preimage_conjugate (O P : Octad) (g : certifiedMathieuSubgroup)
    (hg : literalMathieuMap g • O.val = P.val) :
    (literalOctadPreimage O).map (MulAut.conj g).toMonoidHom = literalOctadPreimage P := by
  have hP : octadStabilizer P =
      (octadStabilizer O).map (MulAut.conj (literalMathieuMap g)).toMonoidHom := by
    change MulAction.stabilizer M24 P.val =
      (MulAction.stabilizer M24 O.val).map _
    rw [← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  ext x
  rw [mem_map_equiv]
  change literalMathieuMap ((MulAut.conj g).symm x) ∈ octadStabilizer O ↔
    literalMathieuMap x ∈ octadStabilizer P
  rw [hP, mem_map_equiv]
  simp only [MulAut.conj_symm_apply, map_mul, map_inv]

private theorem residual_conjugate (O P : Octad) (g : certifiedMathieuSubgroup)
    (hg : literalMathieuMap g • O.val = P.val) :
    (literalOctadResidual O).map (MulAut.conj g).toMonoidHom = literalOctadResidual P := by
  have hP := preimage_conjugate O P g hg
  have hm := map_solvableResidual_comap (MulAut.conj g).toMonoidHom
    (MulAut.conj g).surjective (literalOctadPreimage P)
  have hc : (literalOctadPreimage P).comap (MulAut.conj g).toMonoidHom =
      literalOctadPreimage O := by
    rw [← hP]
    exact (literalOctadPreimage O).comap_map_eq_self_of_injective (MulAut.conj g).injective
  rw [hc] at hm
  exact hm

/-- Octad transitivity transports the literal seed witness along actual max1 conjugation. -/
theorem octad_coreCenter_seed_witness (O : Octad) :
    ∃ g : certifiedMathieuSubgroup,
      g * literalCentralizerSeed * g⁻¹ ∈ coreCenter (literalOctadResidual O) := by
  obtain ⟨h, hh⟩ := exists_smul_octad_eq LinearFourCore.seedOctad O
  obtain ⟨x, rfl⟩ := literalMathieuMap_surjective h
  obtain ⟨g, hg⟩ := SeedDuads.seed_octad_witness
  have hm := mem_map_of_mem (MulAut.conj x).toMonoidHom hg
  rw [map_coreCenter, residual_conjugate _ _ x hh] at hm
  refine ⟨x * g, ?_⟩
  simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply,
    mul_inv_rev, mul_assoc] using hm

/-- Every intrinsic Sylow-local L₄(2) section in literal max1 has a conjugate
of `(xy)^14` in the center of its two-core. -/
theorem localCoreCenterSeedWitness : LocalCoreCenterSeedWitness := by
  intro B T hB hlocal
  obtain ⟨O, him, hle⟩ := literalImage_eq_octad MathieuLocalSections.octadPlacement
    B T hB hlocal
  rw [literalLocal_eq_residual B T O hlocal him hle]
  exact octad_coreCenter_seed_witness O

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.AmbientGeometry
