module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.NaturalParabolic.Alignment

/-!
# The actual residual actor in aligned natural coordinates

Restrict the starred map to the original embedded two-residual and then the
aligned model. Its image is the entire upper Borel and its kernel is exactly
S intersect L1. The invariant line and its quotient retain irreducibility and
noncentrality by surjective pullback of the checked Borel model facts.

Source: Aschbacher--Smith 13.5.22(2), p.924/PDF p.941, using G.2.4.
-/

@[expose] public section
open Subgroup NoncentralChiefRefinement Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.NaturalParabolic
open ChapterG.Section02 ChapterG.Section02.Setup
open ChapterG.Section02.AlternatingFive
open ChapterG.Section02.AlternatingFive.Recognition.ProjectiveGeometry
open Representation.SL2FourNatural.BorelFactors
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}
variable (d : Hypothesis D g) (e : D.star D.L ≃* SL(2,F4))
  (he : ((D.star D.L₁).subgroupOf (D.star D.L)).map e.toMonoidHom = B0)

noncomputable def actor : D.L₁ →* B0 :=
  (e.toMonoidHom.comp ((starProjection D).comp (inclusion (residual_le_L D)))).codRestrict _
    (fun k => he ▸ mem_map.mpr ⟨starProjection D (inclusion (residual_le_L D) k),
      mem_map.mpr ⟨⟨k, ((residual_le_L D).trans le_sup_left) k.property⟩, k.property, rfl⟩, rfl⟩)

omit [Finite G] in
theorem actor_surjective : Function.Surjective (actor e he) := by
  intro b
  have hb : b.val ∈ ((D.star D.L₁).subgroupOf (D.star D.L)).map e.toMonoidHom :=
    he.symm ▸ b.property
  obtain ⟨z, hz, hzb⟩ := hb
  obtain ⟨l, hl, hlz⟩ := hz
  let k : D.L₁ := ⟨l, hl⟩
  have hk : starProjection D (inclusion (residual_le_L D) k) = z := Subtype.ext hlz
  refine ⟨k, ?_⟩
  apply Subtype.ext
  change e (starProjection D (inclusion (residual_le_L D) k)) = b.val
  exact (congrArg e hk).trans hzb

theorem actor_kernel : (actor e he).ker = (core d).val := by
  rw [← localProjection_kernel d]
  ext k
  change actor e he k = 1 ↔ localProjection d k = 1
  rw [Subtype.ext_iff, Subtype.ext_iff]
  change e (starProjection D (inclusion (residual_le_L D) k)) = 1 ↔
    d.model (starProjection D (inclusion (residual_le_L D) k)) = 1
  rw [e.map_eq_one_iff, d.model.map_eq_one_iff]

noncomputable def naturalRepresentation : Representation (ZMod 2) D.L₁ Representation.SL2FourNatural.V :=
  natural.comp (actor e he)

noncomputable def naturalLine : Subrepresentation (naturalRepresentation e he) where
  toSubmodule := line.toSubmodule
  apply_mem_toSubmodule k _ hv := line.apply_mem_toSubmodule (actor e he k) hv

omit [Finite G] in
theorem naturalLine_irreducible : Representation.IsIrreducible (naturalLine e he).toRepresentation := by
  change Representation.IsIrreducible (line.toRepresentation.comp (actor e he))
  exact (Representation.irreducible_comp_surjective_iff _ (actor_surjective e he) _).mpr inferInstance

omit [Finite G] in
theorem naturalQuotient_irreducible : Representation.IsIrreducible (naturalLine e he).quotientRepresentation := by
  change Representation.IsIrreducible (line.quotientRepresentation.comp (actor e he))
  exact (Representation.irreducible_comp_surjective_iff _ (actor_surjective e he) _).mpr inferInstance

omit [Finite G] in
theorem natural_factors_noncentral :
    (∃ k v, (naturalLine e he).toRepresentation k v ≠ v) ∧
    (∃ k v, (naturalLine e he).quotientRepresentation k v ≠ v) := by
  constructor
  · obtain ⟨b, v, hv⟩ := line_noncentral
    obtain ⟨k, rfl⟩ := actor_surjective e he b
    exact ⟨k, v, hv⟩
  · obtain ⟨b, v, hv⟩ := quotient_noncentral
    obtain ⟨k, rfl⟩ := actor_surjective e he b
    exact ⟨k, v, hv⟩

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.NaturalParabolic
