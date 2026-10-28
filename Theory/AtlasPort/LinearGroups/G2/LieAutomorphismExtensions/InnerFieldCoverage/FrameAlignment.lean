module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage.RootFrame
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage.SylowAlignment
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage.FrameAlignment.TorusAlignment
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage.FrameAlignment.RootRecovery
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage.FrameAlignment.WeylCorrection
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage.FrameAlignment.RankOneNormalizers

/-!
# Root-frame alignment for Sylow-preserving G₂ automorphisms

Hall conjugacy in the concrete Borel aligns the split torus while preserving
the Sylow subgroup. The intrinsic Sylow geometry preserves both labelled
parabolics. Their torus-normalizer covers then put the two Weyl images in
the appropriate torus cosets. An explicit common torus correction fixes both
reflections, and a Sylow-intersection calculation recovers all eight roots.

The concrete rank-one normalizer calculations discharge both cover premises
for finite fields of characteristic two with more than two elements. Thus
`root_frame_alignment_of_sylow` gives the simultaneous invariance of all eight
literal root subgroups without additional model assumptions, including over
the field of order four.

Source context: the G₂ automorphism input in Aschbacher--Smith F.1.12,
printed pp.263--264, and invariant parabolics as used in 2.3.9(7), printed
p.526. All groups and maps are the actual split-octonion model.
-/

public section

namespace Atlas.G2.LieAutomorphismExtensions.InnerFieldCoverage
open Subgroup LieParabolicSetup
variable {F : Type*} [Field F]

private theorem weyl_image_form (a : MulAut (Model F))
    (hT : splitTorus.map a.toMonoidHom = splitTorus)
    (P : Subgroup (Model F)) (hP : P.map a.toMonoidHom = P)
    (w : Model F) (hwP : w ∈ P)
    (hwN : w ∈ normalizer (splitTorus (K := F) : Set (Model F)))
    (hwT : w ∉ splitTorus) (hcover : RankOneTorusNormalizerCover P w) :
    ∃ l m : Fˣ, a w = torus l m * w := by
  have hp : a w ∈ P := by
    rw [← hP]
    exact mem_map_of_mem _ hwP
  have hN : (normalizer (splitTorus (K := F) : Set (Model F))).map a.toMonoidHom =
      normalizer (splitTorus (K := F) : Set (Model F)) := by
    rw [map_equiv_normalizer_eq, hT]
  have hn : a w ∈ normalizer (splitTorus (K := F) : Set (Model F)) := by
    rw [← hN]
    exact mem_map_of_mem _ hwN
  rcases hcover (a w) hp hn with h | h
  · rw [← hT] at h
    obtain ⟨v,hv,he⟩ := h
    exact False.elim (hwT (a.injective he ▸ hv))
  · exact h

variable [Finite F] [CharP F 2]

/-- Concrete rank-one normalizer covers suffice for the full eight-root alignment. -/
theorem root_frame_alignment_of_rankOne_torusNormalizers
    (hshort : RankOneTorusNormalizerCover (parabolic₁ (F := F)) weylS)
    (hlong : RankOneTorusNormalizerCover (parabolic₂ (F := F)) weylR)
    (a : MulAut (Model F)) (ha : unipotent.map a.toMonoidHom = unipotent) :
    ∃ g : Model F, PreservesRootGroups (MulAut.conj g * a) := by
  obtain ⟨g, _, hU, hT⟩ := exists_sylow_torus_alignment a ha
  let b : MulAut (Model F) := MulAut.conj g * a
  have hP := parabolics_invariant_of_sylow b hU
  have hrP : (weylR : Model F) ∈ parabolic₂ :=
    mem_sup_right (subset_closure (by simp))
  have hsP : (weylS : Model F) ∈ parabolic₁ :=
    mem_sup_right (subset_closure (by simp))
  have hR := weyl_image_form b hT parabolic₂ hP.2 weylR hrP
    weylR_mem_torusNormalizer weylR_not_mem_torus hlong
  have hS := weyl_image_form b hT parabolic₁ hP.1 weylS hsP
    weylS_mem_torusNormalizer weylS_not_mem_torus hshort
  obtain ⟨t,ht,htR,htS⟩ := exists_torus_weyl_correction b hR hS
  have hu : unipotent.map (MulAut.conj t * b).toMonoidHom = unipotent := by
    change unipotent.map ((MulAut.conj t).toMonoidHom.comp b.toMonoidHom) = _
    rw [← map_map, hU]
    exact mem_normalizer_iff_map_conj_eq.mp (EvenBorelTorus.torus_le_normalizer ht)
  refine ⟨t*g, ?_⟩
  have h := root_frame_of_sylow_weyl (MulAut.conj t * b) hu htR htS
  simpa only [b, map_mul, mul_assoc] using h

/-- Every automorphism preserving the standard Sylow subgroup admits an inner
correction preserving each of the eight concrete root groups, also over F₄. -/
theorem root_frame_alignment_of_sylow (hq : 2 < Nat.card F)
    (a : MulAut (Model F)) (ha : unipotent.map a.toMonoidHom = unipotent) :
    ∃ g : Model F, PreservesRootGroups (MulAut.conj g * a) :=
  root_frame_alignment_of_rankOne_torusNormalizers
    (rankOne_torusNormalizerCover_short hq) (rankOne_torusNormalizerCover_long hq) a ha

end Atlas.G2.LieAutomorphismExtensions.InnerFieldCoverage
