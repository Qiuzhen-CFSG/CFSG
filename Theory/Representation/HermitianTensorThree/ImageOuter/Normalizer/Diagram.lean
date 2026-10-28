module
public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.Diagram

/-!
# Diagram triviality on the binary Hermitian PSL₃(4) module

The faithful projective action is the actual descended SL₃ action, divided by
its cubic scalar kernel. A binary intertwiner normalizes its image. The proved
Hermitian normalizer calculation makes its induced automorphism linear-field,
which preserves the two geometric parabolic types. In the last theorem the
intertwiner is constructed from ambient conjugation on a marked subgroup.

This is the tensor-row obstruction in Aschbacher–Smith 3.2.9(4), printed
pp.582–583, used in 5.1.14 on p.638 (refs/quasithin.pdf). Recognition of a source
module as this tensor is separate from the normalizer calculation. The literal
FSU consumer is Chapter3/Section02/LinearThreeFourGraphTensor.lean.
-/

public noncomputable section
open scoped MatrixGroups
open Subgroup
open Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
open Matrix.PSL3.CartanActions.SixCommutators

namespace Representation.HermitianTensorThree.ImageOuter

/-- The descended binary action of the actual central quotient PSL₃(4). -/
@[expose] def projectiveAction : PSL(3,E 1) →* (Space 1 ≃ₗ[ZMod 2] Space 1) :=
  (binaryImage 1).subtype.comp ((binaryImageEquiv 1).toMonoidHom.comp
    (imageEquivPSL 1 (by decide)).symm.toMonoidHom)

/-- The faithful projective action retains the original SL₃ projection. -/
theorem projectiveAction_mk (g : Cover 1) :
    projectiveAction (QuotientGroup.mk g) = binaryActionHom 1 g := by
  rw [← imageEquivPSL_toImage 1 (by decide) g]
  change ((binaryImageEquiv 1) ((imageEquivPSL 1 (by decide)).symm
    ((imageEquivPSL 1 (by decide)) (toImage 1 g)))).val = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The descended quotient acts faithfully. -/
theorem projectiveAction_injective : Function.Injective projectiveAction :=
  (binaryImage 1).subtype_injective.comp ((binaryImageEquiv 1).injective.comp
    (imageEquivPSL 1 (by decide)).symm.injective)

/-- Its image is exactly the already computed binary Hermitian image. -/
theorem projectiveAction_range : projectiveAction.range = binaryImage 1 := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    exact ((binaryImageEquiv 1) ((imageEquivPSL 1 (by decide)).symm a)).property
  · rintro ⟨g,rfl⟩
    exact ⟨QuotientGroup.mk g,projectiveAction_mk g⟩

/-- Every automorphism implemented on the binary Hermitian module fixes both
geometric parabolic types. No chosen automorphism factorization is assumed. -/
theorem diagram_trivial_of_intertwiner
    (u : Space 1 ≃ₗ[ZMod 2] Space 1) (a : MulAut PSL(3,E 1))
    (h : ∀ x, u * projectiveAction x * u⁻¹ = projectiveAction (a x)) :
    a ∈ diagramTrivial (E 1) := by
  have hu : u ∈ binaryNormalizer 1 := by
    change u ∈ normalizer (binaryImage 1 : Set _)
    rw [← projectiveAction_range, mem_normalizer_iff_map_conj_eq]
    apply le_antisymm
    · rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
      exact ⟨a x,(h x).symm⟩
    · rintro _ ⟨x,rfl⟩
      refine ⟨projectiveAction (a.symm x),⟨_,rfl⟩,?_⟩
      change u * projectiveAction (a.symm x) * u⁻¹ = _
      rw [h,a.apply_symm_apply]
  obtain ⟨g,τ,hg⟩ := inducedActionCoverage_of_scalarCentralizer 1
    (scalarCentralizerCoverage 1) u hu
  have ha : a = projectiveActor (E 1) g τ false := by
    ext x
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (center (Cover 1)) x
    apply projectiveAction_injective
    rw [← h]
    change u * projectiveAction (QuotientGroup.mk y) * u⁻¹ =
      projectiveAction (projectiveActor (E 1) g τ false (QuotientGroup.mk y))
    rw [projectiveAction_mk, hg, semilinearCongruence_conj]
    rw [← centerAction_specialActor, centerAction_mk, projectiveAction_mk]
  rw [ha,diagramTrivial_eq_linearField (E 1) (n := 2) (by decide) (card_E 1)]
  simp only [projectiveActor, Bool.false_eq_true, ↓reduceIte, mul_one]
  exact (linearField (E 1)).mul_mem (mem_sup_left ⟨g,rfl⟩) (mem_sup_right ⟨τ,rfl⟩)

end Representation.HermitianTensorThree.ImageOuter

namespace Representation.HermitianTensorThree.ImageOuter
/-- Transport the normalizer calculation through actual module coordinates.
The implementing operator is constructed from the original ambient conjugation. -/
theorem diagram_trivial_of_conjugation
    {G : Type*} [Group G] (K W : Subgroup G)
    (hKW : K ≤ normalizer (W : Set G))
    (q : K →* PSL(3,E 1)) (hq : Function.Surjective q)
    (c : Additive W ≃+ Space 1)
    (hc : ∀ (k : K) (w : W),
      c (Additive.ofMul (W.normalizerMonoidHom ⟨k,hKW k.property⟩ w)) =
        projectiveAction (q k) (c (Additive.ofMul w)))
    (t : G) (ht : t ∈ normalizer (W : Set G))
    (a : MulAut K) (ha : ∀ k : K, (a k : G) = t * k * t⁻¹)
    (b : MulAut PSL(3,E 1)) (hb : ∀ k, q (a k) = b (q k)) :
    b ∈ diagramTrivial (E 1) := by
  let v := W.normalizerMonoidHom ⟨t,ht⟩
  let d : Space 1 ≃+ Space 1 := c.symm.trans (v.toAdditive.trans c)
  let u : Space 1 ≃ₗ[ZMod 2] Space 1 :=
    LinearEquiv.ofBijective (d.toAddMonoidHom.toZModLinearMap 2) d.bijective
  have hu (w : W) : u (c (Additive.ofMul w)) = c (Additive.ofMul (v w)) := by
    change c (Additive.ofMul (v (c.symm (c (Additive.ofMul w))).toMul)) = _
    rw [c.symm_apply_apply]
    rfl
  apply diagram_trivial_of_intertwiner u b
  intro x
  obtain ⟨k,rfl⟩ := hq x
  apply LinearEquiv.ext
  intro X
  obtain ⟨w,hw⟩ := c.surjective (u.symm X)
  have hX : X = u (c w) := by rw [hw]; exact (u.apply_symm_apply X).symm
  rw [hX]
  change u (projectiveAction (q k) (u.symm (u (c w)))) =
    projectiveAction (b (q k)) (u (c w))
  rw [u.symm_apply_apply,← hb k]
  change u (projectiveAction (q k) (c (Additive.ofMul w.toMul))) =
    projectiveAction (q (a k)) (u (c (Additive.ofMul w.toMul)))
  rw [← hc k w.toMul,hu,hu,← hc (a k) (v w.toMul)]
  apply congrArg c
  apply congrArg Additive.ofMul
  apply Subtype.ext
  change t * ((k : G) * w.toMul * (k : G)⁻¹) * t⁻¹ =
    (a k : G) * (t * w.toMul * t⁻¹) * (a k : G)⁻¹
  rw [ha]
  group
end Representation.HermitianTensorThree.ImageOuter
