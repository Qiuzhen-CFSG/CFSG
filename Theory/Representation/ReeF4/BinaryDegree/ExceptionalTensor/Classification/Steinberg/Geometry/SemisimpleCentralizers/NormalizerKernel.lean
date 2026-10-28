module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers.TorusCoordinates
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.TorusConjugacy

/-!
# Kernel of the actual F4 torus normalizer action

Trivial action on the full integral character lattice fixes every torus point.
The proved concrete self-centralizing property of the split F4 torus then
identifies the kernel with torus points. This is the kernel step in the source
connected-centralizer argument (Steinberg, §3.9).
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers
open RootModel.Corrected
open BorelIntersectionGeometry.RankOneGeometry.NormalizerActionExistence
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]
attribute [local instance] torusGroup

/-- Trivial actual Weyl action forces a normalizer element into the literal torus. -/
theorem mem_torus_of_normalizerWeyl_eq_one
    (n : (F4Chevalley.splitTorus (k := F)).normalizer.toSubgroup)
    (hn : normalizerWeyl n = 1) : n.val ∈ F4Chevalley.splitTorus := by
  have hp (t : Variety.Point (F4Chevalley.splitTorus (k := F)).carrierVariety) :
      (torusConjugation n⁻¹).onPoints t = t := by
    apply rawEvaluation_injective
    apply AddMonoidHom.ext
    intro a
    have h := rawEvaluation_normalizer n t a
    rw [hn, map_one] at h
    exact h.symm
  change n.val ∈ (F4Chevalley.splitTorus (k := F)).toSubgroup
  rw [← F4Chevalley.TorusConjugacy.splitTorus_centralizer_eq]
  apply Subgroup.mem_centralizer_iff.mpr
  intro t ht
  let s := (F4Chevalley.splitTorus (k := F)).pointEquiv.symm ⟨t, ht⟩
  have hs : (F4Chevalley.splitTorus (k := F)).includePoint s = t :=
    congrArg Subtype.val ((F4Chevalley.splitTorus (k := F)).pointEquiv.apply_symm_apply _)
  have h := congrArg (F4Chevalley.splitTorus (k := F)).includePoint (hp s)
  rw [torusConjugation_include, hs, Subgroup.coe_inv, inv_inv] at h
  have h' := congrArg (fun z => n.val * z) h
  simpa only [mul_inv_cancel_left, mul_assoc, mul_inv_cancel, mul_one] using h'
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SemisimpleCentralizers
