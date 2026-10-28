module

public import Theory.Representation.ExtraspecialCubicTrace
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.PolynomialSelection.Complement
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.PolynomialSelection.KernelAction
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Fixed central cosets from the whole-Leech polynomial

The faithful rational action on the sixteen complementary coordinates sends
the nonidentity central element of the extraspecial octad kernel to minus
identity. Its 256 central cosets therefore give a trace-orthogonal basis of
the endomorphism space. The literal kernel conjugation and quotient action
are compatible with this basis. Since the actor is cubic, the endomorphism
trace is the number of fixed central cosets.

The whole-Leech polynomial gives trace 64 by `Complement`; applying the
projective-basis count yields exactly 64 fixed cosets. Extraspeciality and
kernel order 512 remain the two stated kernel hypotheses. Quaternion
recognition and its source-theorem assembly belong to the parent module.

Source: Aschbacher, *Sporadic Groups* (1994), 25.1–25.5, 25.9, Chapter 9
Exercise 6, p.141, §46, p.251, and 49.3(2). Exercise 9.6 itself asserts only
the forward fixed-free implication; the trace-to-count argument is proved
here from the actual representation rather than inferred from that exercise.
-/

public section

namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction.PolynomialSelection

/-- The whole-Leech polynomial forces exactly 64 fixed cosets of the kernel center. -/
theorem kernelQuotientFixed_card_of_polynomial (hQ : IsExtraspecial 2 action.ker)
    (hcard : Nat.card action.ker = 512) {r : centralizer} (ho : orderOf r = 3)
    (hr : ∀ x : Atlas.Lattices.leech, r.val.val (r.val.val x) + r.val.val x + x = 0) :
    Nat.card (kernelQuotientFixed r) = 64 := by
  let := hQ
  let : IsMulCommutative KernelQuotient :=
    (IsExtraspecial.quotient_elementary_abelian 2 action.ker).toIsMulCommutative
  have hcomm : commutator action.ker ≤ Subgroup.center action.ker :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le
      (N := Subgroup.center action.ker)).mp inferInstance
  have hdim : Module.finrank ℚ (Module.End ℚ ComplementSpace) = 256 := by
    rw [Module.finrank_linearMap, complementSpace_finrank]
  have ht := Representation.ExtraspecialCubicTrace.trace_eq_card_fixed
    kernelRepresentation hcomm (kernelRepresentation_center hQ)
    (by rw [complementSpace_finrank]; norm_num)
    ((kernelQuotient_card hQ hcard).trans hdim.symm)
    (kernelConjugation r) (kernelQuotientAction r)
    (kernelQuotientAction_mk r) (kernelConjugation_cube ho)
    (complementAction r).conj.toLinearMap
    (fun q => (kernelRepresentation_conjugation r q).symm)
  rw [complementAction_conjugation_trace ho hr] at ht
  change (64 : ℚ) = (Nat.card (kernelQuotientFixed r) : ℚ) at ht
  exact_mod_cast ht.symm

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction.PolynomialSelection
