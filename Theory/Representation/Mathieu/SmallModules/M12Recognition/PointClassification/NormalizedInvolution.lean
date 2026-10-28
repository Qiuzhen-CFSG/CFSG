module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Algebra
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.NormIdeal
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate

/-!
# Normalized M₁₁ involution conjugacy

The norm-generated ideal annihilates every faithful degree-ten binary
M₁₁ action. If the cube of the reference annihilator lies in this ideal,
irreducibility forces that annihilator to kill the given action as well.
Surjectivity onto the reference endomorphism algebra then constructs an
equivalence. Literal agreement on the Sylow-eleven normalizer makes this
equivalence a normalizer-module automorphism with the required equation
on the marked involution A.

The finite certificates prove the kernel-cube containment and full
endomorphism image for the actual point representation. `exists_equiv`
discharges both premises of the algebraic reduction, retaining precisely
faithfulness, irreducibility and agreement on the literal normalizer.

Source application: Aschbacher--Smith G.7.3(2), printed p.348 (PDF p.359),
citing James, J. Algebra 27 (1973), 57--111.
-/

public section
open scoped MonoidAlgebra
namespace Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution
open Sporadic.Mathieu

/-- The exact normalized involution conclusion follows from two finite facts about
the reference group-algebra map. The concrete certificates are applied in
`exists_equiv` below. -/
theorem exists_equiv_of_algebra_certificate
    (hfull : Function.Surjective pointRepresentation.asAlgebraHom)
    (hcube : ∀ x ∈ referenceKernel, ∀ y ∈ referenceKernel,
      ∀ z ∈ referenceKernel, x * y * z ∈ elevenIdeal)
    (τ : Representation (ZMod 2) M11 M12Heart)
    (hf : Function.Injective τ) (hirr : τ.IsIrreducible)
    (hon : ∀ g : m11Sylow11Normalizer, τ g.val = pointRepresentation g.val) :
    ∃ e : normalizerRepresentation.Equiv normalizerRepresentation,
      e.toLinearMap.comp (τ m11GeneratorAInM11) =
        (pointRepresentation m11GeneratorAInM11).comp e.toLinearMap := by
  let : τ.IsIrreducible := hirr
  let : pointRepresentation.IsIrreducible := pointRepresentation_isIrreducible
  let : Nontrivial M12Heart := Module.nontrivial_of_finrank_pos
    (by rw [finrank_m12Heart]; decide : 0 < Module.finrank (ZMod 2) M12Heart)
  have hI := elevenIdeal_le_kernel τ hf
  have hK : referenceKernel ≤ TwoSidedIdeal.ker τ.asAlgebraHom :=
    kernel_le_of_cube τ referenceKernel (fun x hx y hy z hz =>
      hI (hcube x hx y hy z hz))
  obtain ⟨f⟩ := equiv_of_kernel_le pointRepresentation τ hfull hK
  let e : normalizerRepresentation.Equiv normalizerRepresentation :=
    .mk f.symm.toLinearEquiv (by
      intro g
      change f.symm.toLinearMap.comp (pointRepresentation g.val) =
        (pointRepresentation g.val).comp f.symm.toLinearMap
      simpa only [hon g] using f.symm.isIntertwining' g.val)
  exact ⟨e, f.symm.isIntertwining' m11GeneratorAInM11⟩

/-- Every faithful irreducible binary M₁₁ action agreeing with the point action
on the literal Sylow-eleven normalizer admits a normalizer-module automorphism
intertwining its marked involution with the reference involution. -/
theorem exists_equiv
    (τ : Representation (ZMod 2) M11 M12Heart)
    (hf : Function.Injective τ) (hirr : τ.IsIrreducible)
    (hon : ∀ g : m11Sylow11Normalizer, τ g.val = pointRepresentation g.val) :
    ∃ e : normalizerRepresentation.Equiv normalizerRepresentation,
      e.toLinearMap.comp (τ m11GeneratorAInM11) =
        (pointRepresentation m11GeneratorAInM11).comp e.toLinearMap :=
  exists_equiv_of_algebra_certificate pointRepresentation_asAlgebraHom_surjective
    referenceKernel_cube_le_elevenIdeal τ hf hirr hon

end Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution
