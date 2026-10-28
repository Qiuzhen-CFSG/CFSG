module

public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules
import all Theory.Representation.MathieuCodeRestriction.CocodeLocal.PairResidual.Stabilizer

/-!
# The marked pair conjugation equivalence

This is an intentional proof extension of `PairResidual.Stabilizer`: its
conjugation formula is private, so `import all` is used only to prove the
public compatibility equation below. Its implementation is neither copied nor
re-exported. The equivalence comes from faithful conjugation on the pointwise
pair subgroup and the completed abstract M22 automorphism coverage.

Source: Aschbacher--Smith, H.13.1, printed p.395.
-/

public section
noncomputable section
open Sporadic.Mathieu
namespace MathieuCode

/-- The actual degree-24 setwise pair stabilizer, identified by conjugation. -/
def m22PairStabilizerEquivAut : m22PairStabilizer ≃* MulAut M22 :=
  pairResidual_baseStabilizerEquiv

/-- The equivalence intertwines conjugation with the original native embedding. -/
theorem m22PairStabilizerEquivAut_apply (g : m22PairStabilizer) (k : M22) :
    m22Embedding (m22PairStabilizerEquivAut g k) =
      g.val * m22Embedding k * g.val⁻¹ :=
  pairToAut_apply (show pairGroup from g) k

/-- The marked native inclusion becomes the inner-automorphism map. -/
@[simp] theorem m22PairStabilizerEquivAut_inner (g : M22) :
    m22PairStabilizerEquivAut (m22ToPairStabilizer g) = MulAut.conj g := by
  apply MulEquiv.ext
  intro k
  apply m22Embedding_injective
  rw [m22PairStabilizerEquivAut_apply]
  simp [MulAut.conj_apply]

theorem m22PairStabilizer_card : Nat.card m22PairStabilizer = 887040 :=
  pairGroup_card

end MathieuCode
