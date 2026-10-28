module

public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.ElementaryPlanes

/-!
# Normality of the two transported elementary planes

Conjugation does not change either root coordinate of UT₃(F₄). Thus its two
root planes, and their literal preimages under every group equivalence, are
normal. Together with the two source reflection actions, this supplies their
normality in the generated source normalizer in Aschbacher 45.3.
-/

public section
noncomputable section
open Subgroup Matrix.PSL3Four
namespace Theory.GroupTheory.HyperbolicRecognition
variable {K : Type*} [Group K]

instance (e : K ≃* RootNormalizerModel.Root) : (transportedPlane₁ e).Normal where
  conj_mem x hx g := by
    apply (mem_transportedPlane₁ e _).mpr
    rw [map_mul,map_mul,map_inv]
    change ((e g).y + (e x).y) + -(e g).y = 0
    rw [(mem_transportedPlane₁ e x).mp hx,add_zero,add_neg_cancel]

instance (e : K ≃* RootNormalizerModel.Root) : (transportedPlane₂ e).Normal where
  conj_mem x hx g := by
    apply (mem_transportedPlane₂ e _).mpr
    rw [map_mul,map_mul,map_inv]
    change ((e g).x + (e x).x) + -(e g).x = 0
    rw [(mem_transportedPlane₂ e x).mp hx,add_zero,add_neg_cancel]

end Theory.GroupTheory.HyperbolicRecognition
