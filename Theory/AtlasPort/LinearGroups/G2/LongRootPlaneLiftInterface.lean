module

public import Theory.AtlasPort.LinearGroups.G2.LongRootPlaneLift
import all Theory.AtlasPort.LinearGroups.G2.LongRootPlaneLift

/-!
# Public specification of the long-root lifting input

`CentralInvolutionLifting` has a public name but a hidden definition body.
This internal interface extension deliberately imports that body to publish
its specification, allowing production proofs to construct the lifting input
without modifying the existing module or its downstream imports.
-/

public section
namespace Atlas.G2.LongRootPlaneLift
open Subgroup Theory.GroupTheory

theorem centralInvolutionLifting_iff (K : Type*) [Group K] :
    CentralInvolutionLifting K ↔
      ∀ x : K ⧸ center K, IsSylowCentralInvolution x →
        ∃ y : K, QuotientGroup.mk' (center K) y = x ∧ orderOf y = 2 := Iff.rfl

end Atlas.G2.LongRootPlaneLift
