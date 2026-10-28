module

public import Theory.AtlasPort.LinearGroups.G2.ShortRootProducts.CentralizerCore.Coordinates

/-!+# Reduction of the short-root residual core to parabolic containment

The calculation inside the long parabolic identifies the two-residual with
the concrete affine block, and its embedded two-core with the A–B root
plane. These conclusions apply to the full centralizer as soon as its
containment in that parabolic is established. The containment premise is
explicit: these theorems do not yet supply the unconditional model identity.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), 16.1.4(1), printed p.1171, and the final case (a)
on printed pp.1202–1203. The two-residual and two-core retain their distinct
conventions and their actual inclusions into the split-octonion G₂ model.
-/

public section

open Subgroup Theory.GroupTheory

namespace Atlas.G2.ShortRootProducts.CentralizerCore
open LieParabolicSetup
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

/-- The sole geometric premise identifies the full and relative centralizers. -/
theorem centralizerTwoResidual_rootC_of_parabolic_containment
    (hq : 2 < Nat.card F) (a : F) (ha : a ≠ 0)
    (hplacement : centralizer ({rootC a} : Set (Model F)) ≤ parabolic₂) :
    centralizerTwoResidual (rootC a) = residualBlock := by
  have hc : centralizer ({rootC a} : Set (Model F)) = centralizerProduct := by
    rw [← parabolic_inf_centralizer_rootC a ha, inf_eq_right.mpr hplacement]
  unfold centralizerTwoResidual
  rw [hc]
  exact centralizerProduct_twoResidual hq

/-- The actual embedded core, conditional only on the parabolic placement. -/
theorem centralizerResidualCore_rootC_of_parabolic_containment
    (hq : 2 < Nat.card F) (a : F) (ha : a ≠ 0)
    (hplacement : centralizer ({rootC a} : Set (Model F)) ≤ parabolic₂) :
    centralizerResidualCore (rootC a) = longRootLocal := by
  unfold centralizerResidualCore
  rw [centralizerTwoResidual_rootC_of_parabolic_containment hq a ha hplacement]
  exact residualBlock_pCoreIn

end Atlas.G2.ShortRootProducts.CentralizerCore
