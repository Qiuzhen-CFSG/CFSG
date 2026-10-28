module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.CentralKernel.Interface
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.CentralKernel.Residual
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.CentralKernel.RootLift

/-!
# Central-kernel elimination for G.2.5

The actual quotient I/(WWᵍWʰ) maps onto the original L* with central
two-kernel. The cubic point-stabilizer action places U⁺ in L⁺, making the
quotient two-perfect. The point radical and the extra root factor map
faithfully and cover a Sylow image. Transfer and Frattini nongeneration
then kill the central kernel, giving both the subgroup identity and the
literal ordered product with the original g and h.

The proof applies to every field of order 2ⁿ, including n = 1, and does
not identify the kernel with the possibly larger center of SL₃(F).
Only U≤T, I*=L*, the additive model for U*, and [V,U]=V₁ are needed from
the permitted preceding outputs; the Frattini bound and the full radical
identification are unnecessary here. Their source producers and the
discharge of the remaining preceding outputs belong to `Structure`.

Source: Aschbacher–Smith G.2.5(3), printed pp.335–336, referring to G.2.3,
printed pp.333–334. This completes the central-kernel implication, while
the full source theorem remains with structural assembly.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree
open Setup

variable {G : Type*} [Group G] [Finite G]
  {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : Hypothesis D F n g h)

namespace CentralKernel

/-- The central two-kernel of the literal I/P star map vanishes. Both
local inputs to transfer are constructed from the preceding source outputs. -/
theorem starMap_ker_eq_bot (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L)
    (eU : D.star D.U ≃* Multiplicative (Fin 2 → F))
    (hmove : ⁅D.V, D.U⁆ = D.V₁) :
    letI := d.WProduct_normal hUT hstar.ge
    (starMap d hUT hstar).ker = ⊥ := by
  let := d.WProduct_normal hUT hstar.ge
  exact starMap_ker_eq_bot_of_rootLift d hUT hstar
    (isPPerfect_quotient d hUT hstar hmove) (hasRootLift d hUT hstar eU hmove)

end CentralKernel

namespace Hypothesis

include d

/-- G.2.5(3), as a subgroup equality, from the preceding starred generation,
radical model and movement outputs. No central-kernel premise remains. -/
theorem S_eq_WProduct_of_star (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L)
    (eU : D.star D.U ≃* Multiplicative (Fin 2 → F))
    (hmove : ⁅D.V, D.U⁆ = D.V₁) : S D g h = WProduct D g h := by
  let := d.WProduct_normal hUT hstar.ge
  exact CentralKernel.core_eq_product_of_ker_eq_bot d hUT hstar
    (CentralKernel.starMap_ker_eq_bot d hUT hstar eU hmove)

/-- The literal ordered product in G.2.5(3), retaining the original g and h. -/
theorem S_eq_product_of_star (hUT : D.U ≤ D.T)
    (hstar : D.star (I D g h) = D.star D.L)
    (eU : D.star D.U ≃* Multiplicative (Fin 2 → F))
    (hmove : ⁅D.V, D.U⁆ = D.V₁) :
    (S D g h : Set G) = (W D g h : Set G) * (conjugate (W D g h) g : Set G) *
      (conjugate (W D g h) h : Set G) := by
  rw [d.S_eq_WProduct_of_star hUT hstar eU hmove]
  exact d.WProduct_eq_product hUT hstar.ge

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.LinearThree
