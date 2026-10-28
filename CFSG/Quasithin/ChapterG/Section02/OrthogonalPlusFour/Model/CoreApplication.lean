module

public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Model.Assembly
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Core

/-!
# Applying the marked model to the central-kernel argument

The geometry and generation results discharge every preceding premise of
the independent central-kernel proof: I=LU, S normalizes U, and the actual
L-image is A₃×A₃ under the intrinsic quotient model. Thus S=WWᵍ follows
without a factorization assumption. The plus-image comparisons use the
same star projection as the original hypotheses.

Together with Model.Assembly this proves G.2.6(1–4). The representation
decomposition in clause (5) remains with its separate source assembly.
Source: Aschbacher–Smith, G.2.6, printed p.336/PDF p.347.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open Setup
namespace Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G} (d : Hypothesis D g)
include d

/-- The literal model-map premise in the central-kernel theorem. -/
theorem coreModelProjection_L_image :
    (D.L.subgroupOf (D.I g)).map (coreModelProjection D g d.quotientSymmetricEquiv) =
      alternatingPair :=
  d.quotientSymmetricEquiv_L_image

/-- G.2.6(2), after the marked geometry has supplied the preceding source conclusions. -/
theorem S_eq_coreProduct : D.S g = coreProduct D g :=
  core_eq_coreProduct_of_model d d.I_eq_LU d.S_normalizes_U
    d.quotientSymmetricEquiv d.coreModelProjection_L_image

theorem S_product :
    (D.S g : Set G) = (D.W g : Set G) * (conjugate (D.W g) g : Set G) :=
  core_eq_product_of_model d d.I_eq_LU d.S_normalizes_U
    d.quotientSymmetricEquiv d.coreModelProjection_L_image

theorem coreProduct_normal_in_I : ((coreProduct D g).subgroupOf (D.I g)).Normal :=
  coreProduct_normal d d.I_eq_LU d.S_normalizes_U

variable [((coreProduct D g).subgroupOf (D.I g)).Normal]

/-- Plus images and original starred images agree through the literal quotient maps. -/
def plusImageStarEquiv (A : Subgroup G) (hAI : A ≤ D.I g) :
    coreImage D g A ≃* D.star A :=
  coreImageEquivStar d d.I_eq_LU d.S_normalizes_U
    d.quotientSymmetricEquiv d.coreModelProjection_L_image
    d.quotientIStarEquiv d.quotientIStarEquiv_mk A hAI

theorem plusImageStarEquiv_comp (A : Subgroup G) (hAI : A ≤ D.I g) :
    (d.plusImageStarEquiv A hAI).toMonoidHom.comp (coreImageProjection D g A hAI) =
      starProjection D A (hAI.trans d.I_le_LT) :=
  coreImageEquivStar_comp d d.I_eq_LU d.S_normalizes_U
    d.quotientSymmetricEquiv d.coreModelProjection_L_image
    d.quotientIStarEquiv d.quotientIStarEquiv_mk A hAI

/-- The actual U⁺≃U* comparison, without an extra model or compatibility premise. -/
def plusUStarEquiv : coreImage D g D.U ≃* D.star D.U :=
  d.plusImageStarEquiv D.U le_sup_left

/-- The odd-residual argument identifies the actual L⁺ with E₉. -/
def plusLEquivNine : coreImage D g D.L ≃* Multiplicative (Fin 2 → ZMod 3) :=
  (d.plusImageStarEquiv D.L (d.I_eq_LU.symm ▸ le_sup_left)).trans d.L_model

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
