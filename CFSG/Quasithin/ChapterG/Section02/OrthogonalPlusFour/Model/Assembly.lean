module

public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Model.StarGeometry
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Model.ModuleGeometry

/-!
# The geometry and generation branch of G.2.6

The marked singular-point stabilizers generate the determinant group. The
residual lift through the original star map gives I=LU, hence S≤T and the
intrinsic quotient comparisons. This discharges the earlier geometry premises
in the irreducibility, central-layer and marked-intersection calculations.
The symmetric quotient carries the actual L-image to A₃×A₃, preserving the
ordered factors and the original projections used by the core argument.

The core factorization and the decomposition of S/S₂ belong to the separate
source assembly. The Chapter 15 closure intersection retains its independent
coprime-action containment, while all preceding geometry is discharged here.
Source: Aschbacher–Smith, G.2.6, printed p.336/PDF p.347, using G.2.3(2),
printed pp.333–334; the marked Chapter 15 application is 15.3.54, p.1146.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open Setup ClassicalOrthogonal.FourPlusMatrix
namespace Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G} (d : Hypothesis D g)
include d

/-- The determinant formulation consumed by the displacement calculations. -/
theorem pointVector_det (z : D.V₁) : (d.pointVector z).det = 0 := by
  simpa only [determinantForm_apply] using d.pointVector_singular z

/-- The original starred U is the actual singular-point stabilizer. -/
def starUStabilizerEquiv : D.star D.U ≃* d.pointStabilizer :=
  (d.starModelImageEquiv D.U le_sup_right).trans
    (MulEquiv.subgroupCongr d.modelImage_U_eq_pointStabilizer)

/-- G.2.6(1), with the starred-generation premise discharged. -/
theorem I_eq_LU : D.I g = D.L ⊔ D.U :=
  d.I_eq_LU_of_star d.star_I_eq_star_LU

theorem I_product : (D.I g : Set G) = (D.L : Set G) * (D.U : Set G) :=
  d.I_product_of_star d.star_I_eq_star_LU

theorem g_mem_I : g ∈ D.I g := d.g_mem_I_of_star d.star_I_eq_star_LU

theorem S_eq_star_kernel : D.S g = D.I g ⊓ D.LT.pCoreIn 2 :=
  d.S_eq_star_kernel_of_star d.star_I_eq_star_LU

theorem S_le_T : D.S g ≤ D.T := d.S_le_T_of_star d.star_I_eq_star_LU

theorem S_normalizes_U : D.S g ≤ normalizer (D.U : Set G) :=
  d.S_normalizes_U_of_star d.star_I_eq_star_LU

theorem W_index_eq_four : (D.W g).relIndex D.U = 4 :=
  d.W_index_eq_four_of_star d.star_I_eq_star_LU

/-- Irreducibility of the actual generated group, without a generation premise. -/
theorem I_on_VL_irreducible (A : Subgroup G) (hA : A ≤ D.VL)
    (hN : D.I g ≤ normalizer (A : Set G)) : A = ⊥ ∨ A = D.VL :=
  d.I_irreducible d.star_I_eq_star_LU A hA hN

theorem central_first_layer : D.VL ≤ D.S g ⊓ centralizer (D.S g : Set G) :=
  d.central_first_layer_of_star d.star_I_eq_star_LU

/-- The normal I-series and G.2.6(4), prior to the independent core factorization. -/
theorem normal_layers :
    D.VL ≤ S₂ D g ∧ S₂ D g ≤ D.S g ∧
      (D.VL.subgroupOf (D.I g)).Normal ∧ ((S₂ D g).subgroupOf (D.I g)).Normal ∧
      ⁅S₂ D g, D.I g⁆ ≤ D.VL :=
  d.layers_of_star d.star_I_eq_star_LU

/-- The source hyperplane is the displacement subgroup of the literal U-action. -/
theorem commutator_VL_U : ⁅D.VL, D.U⁆ = D.V :=
  d.commutator_VL_U_eq_V d.pointVector_det d.modelImage_U_eq_pointStabilizer

theorem VL_inf_U : D.VL ⊓ D.U = D.V :=
  d.VL_inf_U_eq_V d.pointVector_det d.modelImage_U_eq_pointStabilizer

theorem VL_inf_conjugate_U : D.VL ⊓ conjugate D.U g = conjugate D.V g :=
  d.VL_inf_conjugate_U_eq_conjugate_V d.pointVector_det d.modelImage_U_eq_pointStabilizer

/-- The marked intersection used for directness after quotienting by S₂. -/
theorem VL_inf_marks :
    D.VL ⊓ (D.U ⊓ conjugate D.U g) = D.V ⊓ conjugate D.V g :=
  d.VL_inf_U_inf_conjugate_U d.pointVector_det d.modelImage_U_eq_pointStabilizer

/-- The marked point misses the opposite closure, as needed for Chapter 15 commutators. -/
theorem point_inf_conjugate_U : D.V₁ ⊓ conjugate D.U g = ⊥ := by
  calc
    D.V₁ ⊓ conjugate D.U g = D.V₁ ⊓ (D.VL ⊓ conjugate D.U g) := by
      rw [← inf_assoc, inf_eq_left.mpr (point_le_VL D)]
    _ = ⊥ := by rw [d.VL_inf_conjugate_U, d.point_inf_conjugate_V]

theorem conjugate_point_inf_U : conjugate D.V₁ g ⊓ D.U = ⊥ := by
  have hpoint : conjugate D.V₁ g ≤ D.VL :=
    (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (point_le_VL D)).trans
      d.conjugate_VL_eq.le
  calc
    conjugate D.V₁ g ⊓ D.U = conjugate D.V₁ g ⊓ (D.VL ⊓ D.U) := by
      rw [← inf_assoc, inf_eq_left.mpr hpoint]
    _ = ⊥ := by rw [d.VL_inf_U, d.conjugate_point_inf_V]

/-- The intrinsic quotient identified with the original starred LU. -/
def quotientStarEquiv : (D.I g ⧸ pCore 2 (D.I g)) ≃* D.star (D.L ⊔ D.U) :=
  d.coreQuotientStarEquiv d.star_I_eq_star_LU

theorem quotientStarEquiv_mk (i : D.I g) :
    d.quotientStarEquiv (QuotientGroup.mk' (pCore 2 (D.I g)) i) = d.IStarProjection i := rfl

/-- The same comparison with codomain the literal starred I, for the plus quotient. -/
def quotientIStarEquiv : (D.I g ⧸ pCore 2 (D.I g)) ≃* D.star (D.I g) :=
  d.quotientStarEquiv.trans (MulEquiv.subgroupCongr d.star_I_eq_star_LU.symm)

theorem quotientIStarEquiv_mk (i : D.I g) :
    d.quotientIStarEquiv (QuotientGroup.mk' (pCore 2 (D.I g)) i) =
      starProjection D (D.I g) d.I_le_LT i := rfl

def quotientMatrixEquiv : (D.I g ⧸ pCore 2 (D.I g)) ≃* PairSL (F := ZMod 2) :=
  d.coreQuotientEquiv d.star_I_eq_star_LU

theorem quotientMatrixEquiv_mk (i : D.I g) :
    d.quotientMatrixEquiv (QuotientGroup.mk' (pCore 2 (D.I g)) i) =
      d.matrixProjection (inclusion d.I_le_LU i) := rfl

/-- The intrinsic quotient acts through the supplied natural coordinates. -/
theorem quotientMatrixEquiv_equivariant (i : D.I g) (v : D.VL) :
    (d.coordinates.symm (Multiplicative.ofAdd
      (matrixAction (d.quotientMatrixEquiv (QuotientGroup.mk' (pCore 2 (D.I g)) i))
        (d.coordinates v).toAdd)) : G) = (i : G) * v * (i : G)⁻¹ :=
  d.coreQuotientEquiv_equivariant d.star_I_eq_star_LU i v

def quotientOrthogonalEquiv :
    (D.I g ⧸ pCore 2 (D.I g)) ≃* ClassicalOrthogonal.POmegaPlus 2 (ZMod 2) :=
  d.coreOrthogonalEquiv d.star_I_eq_star_LU

theorem quotientOrthogonalEquiv_mk (i : D.I g) :
    d.quotientOrthogonalEquiv (QuotientGroup.mk' (pCore 2 (D.I g)) i) =
      projectiveEquiv (d.matrixProjection (inclusion d.I_le_LU i)) := rfl

def quotientSymmetricEquiv :
    (D.I g ⧸ pCore 2 (D.I g)) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
  d.coreSymmetricEquiv d.star_I_eq_star_LU

theorem quotientSymmetricEquiv_mk (i : D.I g) :
    d.quotientSymmetricEquiv (QuotientGroup.mk' (pCore 2 (D.I g)) i) =
      pairPermEquiv (d.matrixProjection (inclusion d.I_le_LU i)) := rfl

/-- Every marked subgroup has the same image under the intrinsic and original maps. -/
theorem quotientSymmetricEquiv_image (A : Subgroup G) :
    (A.subgroupOf (D.I g)).map
      (d.quotientSymmetricEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (D.I g)))) =
        d.symmetricImage A := by
  rw [symmetricImage, modelImage, map_map]
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨inclusion d.I_le_LU a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, d.I_eq_LU.symm ▸ a.property⟩, ha, rfl⟩

/-- This discharges the alternating-pair marking premise of the core-factorization proof. -/
theorem quotientSymmetricEquiv_L_image :
    (D.L.subgroupOf (D.I g)).map
      (d.quotientSymmetricEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (D.I g)))) =
        (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3)) :=
  (d.quotientSymmetricEquiv_image D.L).trans d.symmetricImage_L

/-- The two independent Sylow factors are also marked through the intrinsic quotient. -/
theorem quotientSymmetricEquiv_U_image :
    (D.U.subgroupOf (D.I g)).map
      (d.quotientSymmetricEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (D.I g)))) =
        d.symmetricUFirst.prod d.symmetricUSecond :=
  (d.quotientSymmetricEquiv_image D.U).trans d.symmetricImage_U_split.1

end Hypothesis

namespace Chapter15
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
variable {G : Type*} [Group G] [Finite G]
variable {Z ZS Zperp V Y T : Subgroup G} {g : G}

/-- The actual Chapter 15 intersection, with only its separate coprime-action
containment left to the source application. -/
theorem closure_intersection_eq_of_contained
    (d : Hypothesis (setup Z Zperp Y T) g)
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS) (hspan : localSpan Z Y = V)
    (hcontained : closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g ≤ V) :
    closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g =
      Zperp ⊓ rightConjugate Zperp g :=
  closure_intersection_eq_of_le d hZS hperp hspan
    d.pointVector_det d.modelImage_U_eq_pointStabilizer hcontained

/-- No marked-vector choice or earlier geometry premise remains in the E₄ comparison. -/
def closureIntersectionEquivOfContained
    (d : Hypothesis (setup Z Zperp Y T) g)
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS) (hspan : localSpan Z Y = V)
    (hcontained : closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g ≤ V) :
    (closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g : Subgroup G) ≃*
      Multiplicative (Fin 2 → ZMod 2) :=
  closureIntersectionEquiv d hZS hperp hspan d.pointVector_det
    d.modelImage_U_eq_pointStabilizer hcontained
    (Classical.choose d.exists_pointVector_ne_zero)
    (Classical.choose_spec d.exists_pointVector_ne_zero)

end Chapter15
end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
