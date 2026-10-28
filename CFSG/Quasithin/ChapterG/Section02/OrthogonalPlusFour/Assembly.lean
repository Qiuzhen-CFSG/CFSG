module

public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Model
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Modules
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse

/-!
# Assembly of the proved parts of G.2.6

The genuine source hypothesis supplies generation, the central-kernel
factorization and the normal central series. Its marked quotient model also
discharges every structural premise of the two-factor recognition theorem.
The resulting data retain the canonical S/S₂ coordinates, actual factor
preimages, commutator images, opposite fixed spaces and finite natural sums.

The two multiplicities are still independent here. The source's common
multiplicity is a separate, unresolved obligation; `factorConclusion` and
the Chapter 15 adapter explicitly retain that equality. In particular this
module does not advertise the weaker decomposition as all of G.2.6(5).

Source: Aschbacher–Smith, G.2.6, printed p.336/PDF p.347.
-/

@[expose] public noncomputable section
open Subgroup InvertedCubicTensor
open scoped Pointwise IsMulCommutative
open Representation.BinaryOffender Representation.BinaryQuadraticPair
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

namespace Hypothesis
variable (d : Hypothesis D g)
include d

/-- Clauses (1)--(4), including the actual products and relative normality.
The series has endpoints 1 and S, and its two middle terms are V_L and S₂. -/
theorem source_structure :
    D.I g = D.L ⊔ D.U ∧
    (D.I g : Set G) = (D.L : Set G) * (D.U : Set G) ∧
    D.S g = coreProduct D g ∧
    (D.S g : Set G) = (D.W g : Set G) * (conjugate (D.W g) g : Set G) ∧
    (S₂ D g : Set G) = (D.VL : Set G) * (D.S₂ g : Set G) ∧
    D.VL ≤ S₂ D g ∧ S₂ D g ≤ D.S g ∧
    (D.VL.subgroupOf (D.I g)).Normal ∧
    ((S₂ D g).subgroupOf (D.I g)).Normal ∧
    ((D.S g).subgroupOf (D.I g)).Normal ∧
    D.VL ≤ centralizer (D.S g : Set G) ∧ ⁅S₂ D g, D.I g⁆ ≤ D.VL := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := d.normal_layers
  exact ⟨d.I_eq_LU, d.I_product, d.S_eq_coreProduct, d.S_product,
    S₂_product d.I_normalizes_VL, h₁, h₂, h₃, h₄, normal_subgroupOf_of_le_normalizer (core_normalized D g), d.central_first_layer.trans inf_le_right, h₅⟩

end Hypothesis

section ModuleData
variable [((S₂ D g).subgroupOf (D.S g)).Normal]
  [IsElementaryAbelian 2 (Quotient D g)]

/-- The proved module data, with the original quotient coordinates and
ordered model. This record deliberately makes no equal-multiplicity claim. -/
structure SourceModuleData (d : Hypothesis D g) where
  representation : Representation (ZMod 2) (S₃ × S₃) (Additive (Quotient D g))
  conjugation : Representation.BinaryConjugationSection (D.I g) (D.S g) (S₂ D g)
    (representation.comp (moduleProjection d.quotientSymmetricEquiv))
  decomposition : ProductDecomposition representation
  coordinates : ∀ s : D.S g, (conjugation.coordinates s).toAdd =
    Additive.ofMul (QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g)) s)
  marks : IsCompl (conjugation.imageSpace (D.W g))
    (conjugation.imageSpace (conjugate (D.W g) g))
  odd_fixed : fixedSpace (representation.comp (moduleProjection d.quotientSymmetricEquiv))
    (D.L.subgroupOf (D.I g)) = ⊥
  left_image : quotientImage D g
    ⁅D.S g, factorPreimage d.quotientSymmetricEquiv ProductDecomposition.leftFactor⁆ =
      binarySubgroup decomposition.left.toSubmodule
  right_image : quotientImage D g
    ⁅D.S g, factorPreimage d.quotientSymmetricEquiv ProductDecomposition.rightFactor⁆ =
      binarySubgroup decomposition.right.toSubmodule
  left_fixed : decomposition.left.toSubmodule =
    fixedSpace (representation.comp (moduleProjection d.quotientSymmetricEquiv))
      ((factorPreimage d.quotientSymmetricEquiv ProductDecomposition.rightFactor).subgroupOf (D.I g))
  right_fixed : decomposition.right.toSubmodule =
    fixedSpace (representation.comp (moduleProjection d.quotientSymmetricEquiv))
      ((factorPreimage d.quotientSymmetricEquiv ProductDecomposition.leftFactor).subgroupOf (D.I g))

/-- Recognition applied to the actual marked source configuration, with
all structural, geometric and quotient-model premises discharged. -/
theorem Hypothesis.source_module_data (d : Hypothesis D g) : Nonempty (SourceModuleData d) := by
  obtain ⟨σ, c, r, hc, hm, hf, hl, hr, hlf, hrf⟩ :=
    source_quotient_factor_modules d d.I_eq_LU d.S_normalizes_U d.S_eq_coreProduct
      d.VL_eq_sup_conjugate_V d.VL_inf_U d.quotientSymmetricEquiv
      d.quotientSymmetricEquiv_L_image d.symmetricUFirst d.symmetricUSecond
      d.quotientSymmetricEquiv_U_image d.symmetricImage_U_split.2.1
      d.symmetricImage_U_split.2.2
  exact ⟨⟨σ, c, r, hc, hm, hf, hl, hr, hlf, hrf⟩⟩

namespace SourceModuleData
variable {d : Hypothesis D g} (f : SourceModuleData d)

/-- The outstanding common-multiplicity clause is exactly equality of
the dimensions of these actual, ordered factor summands. -/
theorem commonMultiplicity_iff_finrank :
    f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity ↔
      Module.finrank (ZMod 2) f.decomposition.left.toSubmodule =
        Module.finrank (ZMod 2) f.decomposition.right.toSubmodule := by
  obtain ⟨hl, hr⟩ := f.decomposition.finranks
  rw [hl, hr]
  omega

/-- The actual residual-factor version used in Chapter 15. Only the
common-multiplicity clause remains explicit; all other inputs are proved
from the original G.2.6 source hypothesis. -/
def factorConclusion (hsame : f.decomposition.leftMultiplicity =
    f.decomposition.rightMultiplicity) :
    Chapter15Collapse.FactorModuleConclusion (D.I g) (D.S g) (S₂ D g) D.L
      (moduleProjection d.quotientSymmetricEquiv) f.representation := by
  have hr := Chapter15Collapse.source_oddFactor_modules
    (moduleProjection d.quotientSymmetricEquiv) D.L
    (d.I_eq_LU.symm ▸ le_sup_left) d.quotientSymmetricEquiv_L_image
    f.representation f.conjugation f.decomposition
  exact {
    conjugation := f.conjugation
    decomposition := f.decomposition
    sameMultiplicity := hsame
    left_residual := hr.1
    right_residual := hr.2
    left_fixed := f.left_fixed
    right_fixed := f.right_fixed }

end SourceModuleData
end ModuleData

/-- The source-only existence statement also constructs the quotient's
normality and elementary abelian instances. The factor multiplicities
remain separate, as in `SourceModuleData`. -/
theorem Hypothesis.source_modules (d : Hypothesis D g) :
    letI := moduleSectionNormal d d.I_eq_LU
    letI := moduleSectionElementary d d.I_eq_LU d.S_normalizes_U d.S_eq_coreProduct
    Nonempty (SourceModuleData d) := by
  let := moduleSectionNormal d d.I_eq_LU
  let := moduleSectionElementary d d.I_eq_LU d.S_normalizes_U d.S_eq_coreProduct
  exact d.source_module_data

end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
