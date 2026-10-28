module

public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Assembly

/-!
# Assembly on the literal Chapter 15 quotient

The earlier 15.3.48/53 hypotheses are retained in the actual source setup.
All generation, core, geometry, central collapse and representation inputs
are supplied by the proved G.2.6 branches. In particular the resulting
section is P/V, with the same quotient coordinates as P/P₀, and its actors
are the actual residuals O²(Y ∩ Nᵢ).

`literal_factor_data` constructs both finite natural sums without an assumed
module decomposition. Their common multiplicity remains unproved.
`literal_application_of_common_multiplicity` states this last obligation
explicitly and otherwise assembles all five clauses of 15.3.54. Discharge of
the earlier source setup remains with the Chapter G and Chapter 15 owners.

Source: Aschbacher–Smith, 15.3.54, printed p.1146/PDF p.1163, using
G.2.6 on printed p.336/PDF p.347.
-/

@[expose] public noncomputable section
open Subgroup InvertedCubicTensor
open scoped Pointwise IsMulCommutative
open Representation.BinaryOffender Representation.BinaryQuadraticPair
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Assembly
open Setup Chapter15Collapse
variable {G : Type*} [Group G]
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

/-- The actual intrinsic quotient model, its conjugation section and two
residual-factor natural sums. Equality of multiplicities is not a field. -/
structure FactorData (I P V Y : Subgroup G) (M : Type*)
    [AddCommGroup M] [Module (ZMod 2) M] where
  model : (I ⧸ pCore 2 I) ≃* (S₃ × S₃)
  representation : Representation (ZMod 2) (S₃ × S₃) M
  conjugation : Representation.BinaryConjugationSection I P V
    (representation.comp (model.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))))
  decomposition : ProductDecomposition representation
  odd_image : (Y.subgroupOf I).map
    (model.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))) =
      (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3))
  left_residual : conjugation.imageSpace
    ⁅P, oddFactor (model.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))) Y
      ProductDecomposition.leftFactor⁆ = decomposition.left.toSubmodule
  right_residual : conjugation.imageSpace
    ⁅P, oddFactor (model.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))) Y
      ProductDecomposition.rightFactor⁆ = decomposition.right.toSubmodule
  left_fixed : decomposition.left.toSubmodule =
    fixedSpace (representation.comp (model.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))))
      ((actorPreimage (model.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I)))
        ProductDecomposition.rightFactor).subgroupOf I)
  right_fixed : decomposition.right.toSubmodule =
    fixedSpace (representation.comp (model.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))))
      ((actorPreimage (model.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I)))
        ProductDecomposition.leftFactor).subgroupOf I)

namespace FactorData
variable {I P V Y I' P' V' Y' : Subgroup G}

/-- Transport the subgroup markings, keeping the representation carrier fixed. -/
def transport (f : FactorData I P V Y M)
    (hI : I = I') (hP : P = P') (hV : V = V') (hY : Y = Y') :
    FactorData I' P' V' Y' M := by
  subst I' P' V' Y'
  exact f

/-- Subgroup transport preserves the actual two finite-sum multiplicities. -/
theorem transport_common (f : FactorData I P V Y M)
    (hI : I = I') (hP : P = P') (hV : V = V') (hY : Y = Y') :
    (f.transport hI hP hV hY).decomposition.leftMultiplicity =
      (f.transport hI hP hV hY).decomposition.rightMultiplicity ↔
    f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity := by
  subst I' P' V' Y'
  rfl

/-- Convert to the existing full consumer interface precisely when the
remaining common-multiplicity clause has been established. -/
def complete (f : FactorData I P V Y M)
    (hsame : f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity) :
    FactorModuleConclusion I P V Y
      (f.model.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))) f.representation where
  conjugation := f.conjugation
  decomposition := f.decomposition
  sameMultiplicity := hsame
  left_residual := f.left_residual
  right_residual := f.right_residual
  left_fixed := f.left_fixed
  right_fixed := f.right_fixed

end FactorData

variable [Finite G] {D : Setup G} {g : G}
variable [((S₂ D g).subgroupOf (D.S g)).Normal]
  [IsElementaryAbelian 2 (Quotient D g)]

/-- Collapse the central middle layer and use the literal residual actors.
The coordinates and decomposition are preserved, without a multiplicity premise. -/
def factorData_of_source {d : Hypothesis D g} (f : SourceModuleData d)
    (hΩ : omegaCenter D.T ≤ D.VL) :
    FactorData (D.I g) (D.S g) D.VL D.L (Additive (Quotient D g)) := by
  have hc := source_collapse d hΩ
  let c := section_with_kernel f.conjugation hc.2.2.2.2.2
  have hr := source_oddFactor_modules (moduleProjection d.quotientSymmetricEquiv)
    D.L (d.I_eq_LU.symm ▸ le_sup_left) d.quotientSymmetricEquiv_L_image
    f.representation c f.decomposition
  exact {
    model := d.quotientSymmetricEquiv
    representation := f.representation
    conjugation := c
    decomposition := f.decomposition
    odd_image := d.quotientSymmetricEquiv_L_image
    left_residual := hr.1
    right_residual := hr.2
    left_fixed := f.left_fixed
    right_fixed := f.right_fixed }

/-- Central collapse changes only the kernel description, not the quotient map. -/
theorem factorData_of_source_coordinates {d : Hypothesis D g} (f : SourceModuleData d)
    (hΩ : omegaCenter D.T ≤ D.VL) :
    (factorData_of_source f hΩ).conjugation.coordinates = f.conjugation.coordinates := rfl

/-- The finite sums survive central collapse with their exact multiplicities. -/
theorem factorData_of_source_decomposition {d : Hypothesis D g} (f : SourceModuleData d)
    (hΩ : omegaCenter D.T ≤ D.VL) :
    (factorData_of_source f hΩ).decomposition = f.decomposition := rfl

open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.Nonabelian

/-- Apply the constructed factor modules to the exact Chapter 15 I, P, V and Y.
No quotient model, decomposition, or central-collapse conclusion is assumed. -/
theorem literal_factor_data {Z ZS Zperp V Y T : Subgroup G} {g : G}
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS)
    (hspan : localSpan Z Y = V)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g)
    (hΩ : omegaCenter T = Z) :
    letI := moduleSectionNormal d d.I_eq_LU
    letI := moduleSectionElementary d d.I_eq_LU d.S_normalizes_U d.S_eq_coreProduct
    Nonempty (FactorData (pairI Z ZS g) (pairP Z ZS g) V Y
      (Additive (Quotient (Chapter15.setup Z Zperp Y T) g))) := by
  let := moduleSectionNormal d d.I_eq_LU
  let := moduleSectionElementary d d.I_eq_LU d.S_normalizes_U d.S_eq_coreProduct
  obtain ⟨f⟩ := d.source_module_data
  have hΩD : omegaCenter (Chapter15.setup Z Zperp Y T).T ≤
      (Chapter15.setup Z Zperp Y T).VL := by
    change omegaCenter T ≤ (Chapter15.setup Z Zperp Y T).VL
    rw [hΩ]
    exact point_le_VL (Chapter15.setup Z Zperp Y T)
  exact ⟨(factorData_of_source f hΩD).transport (Chapter15.I_eq g hZS hperp)
    (Chapter15.S_eq g hZS hperp) (Chapter15.VL_eq hspan) rfl⟩

/-- All five literal clauses, conditional only on the still unproved common
multiplicity and the genuine earlier Chapter 15 setup. `literal_factor_data`
supplies the data argument without a module-recognition premise. -/
theorem literal_application_of_common_multiplicity
    {Z ZS Zperp V Y T : Subgroup G} {g : G}
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS)
    (hspan : localSpan Z Y = V)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g)
    (hΩ : omegaCenter T = Z)
    (f : FactorData (pairI Z ZS g) (pairP Z ZS g) V Y M)
    (hsame : f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity) :
    pairI Z ZS g = Y ⊔ closureU Z ZS ∧
    pairP Z ZS g = pairW Z ZS g ⊔ rightConjugate (pairW Z ZS g) g ∧
    (pairI Z ZS g : Set G) = (Y : Set G) * (closureU Z ZS : Set G) ∧
    (pairP Z ZS g : Set G) = (pairW Z ZS g : Set G) *
      (rightConjugate (pairW Z ZS g) g : Set G) ∧
    V ≤ pairP Z ZS g ⊓ centralizer (pairP Z ZS g : Set G) ∧
    closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g =
      Zperp ⊓ rightConjugate Zperp g ∧
    pairW Z ZS g ⊓ rightConjugate (pairW Z ZS g) g =
      closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g ∧
    Nonempty ((closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g : Subgroup G) ≃*
      Multiplicative (Fin 2 → ZMod 2)) ∧
    Nonempty ((pairW Z ZS g ⊓ rightConjugate (pairW Z ZS g) g : Subgroup G) ≃*
      Multiplicative (Fin 2 → ZMod 2)) ∧
    Nonempty (FactorModuleConclusion (pairI Z ZS g) (pairP Z ZS g) V Y
      (f.model.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (pairI Z ZS g))))
        f.representation) ∧
    rightConjugate (pairW Z ZS g) g ≤ normalizer (closureU Z ZS : Set G) ∧
    ⁅rightConjugate (pairW Z ZS g) g, closureU Z ZS⁆ ≤ pairW Z ZS g := by
  obtain ⟨hI, hP, hV, _, _, _, _, _, _, _, hperps, hmarks, hfour, hfourW, hfive⟩ :=
    literal_source_collapse hZS hperp hspan d hΩ
  have hp := literal_products hZS hperp d
  exact ⟨hI, hP, hp.1, hp.2, hV, hperps, hmarks, hfour, hfourW,
    ⟨f.complete hsame⟩, hfive⟩

end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Assembly
