module

public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Multiplicity
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Assembly

/-!
# The factor-interchange route on the literal Chapter 15 quotient

The source construction supplies the actual two natural sums. An additional
T-conjugacy between their factor preimages gives common multiplicity.
Central collapse and the literal subgroup identifications preserve this
multiplicity. The resulting data and equality are the literal arguments
required by `literal_application_of_common_multiplicity` to give all five
clauses of 15.3.54. No representation or decomposition is an input.

The factor-conjugacy witness is still explicit. Its construction from the
earlier Chapter 15 orthogonal action remains a source obligation.

Source: Aschbacher–Smith, 15.3.54, printed p.1146/PDF p.1163.
-/

@[expose] public noncomputable section
open Subgroup InvertedCubicTensor
open scoped Pointwise IsMulCommutative
open Representation.BinaryOffender Representation.BinaryQuadraticPair
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Multiplicity
open Setup Chapter15Collapse Chapter15Assembly
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem transport_complete
    {I P V Y I' P' V' Y' : Subgroup G}
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (a : FactorData I P V Y M)
    (ha : a.decomposition.leftMultiplicity = a.decomposition.rightMultiplicity)
    (hI : I = I') (hP : P = P') (hV : V = V') (hY : Y = Y') :
    ∃ b : FactorData I' P' V' Y' M,
      b.decomposition.leftMultiplicity = b.decomposition.rightMultiplicity ∧
      Nonempty (FactorModuleConclusion I' P' V' Y'
        (b.model.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I'))) b.representation) := by
  subst I' P' V' Y'
  exact ⟨a, ha, ⟨a.complete ha⟩⟩

variable {Z ZS Zperp V Y T : Subgroup G} {g : G}
variable [((S₂ (Chapter15.setup Z Zperp Y T) g).subgroupOf
  ((Chapter15.setup Z Zperp Y T).S g)).Normal]
  [IsElementaryAbelian 2 (Quotient (Chapter15.setup Z Zperp Y T) g)]

/-- Construct the actual literal module data with common multiplicity,
ready for the full 15.3.54 assembly theorem. -/
theorem literal_common_data_of_factorExchange
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS)
    (hspan : localSpan Z Y = V)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g)
    (hΩ : omegaCenter T = Z) (hexchange : FactorExchange d) :
    ∃ f : FactorData (pairI Z ZS g) (pairP Z ZS g) V Y
        (Additive (Quotient (Chapter15.setup Z Zperp Y T) g)),
      f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity ∧
      Nonempty (FactorModuleConclusion (pairI Z ZS g) (pairP Z ZS g) V Y
        (f.model.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (pairI Z ZS g))))
          f.representation) := by
  obtain ⟨f⟩ := d.source_module_data
  have hΩD : omegaCenter (Chapter15.setup Z Zperp Y T).T ≤
      (Chapter15.setup Z Zperp Y T).VL := by
    change omegaCenter T ≤ (Chapter15.setup Z Zperp Y T).VL
    rw [hΩ]
    exact point_le_VL (Chapter15.setup Z Zperp Y T)
  let a := factorData_of_source f hΩD
  have ha : a.decomposition.leftMultiplicity = a.decomposition.rightMultiplicity := by
    change (factorData_of_source f hΩD).decomposition.leftMultiplicity =
      (factorData_of_source f hΩD).decomposition.rightMultiplicity
    rw [factorData_of_source_decomposition]
    exact f.common_of_factorExchange hexchange
  exact transport_complete a ha (Chapter15.I_eq (Y := Y) (T := T) g hZS hperp)
    (Chapter15.S_eq (Y := Y) (T := T) g hZS hperp)
    (Chapter15.VL_eq (Zperp := Zperp) (T := T) hspan) rfl

end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Multiplicity
