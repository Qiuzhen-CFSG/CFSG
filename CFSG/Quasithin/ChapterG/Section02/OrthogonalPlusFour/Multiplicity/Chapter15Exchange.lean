module
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Multiplicity.Chapter15Exchange.NaturalImage
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Multiplicity.Chapter15Exchange.Transport
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Multiplicity.Chapter15Exchange.ConcreteModel
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Multiplicity.Chapter15

/-!
# The Sylow-action route to the literal Chapter 15 factor interchange

The earlier compatible wreath action gives order eight for the literal
conjugation image of T on V. Transport to the determinant coordinates
identifies the intrinsic I/O₂(I) factors with the actual tensor factors.
A concrete normalizer theorem on the fixed binary matrix space therefore
supplies the source right-conjugacy witness and common multiplicity.

The concrete normalizer theorem and the order-eight calculation are both
discharged in `literal_factorExchange`. The resulting `literal_common_data`
feeds all five clauses of 15.3.54 in `literal_application`, with no assumed
module decomposition or common multiplicity. The genuine earlier action,
Sylow condition and source markings remain inputs from the earlier Chapter 15
source assembly. This specializes to the
literal Chapter 15 setup; it makes no order-eight assertion for general G.2.6.

Source: Aschbacher–Smith, printed pp.336,1121–1122,1146–1147.
-/

@[expose] public noncomputable section
open Subgroup InvertedCubicTensor ClassicalOrthogonal.FourPlusMatrix
open scoped Pointwise IsMulCommutative
open Representation.BinaryOffender Representation.BinaryQuadraticPair
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Multiplicity.Chapter15Exchange
open Setup Chapter15Collapse Chapter15Assembly
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
variable {G : Type*} [Group G] [Finite G]

/-- The order-eight premise is discharged from the genuine earlier Chapter 15
action and Sylow hypotheses. Only the independent fixed-model normalizer
calculation remains explicit. -/
theorem literal_factorExchange_of_normalizer_exchange
    (hmodel : ∀ P : Subgroup MatrixActor,
      P ≤ normalizer ((matrixHom (F := ZMod 2)).range : Set MatrixActor) →
      Nat.card P = 8 → ∃ t ∈ P,
        tensorLeft.map (MulAut.conj t).toMonoidHom = tensorRight)
    {M Z Zperp V Y T : Subgroup G} {g : G}
    (a : NaturalOrthogonalAction M V) (hTM : T ≤ M)
    (hSyl : ∃ P : Sylow 2 M, (P : Subgroup M).map M.subtype = T)
    (hspan : localSpan Z Y = V)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g) : FactorExchange d :=
  factorExchange_of_normalizer_exchange d hmodel
    (literal_naturalAction_card_eight a hTM hSyl hspan d)

/-- The constructed witness feeds the literal consumer, preserving all four
source markings and constructing the actual module data and common multiplicity.
No action-image cardinality or factor exchange is an input to this application. -/
theorem literal_common_data_of_normalizer_exchange
    (hmodel : ∀ P : Subgroup MatrixActor,
      P ≤ normalizer ((matrixHom (F := ZMod 2)).range : Set MatrixActor) →
      Nat.card P = 8 → ∃ t ∈ P,
        tensorLeft.map (MulAut.conj t).toMonoidHom = tensorRight)
    {M Z ZS Zperp V Y T : Subgroup G} {g : G}
    [((S₂ (Chapter15.setup Z Zperp Y T) g).subgroupOf
      ((Chapter15.setup Z Zperp Y T).S g)).Normal]
    [IsElementaryAbelian 2 (Quotient (Chapter15.setup Z Zperp Y T) g)]
    (a : NaturalOrthogonalAction M V) (hTM : T ≤ M)
    (hSyl : ∃ P : Sylow 2 M, (P : Subgroup M).map M.subtype = T)
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS)
    (hspan : localSpan Z Y = V)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g)
    (hΩ : omegaCenter T = Z) :
    ∃ f : FactorData (pairI Z ZS g) (pairP Z ZS g) V Y
        (Additive (Quotient (Chapter15.setup Z Zperp Y T) g)),
      f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity ∧
      Nonempty (FactorModuleConclusion (pairI Z ZS g) (pairP Z ZS g) V Y
        (f.model.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (pairI Z ZS g))))
          f.representation) :=
  literal_common_data_of_factorExchange hZS hperp hspan d hΩ
    (literal_factorExchange_of_normalizer_exchange hmodel a hTM hSyl hspan d)

/-- The genuine earlier action and local Sylow condition construct the actual
right-conjugacy witness. Neither a model-normalizer theorem nor the order of
the natural image is an extra premise. -/
theorem literal_factorExchange
    {M Z Zperp V Y T : Subgroup G} {g : G}
    (a : NaturalOrthogonalAction M V) (hTM : T ≤ M)
    (hSyl : ∃ P : Sylow 2 M, (P : Subgroup M).map M.subtype = T)
    (hspan : localSpan Z Y = V)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g) : FactorExchange d :=
  factorExchange_of_natural_image_card d
    (literal_naturalAction_card_eight a hTM hSyl hspan d)

/-- The literal consumer with the interchange and common multiplicity proved
from the earlier compatible action. All source subgroup markings are retained. -/
theorem literal_common_data
    {M Z ZS Zperp V Y T : Subgroup G} {g : G}
    [((S₂ (Chapter15.setup Z Zperp Y T) g).subgroupOf
      ((Chapter15.setup Z Zperp Y T).S g)).Normal]
    [IsElementaryAbelian 2 (Quotient (Chapter15.setup Z Zperp Y T) g)]
    (a : NaturalOrthogonalAction M V) (hTM : T ≤ M)
    (hSyl : ∃ P : Sylow 2 M, (P : Subgroup M).map M.subtype = T)
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS)
    (hspan : localSpan Z Y = V)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g)
    (hΩ : omegaCenter T = Z) :
    ∃ f : FactorData (pairI Z ZS g) (pairP Z ZS g) V Y
        (Additive (Quotient (Chapter15.setup Z Zperp Y T) g)),
      f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity ∧
      Nonempty (FactorModuleConclusion (pairI Z ZS g) (pairP Z ZS g) V Y
        (f.model.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (pairI Z ZS g))))
          f.representation) :=
  literal_common_data_of_factorExchange hZS hperp hspan d hΩ
    (literal_factorExchange a hTM hSyl hspan d)

/-- All five clauses of 15.3.54 on the original subgroup and quotient maps.
The quotient instances, factor data and common multiplicity are constructed;
only the genuine earlier Chapter 15 action and source hypotheses remain. -/
theorem literal_application
    {M Z ZS Zperp V Y T : Subgroup G} {g : G}
    (a : NaturalOrthogonalAction M V) (hTM : T ≤ M)
    (hSyl : ∃ P : Sylow 2 M, (P : Subgroup M).map M.subtype = T)
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS)
    (hspan : localSpan Z Y = V)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g)
    (hΩ : omegaCenter T = Z) :
    letI := moduleSectionNormal d d.I_eq_LU
    letI := moduleSectionElementary d d.I_eq_LU d.S_normalizes_U d.S_eq_coreProduct
    ∃ f : FactorData (pairI Z ZS g) (pairP Z ZS g) V Y
        (Additive (Quotient (Chapter15.setup Z Zperp Y T) g)),
      f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity ∧
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
  let := moduleSectionNormal d d.I_eq_LU
  let := moduleSectionElementary d d.I_eq_LU d.S_normalizes_U d.S_eq_coreProduct
  obtain ⟨f, hsame, _⟩ := literal_common_data a hTM hSyl hZS hperp hspan d hΩ
  exact ⟨f, hsame,
    literal_application_of_common_multiplicity hZS hperp hspan d hΩ f hsame⟩

end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Multiplicity.Chapter15Exchange
