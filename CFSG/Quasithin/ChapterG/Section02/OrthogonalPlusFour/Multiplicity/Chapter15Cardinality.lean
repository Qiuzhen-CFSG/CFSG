module

public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Multiplicity.Chapter15Exchange
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Orders of the actual plus-four section and the Chapter 15 two-core

The complementary natural sums compute the order of S/S₂ with both
multiplicities retained. In the literal Chapter 15 configuration the
proved Sylow-action interchange equates the multiplicities, and the
central collapse identifies S₂ with the natural group of order sixteen.
This gives the exact |P| = 2^(4s+4) used at the start of 15.3.56, with the
same decomposition and the same integer as the complete 15.3.54 output.

No equality of the two general G.2.6 multiplicities is asserted here.
The earlier compatible orthogonal action, local Sylow witness and source
markings remain genuine inputs of the Chapter 15 application.

Source: Aschbacher–Smith, G.2.6(5) and 15.3.54–56, printed pp.336,
1146–1147 (combined manuscript, 1 March 2004).
-/

@[expose] public noncomputable section
open Subgroup InvertedCubicTensor
open scoped Pointwise IsMulCommutative
open Representation.BinaryOffender Representation.BinaryQuadraticPair
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

section ModuleData
variable [((S₂ D g).subgroupOf (D.S g)).Normal]
  [IsElementaryAbelian 2 (Quotient D g)]

private theorem quotient_card_decomposition
    {ρ : Representation (ZMod 2) (S₃ × S₃) (Additive (Quotient D g))}
    (r : ProductDecomposition ρ) :
    Nat.card (Quotient D g) = 2 ^ (2 * r.leftMultiplicity + 2 * r.rightMultiplicity) := by
  have hd := Submodule.finrank_add_eq_of_isCompl r.complementary
  rw [r.finranks.1, r.finranks.2] at hd
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := Additive (Quotient D g))
  rw [Nat.card_zmod, ← hd] at hc
  exact hc

private theorem core_card_decomposition (d : Hypothesis D g)
    {ρ : Representation (ZMod 2) (S₃ × S₃) (Additive (Quotient D g))}
    (r : ProductDecomposition ρ) :
    Nat.card (D.S g) =
      2 ^ (2 * r.leftMultiplicity + 2 * r.rightMultiplicity) *
        Nat.card (S₂ D g) := by
  rw [card_eq_card_quotient_mul_card_subgroup ((S₂ D g).subgroupOf (D.S g)),
    Nat.card_congr (subgroupOfEquivOfLe d.normal_layers.2.1).toEquiv]
  exact congrArg (fun n => n * Nat.card (S₂ D g))
    (quotient_card_decomposition r)

/-- The order formula valid before comparing the two actual multiplicities.
It retains the genuine middle layer, which need not equal V_L in G.2.6. -/
theorem SourceModuleData.core_card {d : Hypothesis D g} (f : SourceModuleData d) :
    Nat.card (D.S g) =
      2 ^ (2 * f.decomposition.leftMultiplicity + 2 * f.decomposition.rightMultiplicity) *
        Nat.card (S₂ D g) := core_card_decomposition d f.decomposition

end ModuleData

private theorem natural_card (d : Hypothesis D g) : Nat.card D.VL = 2 ^ 4 := by
  rw [Nat.card_congr d.coordinates.toEquiv]
  change Nat.card (Fin 2 → Fin 2 → ZMod 2) = 2 ^ 4
  simp

namespace Multiplicity
open Chapter15Collapse Chapter15Assembly
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.Nonabelian

/-- The literal P has order 2^(4s+4) for the same common multiplicity as
its full factor-module conclusion. Neither the decomposition, its equality,
nor the factor interchange is supplied as a premise. -/
theorem literal_common_cardinality
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
      Nat.card (pairP Z ZS g) = 2 ^ (4 * f.decomposition.leftMultiplicity + 4) ∧
      Nonempty (FactorModuleConclusion (pairI Z ZS g) (pairP Z ZS g) V Y
        (f.model.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (pairI Z ZS g))))
          f.representation) := by
  let := moduleSectionNormal d d.I_eq_LU
  let := moduleSectionElementary d d.I_eq_LU d.S_normalizes_U d.S_eq_coreProduct
  obtain ⟨f, hsame, hf⟩ :=
    Chapter15Exchange.literal_common_data a hTM hSyl hZS hperp hspan d hΩ
  refine ⟨f, hsame, ?_, hf⟩
  have hΩD : omegaCenter (Chapter15.setup Z Zperp Y T).T ≤
      (Chapter15.setup Z Zperp Y T).VL := by
    change omegaCenter T ≤ (Chapter15.setup Z Zperp Y T).VL
    rw [hΩ]
    exact point_le_VL (Chapter15.setup Z Zperp Y T)
  have hc := (source_collapse d hΩD).2.2.2.2.2
  have horder := core_card_decomposition d f.decomposition
  have hmiddle := (congrArg (fun A : Subgroup G => Nat.card A) hc).trans (natural_card d)
  rw [hmiddle, ← hsame, ← pow_add] at horder
  have hexp : 2 * f.decomposition.leftMultiplicity + 2 * f.decomposition.leftMultiplicity + 4 =
      4 * f.decomposition.leftMultiplicity + 4 := by omega
  rw [hexp] at horder
  exact (congrArg (fun A : Subgroup G => Nat.card A)
    (Chapter15.S_eq (Y := Y) (T := T) g hZS hperp)).symm.trans horder

end Multiplicity
end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
