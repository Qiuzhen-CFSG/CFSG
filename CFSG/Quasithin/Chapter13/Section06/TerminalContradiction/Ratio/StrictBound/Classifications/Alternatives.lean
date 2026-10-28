module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Models
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource

/-!
# The competing group models in the terminal B.4 argument

We apply the complete B.4.2 and B.4.5 implications to the original action.
Every row with q > 2 is eliminated numerically, including both boundary
cases. Triviality of the component center excludes both triple covers.
The remaining alternatives below are conclusions of this reduction, not
assumptions replacing either source classification. Their nonisomorphism
with the three terminal components remains a separate group comparison.

The variable-field and fixed-group lists separate those comparisons. The
linear-three entry is SL₃, while the terminal model is PSL₃(4). Likewise
the fixed linear-four entry is SL₄(2), not PSL₃(4).

Source: Aschbacher–Smith, B.4.2 and B.4.5, printed pp.86–87; K.3.2–3,
pp.454–456; terminal §13.6, p.935 (1 March 2004 manuscript).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open BenderSuzuki.MatrixGroups
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
open CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource

namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Classifications

universe u v

/-- Variable-field actors still possible after the numerical B.4 sieve. -/
inductive ClassicalCompetitor (L : Type u) [Group L] : Prop
  | linearTwo (F : BinaryField) (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier)
  | linearThree (F : BinaryField) (e : L ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier)
  | symplectic (F : BinaryField) (large : 1 < F.degree)
      (e : L ≃* Matrix.symplecticGroup (Fin 2) F.Carrier)
  | g2 (F : BinaryField) (large : 1 < F.degree) (e : L ≃* Atlas.G2.Model F.Carrier)
  | orthogonal (K F : BinaryField) (degree : F.degree = 2 * K.degree)
      (e : L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F.Carrier)
  | unitary (F : BinaryField) (n : ℕ) (large : 2 ≤ n) (degree : F.degree = 2 * n)
      (J : HermitianForm 3 F.Carrier) (conjugation : ∀ x, J.conj x = x ^ (2 ^ n))
      (e : L ≃* J.specialSubgroup)
  | suzuki (k : ℕ) (positive : 0 < k) (e : L ≃* SuzukiMatrixGroup k)

/-- Fixed actors still possible after the numerical B.4 sieve. -/
inductive FixedCompetitor (L : Type u) [Group L] : Prop
  | alternatingSix (e : L ≃* alternatingGroup (Fin 6))
  | alternatingSeven (e : L ≃* alternatingGroup (Fin 7))
  | linearFourTwo (e : L ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
  | linearFiveTwo (e : L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
  | g2DerivedTwo (e : L ≃* commutator (Atlas.G2.Model (ZMod 2)))
  | mathieuTwentyTwo (e : L ≃* Sporadic.Mathieu.M22)

/-- Transport uses a group equivalence, not a family tag. -/
theorem ClassicalCompetitor.transport {L M : Type*} [Group L] [Group M]
    (e : L ≃* M) (h : ClassicalCompetitor L) : ClassicalCompetitor M := by
  cases h with
  | linearTwo F f => exact .linearTwo F (e.symm.trans f)
  | linearThree F f => exact .linearThree F (e.symm.trans f)
  | symplectic F hn f => exact .symplectic F hn (e.symm.trans f)
  | g2 F hn f => exact .g2 F hn (e.symm.trans f)
  | orthogonal K F hd f => exact .orthogonal K F hd (e.symm.trans f)
  | unitary F n hn hd J hc f => exact .unitary F n hn hd J hc (e.symm.trans f)
  | suzuki k hk f => exact .suzuki k hk (e.symm.trans f)

/-- Transport of the fixed alternatives, including the actual SL₄(2) model. -/
theorem FixedCompetitor.transport {L M : Type*} [Group L] [Group M]
    (e : L ≃* M) (h : FixedCompetitor L) : FixedCompetitor M := by
  cases h with
  | alternatingSix f => exact .alternatingSix (e.symm.trans f)
  | alternatingSeven f => exact .alternatingSeven (e.symm.trans f)
  | linearFourTwo f => exact .linearFourTwo (e.symm.trans f)
  | linearFiveTwo f => exact .linearFiveTwo (e.symm.trans f)
  | g2DerivedTwo f => exact .g2DerivedTwo (e.symm.trans f)
  | mathieuTwentyTwo f => exact .mathieuTwentyTwo (e.symm.trans f)

private theorem no_triple_center {L : Type*} [Group L]
    (hz : center L = ⊥) (e : center L ≃* Multiplicative (ZMod 3)) : False := by
  have hc := Nat.card_congr e.toEquiv
  rw [hz] at hc
  norm_num at hc

variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) D V)

/-- Every B.4.2 action alternative contributes its actual component actor;
the triple cover is impossible when the component center is trivial. -/
theorem competitors_of_B42 {L H : Subgroup D} (hz : center L = ⊥)
    (h : IrreducibleActionCase σ L H) : ClassicalCompetitor L ∨ FixedCompetitor L := by
  cases h with
  | linearTwo F _ e _ _ => exact .inl (.linearTwo F e.groupEquiv)
  | linearThree F _ e _ => exact .inl (.linearThree F e.groupEquiv)
  | symplectic F hn _ e _ => exact .inl (.symplectic F hn e.groupEquiv)
  | symplecticTwo e _ =>
    exact .inr (.alternatingSix (e.subgroupEquiv.trans binarySymplecticDerivedEquiv))
  | g2 F hn _ e _ _ => exact .inl (.g2 F hn e.groupEquiv)
  | g2Two e _ _ => exact .inr (.g2DerivedTwo e.subgroupEquiv)
  | symmetric n hn e _ _ =>
    rcases hn with rfl | rfl
    · exact .inl (.linearTwo BinaryField.four (e.subgroupEquiv.trans alternatingFiveLinearEquiv))
    · exact .inr (.alternatingSeven e.subgroupEquiv)
  | alternatingSix _ e _ _ => exact .inr (.alternatingSix e.groupEquiv)
  | alternatingSeven _ _ e _ _ _ => exact .inr (.alternatingSeven e)
  | tripleSix _ h _ => exact (no_triple_center hz h.centerEquiv).elim
  | binaryLinear d hd _ e _ =>
    rcases hd with rfl | rfl
    · exact .inr (.linearFourTwo e.groupEquiv)
    · exact .inr (.linearFiveTwo e.groupEquiv)
  | orthogonalSix _ _ e _ _ =>
    exact .inr (.linearFourTwo (e.groupEquiv.trans alternatingEightLinearEquiv))
  | symmetricEight _ e _ =>
    exact .inr (.linearFourTwo (e.subgroupEquiv.trans alternatingEightLinearEquiv))
  | exteriorFive _ _ e _ _ _ => exact .inr (.linearFiveTwo e)

/-- Numerical elimination of all strict rows of Table B.4.5. The M₂₂ code
row has only q ≥ 2, so it remains in the output and needs a group comparison. -/
theorem competitors_of_table {L : Subgroup D} (hz : center L = ⊥)
    (h : TableB45 σ L) (hq : quadraticRatio σ ≤ 2) :
    ClassicalCompetitor L ∨ FixedCompetitor L := by
  cases h with
  | alternatingSeven e _ _ _ => exact .inr (.alternatingSeven e.groupEquiv)
  | orthogonal K F hd e _ _ _ _ => exact .inl (.orthogonal K F hd e)
  | unitary F n hn hd J hc e _ _ _ => exact .inl (.unitary F n hn hd J hc e.groupEquiv)
  | suzuki k hk e _ _ _ => exact .inl (.suzuki k hk e.groupEquiv)
  | linearThree _ _ _ _ _ _ hgt _ => exact (not_lt_of_ge hq hgt).elim
  | g2Derived e _ _ _ => exact .inr (.g2DerivedTwo e.groupEquiv)
  | mathieuTwelve _ _ hgt _ => exact (not_lt_of_ge hq hgt).elim
  | tripleMathieuTwentyTwo e _ _ _ _ => exact (no_triple_center hz e).elim
  | mathieuTwentyTwoCocode _ _ hgt _ => exact (not_lt_of_ge hq hgt).elim
  | mathieuTwentyTwoCode e _ _ _ => exact .inr (.mathieuTwentyTwo e.groupEquiv)
  | mathieuTwentyThreeCocode _ _ hgt _ => exact (not_lt_of_ge hq hgt).elim
  | mathieuTwentyThreeCode _ _ hgt _ => exact (not_lt_of_ge hq hgt).elim
  | mathieuTwentyFourCocode _ _ hgt _ => exact (not_lt_of_ge hq hgt).elim
  | mathieuTwentyFourCode _ _ hgt _ => exact (not_lt_of_ge hq hgt).elim

/-- The complete, unfiltered earlier classifications imply this group
comparison problem. The best offender in case (i) is constructed on σ. -/
theorem competitors_of_small_ratio [Finite D] [Finite V]
    {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦) (hB45 : FullB45.{u,v} 𝒦)
    (hyp : B4Hypotheses 𝒦 σ) (hz : center (generalizedFitting D) = ⊥)
    (hq : quadraticRatio σ ≤ 2) :
    ClassicalCompetitor (generalizedFitting D) ∨ FixedCompetitor (generalizedFitting D) := by
  cases hB45 D V σ (hyp.with_quadratic_bound hq) with
  | ff hc =>
    obtain ⟨A, hA⟩ := hyp.exists_B42_of_cubic_le_one hc
    exact competitors_of_B42 σ hz (hB42 D V σ A hA)
  | table _ _ row => exact competitors_of_table σ hz row hq
  | boundary _ hgt _ => exact (not_lt_of_ge hq hgt).elim

open Section08

/-- Apply the reduction through the literal component-to-residual equivalence.
The exceptional marking comes from the complete 13.6.27 source output.
Eliminating the two resulting competitor lists still requires model comparisons. -/
theorem source_competitors_of_small_ratio [Finite D] [Finite V]
    {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦) (hB45 : FullB45.{u,v} 𝒦)
    (hyp : B4Hypotheses 𝒦 σ) (hz : center (generalizedFitting D) = ⊥)
    {G : Type*} [Group G] [Finite G] (H : Subgroup G) (S : Subgroup H)
    (hs : Components.Conclusion S)
    (e : generalizedFitting D ≃* Source.starImage H (terminalResidual H))
    (hq : quadraticRatio σ ≤ 2) :
    ExceptionalModel (Source.starImage H (terminalResidual H)) ∧
      (ClassicalCompetitor (Source.starImage H (terminalResidual H)) ∨
        FixedCompetitor (Source.starImage H (terminalResidual H))) := by
  refine ⟨(residual_model_of_source H S hs).2, ?_⟩
  rcases competitors_of_small_ratio σ hB42 hB45 hyp hz hq with hc | hf
  · exact .inl (hc.transport e)
  · exact .inr (hf.transport e)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Classifications
