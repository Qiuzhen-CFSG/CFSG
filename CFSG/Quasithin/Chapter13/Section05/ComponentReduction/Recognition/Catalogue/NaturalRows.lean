module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.BinaryModels
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.SymplecticTwo

/-!
# The natural component rows after the original source exclusions

The full B.4 catalogue retains actual intertwiners. Once the simple center
and the original moved-plane exclusions remove the binary linear and
exterior rows, only the natural A₆, A₈ and G₂(2)′ restrictions remain.
The small symplectic row is transported through its concrete natural A₆
coordinates, and the marked ambient rows retain their literal component.
Source: Aschbacher–Smith13.5.21, printed p.924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
open ChapterB.QuasisimpleSource

@[expose] def NaturalComponentRows {E W : Type*} [Group E] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) E W) (L : Subgroup E) : Prop :=
  Nonempty (ActionEquiv (ρ.comp L.subtype) (alternatingNatural 6)) ∨
  Nonempty (ActionEquiv (ρ.comp L.subtype) (alternatingNatural 8)) ∨
  Nonempty (ActionEquiv (ρ.comp L.subtype) (g2DerivedNatural (ZMod 2)))

private def quotientModel {L M : Type*} [Group L] [Group M]
    (e : L ≃* M) (hz : center M = ⊥) : (L ⧸ center L) ≃* M :=
  (Representation.TripleSixOuterDisplacement.centralQuotientEquiv e).trans
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot)

private theorem quadratic_of_marked {E W : Type*} [Group E] [Finite E]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) E W) (t : E) (ht : orderOf t = 2)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤ 2) : quadraticRatio ρ ≤ 2 := by
  obtain ⟨hA,hrank,hquad,_⟩ := involution_actor_rank_and_fixedCodim ρ t ht
  apply (quadraticRatio_le_two_iff ρ).mpr
  refine ⟨zpowers t,hA,hquad,?_⟩
  rw [hrank,fixedCodim_zpowers_eq_displacement_rank]
  exact hr

theorem natural_rows_of_chief_sieve {E W : Type*} [Group E] [Finite E]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) E W)
    (hyp : Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.B4Hypotheses
      KnownSimple.IsKnownSimple ρ)
    (c : ChiefSieve ρ)
    (unitary : ∀ (F : Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.BinaryField) (n : ℕ), 2 ≤ n → F.degree = 2*n →
      ∀ J : BenderSuzuki.MatrixGroups.HermitianForm 3 F.Carrier, ¬ UnitaryChiefAction ρ F J)
    (t : E) (ht : orderOf t = 2)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤ 2)
    (hz : center (generalizedFitting E) = ⊥)
    (not_linear : ∀ d, (d = 4 ∨ d = 5) → ¬ Nonempty (ActionEquiv
      (ρ.comp (generalizedFitting E).subtype) (linearNatural BinaryField.two d)))
    (not_ten : (E ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) →
      Module.finrank (ZMod 2) W ≠ 10) :
    NaturalComponentRows ρ (generalizedFitting E) := by
  have hq := quadratic_of_marked ρ t ht hr
  have hs := ChapterB.SmallRatioClassification.rankOne_source_of_b4_quadratic hyp hq
  have hspor : ∀ e : (generalizedFitting E ⧸ center (generalizedFitting E)) ≃* Sporadic.Mathieu.M22,
      False := by
    classical
    intro e
    exact ChapterB.SmallRatioClassification.sporadic_false_of_marked_involution hs
      (Or.inl ⟨.m22,(by intro he; cases he),⟨e⟩⟩) t ht (by
        rw [fixedCodim_zpowers_eq_displacement_rank]
        exact hr)
  rcases c.catalogue with h | h
  · cases h with
    | linearTwo F _ e _ _ => exact (c.not_linearTwo F ⟨e⟩).elim
    | linearThree F _ e _ => exact (c.not_linearThree F ⟨e⟩).elim
    | symplectic F large _ e _ => exact (c.not_symplectic F large ⟨e⟩).elim
    | symplecticTwo e _ => exact Or.inl ⟨ChapterB.QuasisimpleSource.ExtensionConsequences.SymplecticTwo.markedAlternatingActionEquiv e⟩
    | g2 F large _ e _ _ =>
      have hF : 2 < Nat.card F.Carrier := by
        rw [F.card_eq]
        have hh := Nat.pow_lt_pow_right (by decide : 1 < 2) large
        simpa using hh
      exact (ChapterB.SmallRatioClassification.g2_excluded_of_small_involution hs F large
        (quotientModel e.groupEquiv (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hF))
        t ht hr).elim
    | g2Two e _ _ => exact Or.inr (Or.inr ⟨ChapterB.QuasisimpleSource.ExtensionConsequences.markedRestriction e⟩)
    | symmetric n degree e _ _ =>
      rcases degree with rfl | rfl
      · exact (c.not_five ⟨e.subgroupEquiv⟩).elim
      · exact (c.not_seven ⟨e.subgroupEquiv⟩).elim
    | alternatingSix _ e _ _ => exact Or.inl ⟨e⟩
    | alternatingSeven _ _ e _ _ _ => exact (c.not_seven ⟨e⟩).elim
    | tripleSix _ a _ =>
      have hh := Nat.card_congr a.centerEquiv.toEquiv
      rw [hz] at hh
      norm_num at hh
    | binaryLinear d hd _ e _ => exact (not_linear d hd ⟨e⟩).elim
    | orthogonalSix _ _ e _ _ => exact Or.inr (Or.inl ⟨e⟩)
    | symmetricEight _ e _ => exact Or.inr (Or.inl ⟨ChapterB.QuasisimpleSource.ExtensionConsequences.markedRestriction e⟩)
    | exteriorFive _ whole e hd _ _ =>
      exact (not_ten (((MulEquiv.subgroupCongr whole).trans Subgroup.topEquiv).symm.trans e) hd).elim
  · cases h with
    | alternatingSeven e _ _ _ => exact (c.not_seven ⟨e.groupEquiv⟩).elim
    | orthogonal K F degree e _ _ _ _ => exact (c.not_orthogonal K F degree ⟨e⟩).elim
    | unitary F n large degree J _ e _ _ _ => exact (unitary F n large degree J ⟨e⟩).elim
    | suzuki k hk e _ _ _ => exact (c.not_suzuki k hk ⟨e⟩).elim
    | linearThree _ _ _ _ _ _ hbad _ => exact (not_lt_of_ge hq hbad).elim
    | g2Derived e _ _ _ => exact Or.inr (Or.inr ⟨⟨e.groupEquiv,e.linearEquiv,e.intertwines⟩⟩)
    | mathieuTwelve _ _ hbad _ => exact (not_lt_of_ge hq hbad).elim
    | tripleMathieuTwentyTwo _ e _ _ _ => exact (hspor e).elim
    | mathieuTwentyTwoCocode _ _ hbad _ => exact (not_lt_of_ge hq hbad).elim
    | mathieuTwentyTwoCode e _ _ _ =>
      exact (hspor (quotientModel e.groupEquiv Sporadic.Mathieu.m22_center_eq_bot)).elim
    | mathieuTwentyThreeCocode _ _ hbad _ => exact (not_lt_of_ge hq hbad).elim
    | mathieuTwentyThreeCode _ _ hbad _ => exact (not_lt_of_ge hq hbad).elim
    | mathieuTwentyFourCocode _ _ hbad _ => exact (not_lt_of_ge hq hbad).elim
    | mathieuTwentyFourCode _ _ hbad _ => exact (not_lt_of_ge hq hbad).elim

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
