module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity.CanonicalModels
public import Theory.SpecificGroups.ThreeDivisibility.Classical
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder

/-!
# Excluding Suzuki from the complete central-component catalogue

Each actual component carrier listed in B.4.2 has order divisible by three.
This includes both small derived endpoints and the alternating quotients of
the exceptional central covers. The concrete Suzuki group has three-free
order, as does any quotient of it. Cardinality invariance therefore excludes
every entry, without assuming that a representation has trivial kernel.

The final theorem applies this exclusion to the central quotient of the
actual faithful image of a nontrivial quasisimple action. The classification
argument that would put that quotient in the catalogue remains upstream.

Source: Aschbacher--Smith, B.4.2, printed p.86, and 15.3.65, printed p.1152.
The Suzuki order formula is the checked Huppert--Blackburn III, XI.3.3
calculation imported by `Suzuki.TwoCoreExtensionOrder`.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity

open Subgroup Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups

/-- All entries have three-divisible order, including both derived endpoints. -/
theorem ComponentModel.three_dvd_card {S : Type*} [Group S]
    {family : Family} {q : ℕ} (h : ComponentModel S family q) : 3 ∣ Nat.card S := by
  cases h with
  | linearTwo F _ _ e =>
      rw [Nat.card_congr e.toEquiv]
      exact ProjectiveSpecialLinearGroup.three_dvd_card F 2 (by decide)
  | linearThree F _ _ e =>
      rw [Nat.card_congr e.toEquiv]
      exact ProjectiveSpecialLinearGroup.three_dvd_card F 3 (by decide)
  | symplecticFour F _ hF e =>
      rw [Nat.card_congr e.toEquiv]
      exact Theory.SpecificGroups.ThreeDivisibility.symplectic F hF
  | gTwo F _ _ e =>
      rw [Nat.card_congr e.toEquiv]
      exact Theory.SpecificGroups.ThreeDivisibility.g2 F
  | symplecticFourTwoDerived e =>
      rw [Nat.card_congr e.toEquiv,
        Nat.card_congr (derivedCongr
          (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := ZMod 2))).toEquiv]
      exact Theory.SpecificGroups.ThreeDivisibility.symplectic_derived
  | gTwoTwoDerived e =>
      rw [Nat.card_congr e.toEquiv]
      exact Theory.SpecificGroups.ThreeDivisibility.g2_derived
  | alternatingFive e =>
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      norm_num
  | alternatingSix e =>
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      norm_num
  | alternatingSeven e =>
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      norm_num
  | linearFourTwo e =>
      rw [Nat.card_congr e.toEquiv]
      exact ProjectiveSpecialLinearGroup.three_dvd_card (ZMod 2) 4 (by decide)
  | linearFiveTwo e =>
      rw [Nat.card_congr e.toEquiv]
      exact ProjectiveSpecialLinearGroup.three_dvd_card (ZMod 2) 5 (by decide)

/-- A central quotient identified with a Suzuki carrier cannot occur in the
catalogue. No assertion about the order of the central kernel is needed. -/
theorem not_componentModel_of_suzuki_equiv {S : Type*} [Group S]
    (m : ℕ) (hm : 0 < m) (e : S ≃* SuzukiMatrixGroup m) (family : Family) (q : ℕ) :
    ¬ ComponentModel S family q := by
  intro h
  apply suzukiMatrixGroup_three_free m hm
  simpa only [Nat.card_congr e.toEquiv] using h.three_dvd_card

/-- Even after taking the full center quotient, Suzuki cannot be any entry. -/
theorem suzuki_centralQuotient_not_componentModel
    (m : ℕ) (hm : 0 < m) (family : Family) (q : ℕ) :
    ¬ ComponentModel (SuzukiMatrixGroup m ⧸ center (SuzukiMatrixGroup m)) family q := by
  intro h
  exact suzukiMatrixGroup_three_free m hm
    (h.three_dvd_card.trans (center (SuzukiMatrixGroup m)).card_quotient_dvd_card)

/-- The section-image exclusion also applies to any quasisimple central
cover whose actual central quotient is identified with Suzuki. -/
theorem suzuki_actionImage_not_componentModel_of_central_quotient
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) [Theory.GroupTheory.IsQuasisimple D]
    (hn : ¬ ∀ g v, ρ g v = v) (m : ℕ) (hm : 0 < m)
    (e : D ⧸ center D ≃* SuzukiMatrixGroup m) (family : Family) (q : ℕ) :
    ¬ ComponentModel (Representation.BinaryOffender.actionImage ρ ⧸
      center (Representation.BinaryOffender.actionImage ρ)) family q := by
  intro h
  exact not_componentModel_of_suzuki_equiv m hm e family q
    (h.transport (actionImageCentralQuotientEquiv ρ hn))

/-- The exclusion for every nontrivial quasisimple section action with an
actual Suzuki model, retaining any central action kernel. -/
theorem suzuki_actionImage_not_componentModel
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) [Theory.GroupTheory.IsQuasisimple D]
    (hn : ¬ ∀ g v, ρ g v = v) (m : ℕ) (hm : 0 < m)
    (e : D ≃* SuzukiMatrixGroup m) (family : Family) (q : ℕ) :
    ¬ ComponentModel (Representation.BinaryOffender.actionImage ρ ⧸
      center (Representation.BinaryOffender.actionImage ρ)) family q := by
  rw [componentModel_actionImage_iff ρ hn e]
  exact suzuki_centralQuotient_not_componentModel m hm family q

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity
