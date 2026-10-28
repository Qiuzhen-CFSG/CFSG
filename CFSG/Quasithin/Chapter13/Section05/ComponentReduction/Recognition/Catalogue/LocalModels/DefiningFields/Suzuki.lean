module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.FullCatalogue
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
public import Theory.GroupTheory.ConjugatePairsThreeDivisibility
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder


/-!
# Excluding the Suzuki row in the original 13.5.21 configuration

Condition (iv) and relative Baer–Suzuki force three to divide |K̂|.
Transporting this divisibility through K̂ ≃ L/Z(L) to the actual component
L of the chief action contradicts the concrete Suzuki order formula.
The order-two actor need not be assumed inner, or assumed to be a root
element. Thus this row is excluded before any such marking is required.

The comparison is with the central quotient of the chief component;
L and K̂ are not identified. The original Selected D K, the quotient
X/C_X(K*), the actual marked subgroup V̂, and the exact S₃ pair condition
are retained. The configuration and faithful-chief comparison are explicit
producer inputs. This module proves the Suzuki row only; the other
larger-field exclusions remain separate obligations.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Table B.4.5, printed p.87, and 13.5.21, pp.923–924 (PDF pp.940–941).
The shorter exclusion uses the source Baer–Suzuki criterion A.1.2.
-/

public section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels.DefiningFields
open Configuration
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open Chapter13.Section08.Components

variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {K : Subgroup G}
  (s : Selected D K) (h : D.Hypothesis) [(componentCentralizer s h).Normal]

/-- Condition (iv) forces three to divide the actual simple component K̂.
Perfectness is inherited from the selected original component. -/
theorem source_three_dvd_Khat
    (hF : generalizedFitting (Xhat s h) = Khat s h)
    (hcard : Nat.card (Vhat s h) = 2) (hiv : PairCondition s h) :
    3 ∣ Nat.card (Khat s h) := by
  let : (Khat s h).Normal := hF ▸ inferInstance
  let := Khat_simple s h
  let := Khat_perfect s h
  have hc : centralizer (Khat s h : Set (Xhat s h)) = ⊥ := by
    let : IsSimpleGroup (generalizedFitting (Xhat s h)) := hF.symm ▸ Khat_simple s h
    let : Group.IsPerfect (generalizedFitting (Xhat s h)) := hF.symm ▸ Khat_perfect s h
    simpa only [hF] using SimpleSocle.centralizer_eq_bot
      (Group.IsPerfect.not_isMulCommutative (generalizedFitting (Xhat s h)))
  exact three_dvd_card_of_symmetricThree_pairs (Khat s h) (Vhat s h) hc hcard hiv

/-- Lift the divisibility across the actual central-quotient comparison with
the component of a faithful chief action; do not identify L with L/Z(L). -/
theorem source_three_dvd_chief_component
    (hF : generalizedFitting (Xhat s h) = Khat s h)
    (hcard : Nat.card (Vhat s h) = 2) (hiv : PairCondition s h)
    {E : Type*} [Group E] [Finite E] (L : Subgroup E)
    (comparison : Khat s h ≃* (L ⧸ center L)) : 3 ∣ Nat.card L := by
  have hd := source_three_dvd_Khat s h hF hcard hiv
  rw [Nat.card_congr comparison.toEquiv] at hd
  exact hd.trans (center L).card_quotient_dvd_card

/-- Exclude the actual action in Table B.4.5's Suzuki constructor.
The field and action use exactly the table's parameter and intertwiner. -/
theorem source_not_suzuki_action
    (hF : generalizedFitting (Xhat s h) = Khat s h)
    (hcard : Nat.card (Vhat s h) = 2) (hiv : PairCondition s h)
    {E W : Type*} [Group E] [Finite E] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W) (L : Subgroup E)
    (comparison : Khat s h ≃* (L ⧸ center L)) (k : ℕ) (hk : 0 < k) :
    ¬ Nonempty (ActionEquiv (ρ.comp L.subtype) (Suzuki.natural k)) := by
  rintro ⟨action⟩
  have hd := source_three_dvd_chief_component s h hF hcard hiv L comparison
  rw [Nat.card_congr action.groupEquiv.toEquiv] at hd
  exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free k hk hd

/-- Literal source application: the configuration supplies the fitting
identity, order-two marking and condition (iv). Only the faithful chief
component comparison remains with its producer. -/
theorem source_not_suzuki_of_configuration
    (Y : Subgroup G) (hY : Y ≤ D.L₁) (c : SourceConfiguration s h Y hY)
    {E W : Type*} [Group E] [Finite E] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) E W)
    (comparison : Khat s h ≃* ((generalizedFitting E) ⧸ center (generalizedFitting E)))
    (k : ℕ) (hk : 0 < k) :
    ¬ Nonempty (ActionEquiv (ρ.comp (generalizedFitting E).subtype) (Suzuki.natural k)) :=
  source_not_suzuki_action s h c.proved_prefix.khat_fitting c.proved_prefix.actor_card
    c.condition_iv ρ (generalizedFitting E) comparison k hk

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels.DefiningFields
