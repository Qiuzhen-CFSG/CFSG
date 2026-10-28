module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FComparison
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.SourceQuotient

/-!
# Source classification comparison at the actual terminal quotient

The earlier terminal configuration supplies the Goldschmidt triple and
O_{3'}(H)=O₂(H). The literal offender-image containment and X_E outside M
supply a nontrivial offender subgroup, whose full-preimage SQTK cover and
faithful restricted action satisfy B.5.3. Applying the two complete universal
source implications now identifies the quotient and proves that its actual
offender subgroup is the entire quotient. The original B.5 module conclusion
is retained for downstream use.

The parent still constructs the action and discharges the universal source
inputs; this theorem adds no recognition, dimension or irreducibility premise.
Source: Aschbacher--Smith, combined manuscript of 1 March 2004, F.6.18,
B.5.1/B.5.6, and the repaired 15.3.68 argument, pp.1154--1155.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u v
variable {G : Type u} [Group G] [Finite G]

/-- Conditional recognition from the full universal source inputs at the
actual quotient H/O₂(H). All actual-action premises remain explicit. -/
theorem terminal_recognition_of_full_classifications {K : GroupClass.{u}}
    (sourceF : FSource.ClassificationInput K) (sourceB : GeneralClassificationInput.{u,v} K)
    (T : Sylow 2 G) (M Y V E F : Subgroup G)
    (d : OrthogonalFourBinary.NaturalAction V M)
    (c : TerminalConfiguration T M Y V E F d)
    (hH : IsSQTK K (amalgamGroup Y T E F)) (hTM : (T : Subgroup G) ≤ M)
    (hX : ¬ lineX E ≤ M)
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (ρ : Representation (ZMod 2)
      (amalgamGroup Y T E F ⧸ pCore 2 (amalgamGroup Y T E F)) W)
    (hfaith : Function.Injective ρ)
    (hXI : ((lineX E).subgroupOf (amalgamGroup Y T E F)).map
      (QuotientGroup.mk' (pCore 2 (amalgamGroup Y T E F))) ≤ offenderSubgroup ρ)
    (hr : primeRank 3 (amalgamGroup Y T E F ⧸ pCore 2 (amalgamGroup Y T E F)) ≤ 1) :
    SourceAlternative (ρ.comp (offenderSubgroup ρ).subtype) ∧
    offenderSubgroup ρ = ⊤ ∧
    Nonempty ((amalgamGroup Y T E F ⧸ pCore 2 (amalgamGroup Y T E F)) ≃* SL(3,ZMod 2)) := by
  obtain ⟨⟨cover⟩, triple, hyp, hi⟩ := terminal_classification_applicability
    T M Y V E F d c hH hTM hX ρ hfaith hXI
  exact (recognition_of_full_classifications sourceF sourceB _ _ triple cover ρ hyp hr hi
    (CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.coreQuotient_twoCore
      (H := amalgamGroup Y T E F))).2

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
