module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.AdequateRankOne.Alternatives
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

/-!
# Adequate classification on the literal terminal offender action

Apply the corrected adequate B.5 theorem only to the actual offender
subgroup. Its inherited three-rank bound excludes the two corrected cases,
so the full F.6.18 comparison and existing Fano marking apply unchanged.
No universal implication to the legacy classifier is asserted.

Source: Aschbacher–Smith, the repaired 15.3.68 argument, pp.1154–1155.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.AdequateRankOne
open Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u v
section Quotient
variable {D : Type u} [Group D] [Finite D]

/-- The exhaustive F.6.18 comparison uses the adequate B.5 implication
on this actual rank-one offender action, retaining its full conclusion. -/
theorem recognition_of_adequate_classifications {K : GroupClass.{u}}
    (sourceF : FSource.ClassificationInput K) (sourceB : ProjectiveLine.AdequateGeneralClassificationInput.{u,v} K)
    (G₁ G₂ : Subgroup D) (triple : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (cover : ThreePrimeSQTKQuotient K D)
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)
    (hyp : FFHypothesis K (ρ.comp (offenderSubgroup ρ).subtype))
    (hr : primeRank 3 D ≤ 1) (hne : offenderSubgroup ρ ≠ ⊥)
    (hcore : pCore 2 D = ⊥) :
    (∃ S : Sylow 2 D, G₁ ⊓ G₂ = (S : Subgroup D) ∧
      (FSource.Alternative G₁ G₂ S ∨ FSource.Alternative G₂ G₁ S)) ∧
    SourceAlternative (ρ.comp (offenderSubgroup ρ).subtype) ∧
    offenderSubgroup ρ = ⊤ ∧ Nonempty (D ≃* SL(3,ZMod 2)) := by
  obtain ⟨S, hS, hf⟩ := sourceF D G₁ G₂ triple cover
  have hb := sourceAlternative_of_adequate_rank_one _
    ((primeRank_le_of_injective 3 (offenderSubgroup ρ).subtype
      Subtype.val_injective).trans hr) (sourceB _ _ _ hyp)
  refine ⟨⟨S, hS, hf⟩, hb, ?_⟩
  rcases hf with hf | hf
  · exact full_classification_comparison ρ hr hne hcore hf hb
  · exact full_classification_comparison ρ hr hne hcore hf hb

end Quotient

section Terminal
variable {G : Type u} [Group G] [Finite G]

/-- Apply both source implications to the original terminal quotient. -/
theorem terminal_recognition_of_adequate_classifications {K : GroupClass.{u}}
    (sourceF : FSource.ClassificationInput K) (sourceB : ProjectiveLine.AdequateGeneralClassificationInput.{u,v} K)
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
  exact (recognition_of_adequate_classifications sourceF sourceB _ _ triple cover ρ hyp hr hi
    (CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.coreQuotient_twoCore
      (H := amalgamGroup Y T E F))).2

/-- The original Sylow, parabolics and faithful action share one natural marking. -/
theorem terminal_natural_of_adequate_classifications {K : GroupClass}
    (sourceF : FSource.ClassificationInput K) (sourceB : ProjectiveLine.AdequateGeneralClassificationInput.{u,u} K)
    (T : Sylow 2 G) (M Y V E F W : Subgroup G) [IsElementaryAbelian 2 W]
    (d : OrthogonalFourBinary.NaturalAction V M)
    (c : TerminalConfiguration T M Y V E F d)
    (hH : IsSQTK K (amalgamGroup Y T E F)) (hTM : (T : Subgroup G) ≤ M)
    (hX : ¬ lineX E ≤ M)
    (hZE : centralInvolutions T ≤ E) (hZ : Nat.card (centralInvolutions T) = 2)
    (hspan : W = conjugateSpanBy (centralInvolutions T) (amalgamGroup Y T E F))
    (ρ : Representation (ZMod 2)
      (amalgamGroup Y T E F ⧸ pCore 2 (amalgamGroup Y T E F)) (Additive W))
    (hfaith : Function.Injective ρ)
    (hconj : ∀ (h : amalgamGroup Y T E F) (w : Additive W),
      ((ρ (QuotientGroup.mk' _ h) w).toMul : G) = (h : G) * (w.toMul : G) * (h : G)⁻¹)
    (hXI : ((lineX E).subgroupOf (amalgamGroup Y T E F)).map
      (QuotientGroup.mk' (pCore 2 (amalgamGroup Y T E F))) ≤ offenderSubgroup ρ)
    (hr : primeRank 3 (amalgamGroup Y T E F ⧸ pCore 2 (amalgamGroup Y T E F)) ≤ 1) :
    SourceAlternative (ρ.comp (offenderSubgroup ρ).subtype) ∧ offenderSubgroup ρ = ⊤ ∧
    ∃ m : (amalgamGroup Y T E F ⧸ pCore 2 (amalgamGroup Y T E F)) ≃* Matrix.PSL3Two.SL,
      ((lineT T E).subgroupOf (amalgamGroup Y T E F)).map
        (m.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.borelSL ∧
      ((firstAmalgamGroup Y T E F).subgroupOf (amalgamGroup Y T E F)).map
        (m.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.lineParabolicSL ∧
      ((secondAmalgamGroup T E).subgroupOf (amalgamGroup Y T E F)).map
        (m.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.pointParabolicSL ∧
      Nonempty (ρ.Equiv (BinaryLinearThree.W.comp m.toMonoidHom)) ∧
      ∀ z : Additive W, z ≠ 0 → Nat.card (Set.range (fun g => ρ g z)) = 7 := by
  obtain ⟨hb, hi, ⟨e⟩⟩ := terminal_recognition_of_adequate_classifications (G := G) (W := Additive ↥W) sourceF sourceB
    T M Y V E F d c hH hTM hX ρ hfaith hXI hr
  obtain ⟨m, hS, h₁, h₂, ⟨a⟩⟩ := terminal_natural_of_recognition
    T M Y V E F W d c hZE hZ hspan ρ hfaith hconj (e.trans Matrix.PSL3Two.equiv)
  exact ⟨hb, hi, m, hS, h₁, h₂, ⟨a⟩, fun z hz => quotient_natural_orbit_card ρ m a z hz⟩

end Terminal
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.AdequateRankOne
