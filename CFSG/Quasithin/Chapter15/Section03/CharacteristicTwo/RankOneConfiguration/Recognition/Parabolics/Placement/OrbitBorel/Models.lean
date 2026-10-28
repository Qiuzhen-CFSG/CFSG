module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.Reduction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.Models.Quotients
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.Models.Intersection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.ModelComparison.Catalogue
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.ModelComparison.SourceTransport
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder

/-!
# The nonnormal component models and their actual quotient comparison

The genuine Thompson action satisfies B.5.3, so its complete B.5.6
classification supplies an FF model of the selected ordinary component.
The subnormal-core calculation in `Quotients` identifies its star image
with the intrinsic quotient L/O₂(L). Transporting the FF model through
this actual isomorphism permits the exhaustive comparison with 1.2.1(3)
proved in `Intersection`.

The result gives matching PSL₂(2^n), n ≥ 2, or PSL₃(2) models for both
quotients. All exceptional alternatives are treated by the imported
catalogue and intersection proofs; no field-degree parity is imposed.
Only the precise universal earlier orbit and FF classification implications
remain explicit. The source-facing companion also retains the complete
FF hypothesis and its nontrivial witness on the same Thompson action.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 1.2.1(3),
printed pp.503–504; B.5.3/6, pp.104–105; proof of 15.3.27, p.1130.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel
open Chapter1.Section02
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u
variable {G : Type u} [Group G] [Finite G]

/-- A binary PSL₂ intrinsic quotient supplies both actual models in the
first source alternative, with precisely the same field degree. -/
theorem componentModelAlternatives_of_linear_even (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hZS : d.Z ≤ d.S)
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSL (c.L ⧸ pCore 2 c.L) 2 (2 ^ n)) :
    ComponentModelAlternatives d c := by
  let e := nonnormalComponentQuotientEquivStar d c hS hZS (.linear_even n hn hm)
  exact Or.inl ⟨n, hn, hm, hm.of_mulEquiv e.symm⟩

/-- Positive three-rank excludes the Suzuki quotient in the complete
nonnormal list. No FF-model exclusion is assumed. -/
theorem component_quotient_not_suzuki (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) {m : ℕ} (hm : 1 ≤ m) :
    ¬ Nonempty ((c.L ⧸ pCore 2 c.L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  rintro ⟨e⟩
  have hd := component_three_divides_quotient d c
  rw [Nat.card_congr e.toEquiv] at hd
  exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega) hd

/-- The same divisibility holds for the actual Thompson component after
the source nonnormal list supplies its quotient comparison. -/
theorem component_star_three_divides (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hZS : d.Z ≤ d.S)
    (hm : NonnormalCComponentModel (c.L ⧸ pCore 2 c.L)) :
    3 ∣ Nat.card (d.starImage I c.L) := by
  rw [← Nat.card_congr (nonnormalComponentQuotientEquivStar d c hS hZS hm).toEquiv]
  exact component_three_divides_quotient d c

/-- An intrinsic surviving model gives matching models of both quotient
conventions. The model-intersection proof must supply the displayed premise. -/
theorem componentModelAlternatives_of_intrinsic_models (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hZS : d.Z ≤ d.S)
    (hm : NonnormalCComponentModel (c.L ⧸ pCore 2 c.L))
    (hmodel : (∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSL (c.L ⧸ pCore 2 c.L) 2 (2 ^ n)) ∨
      ClassicalGroup.IsPSL (c.L ⧸ pCore 2 c.L) 3 2) :
    ComponentModelAlternatives d c := by
  rcases hmodel with ⟨n, hn, hlin⟩ | hlin
  · exact componentModelAlternatives_of_linear_even d c hS hZS hn hlin
  · let e := nonnormalComponentQuotientEquivStar d c hS hZS hm
    exact Or.inr ⟨hlin, hlin.of_mulEquiv e.symm⟩

/-- Prune only proved cases of 1.2.1(3). The odd-prime and J₁ cases remain
explicit with actual isomorphisms for both the intrinsic and star quotients.
Their intersection with B.5.6 is used in `componentModelAlternatives_of_ambient`. -/
theorem componentModelAlternatives_or_prime_or_janko {K : GroupClass.{u}}
    (earlier : EarlierOrbitResults K) (hG : IsSimpleQTKE K G)
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (hn : ¬ (c.L.subgroupOf I).Normal)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hZS : d.Z ≤ d.S) :
    ComponentModelAlternatives d c ∨
      (∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (c.L ⧸ pCore 2 c.L) 2 p ∧
        ClassicalGroup.IsPSL (d.starImage I c.L) 2 p) ∨
      (Nonempty ((c.L ⧸ pCore 2 c.L) ≃* Janko1.Model) ∧
        Nonempty (d.starImage I c.L ≃* Janko1.Model)) := by
  have hm := (component_orbit_index_and_model earlier hG d hI c hn).2
  let e := nonnormalComponentQuotientEquivStar d c hS hZS hm
  cases hm with
  | linear_even n hn hm =>
    exact Or.inl (componentModelAlternatives_of_linear_even d c hS hZS hn hm)
  | suzuki m hm iso => exact (component_quotient_not_suzuki d c hm iso).elim
  | linear_prime p hp ho iso =>
    exact Or.inr (Or.inl ⟨p, hp, ho, iso, iso.of_mulEquiv e.symm⟩)
  | janko iso => exact Or.inr (Or.inr ⟨iso, iso.map (e.symm.trans ·)⟩)

/-- Extract the selected component's actual FF model from the complete
classification of the Thompson action. The actor itself need not be perfect. -/
theorem component_star_ff_model_of_ambient {K : GroupClass.{u}}
    (classification : FFAlternatives.CompleteClassificationInput.{u,u} K)
    (hG : IsSimpleQTKE K G) (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hVT : d.V ≤ (d.T : Subgroup G)) :
    FFAlternatives.QuasisimpleModel (d.starImage I c.L) := by
  let _ := d.UI_subgroupOf_elementary hS (d.Z_le_S hVT) hf
  have hsource := thompson_classification_of_ambient classification hG d hI hf hS hVT
  have hmodel := ModelComparison.Catalogue.component_model_of_source_alternative
    _ hsource (ModelComparison.component_star_isComponent d c)
  exact ModelComparison.Catalogue.quasisimpleModel_of_equiv
    (ModelComparison.componentThompsonEquiv d c).symm hmodel

/-- The model comparison in the first paragraph of 15.3.27: relative
nonnormality and the actual Thompson classification give matching binary
PSL₂ or PSL₃(2) models for L/O₂(L) and L*. The preliminary Sylow and module
containments are explicit; no specialized component sieve is assumed. -/
theorem componentModelAlternatives_of_ambient {K : GroupClass.{u}}
    (earlier : EarlierOrbitResults K)
    (classification : FFAlternatives.CompleteClassificationInput.{u,u} K)
    (hG : IsSimpleQTKE K G) (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (hn : ¬ (c.L.subgroupOf I).Normal)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hVT : d.V ≤ (d.T : Subgroup G)) :
    ComponentModelAlternatives d c := by
  have hm := (component_orbit_index_and_model earlier hG d hI c hn).2
  have hstar := component_star_ff_model_of_ambient classification hG d hI hf c hS hVT
  have hquot := ModelComparison.Catalogue.quasisimpleModel_of_equiv
    (nonnormalComponentQuotientEquivStar d c hS (d.Z_le_S hVT) hm) hstar
  let _ := c.core_quotient_quasisimple
  exact componentModelAlternatives_of_intrinsic_models d c hS (d.Z_le_S hVT) hm
    (intrinsic_model_intersection hm hquot (component_three_divides_quotient d c))

/-- Keep the model comparison together with every B.5.3 hypothesis and
the nontrivial FF witness on the actual Thompson representation. The earlier
centralizer containment is needed for that witness, not for the comparison. -/
theorem componentModelAlternatives_and_ff_of_ambient {K : GroupClass.{u}}
    (earlier : EarlierOrbitResults K)
    (classification : FFAlternatives.CompleteClassificationInput.{u,u} K)
    (hG : IsSimpleQTKE K G) (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I) (hn : ¬ (c.L.subgroupOf I).Normal)
    (hS : Chapter1.IsSylowIn 2 d.S I) (hVT : d.V ≤ (d.T : Subgroup G))
    (hC : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I) :
    let _ := d.UI_subgroupOf_elementary hS (d.Z_le_S hVT) hf
    let ρ := d.thompsonStarAction I ((d.Z_le_S hVT).trans (le_sup_right.trans hI.1.2))
    FFHypothesis K ρ ∧ Representation.BinaryOffender.IsFFModule ρ ∧
      ComponentModelAlternatives d c := by
  let _ := d.UI_subgroupOf_elementary hS (d.Z_le_S hVT) hf
  obtain ⟨hsource, hff⟩ := thompson_ff_of_ambient hG d hI hf c hS hVT hC
  exact ⟨hsource, hff,
    componentModelAlternatives_of_ambient earlier classification hG d hI hf c hn hS hVT⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel
