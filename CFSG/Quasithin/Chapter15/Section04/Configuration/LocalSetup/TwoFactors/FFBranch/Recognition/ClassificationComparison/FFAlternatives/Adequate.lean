module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.ProductCore
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.QuasisimpleCore
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.OuterShape
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.SourceAlternatives
public import Theory.SpecificGroups.FFG2DerivedCenter

/-!
# The adequate B.5.6 alternatives

The printed outer alternative in B.5.6(4) has a group configuration and a
separate representation conclusion.  The latter is not available in every
source consumer: in particular, the rank-five fixed-space splitting is not a
source hypothesis.  This file exposes the group configuration as an adequate
alternative while retaining every other B.5.6 conclusion verbatim.

The outer constructor stores the actual `ChapterB.OuterSixThreeShape D` on the
same actor `D`; it does not replace it by an isomorphic copy and it does not
assert a converse to `SourceAlternative`.  The old full interface remains
available in `SourceAlternatives`.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), B.5.3 and
B.5.6--B.5.7, printed pp.104--106.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- The nonquasisimple adequate alternatives.  Only the outer branch is
weakened; all other branches retain their complete source records. -/
inductive AdequateNonQuasisimpleAlternative : Prop
  | symmetricThree (case : SymmetricThreeCase ρ)
  | twoFactors (case : SourceTwoFactorCase ρ)
  | outerSixThree (shape : ChapterB.OuterSixThreeShape D)
  | hyperplane (case : HyperplaneCase ρ)

/-- The source alternatives with the actual group-only outer configuration. -/
inductive AdequateSourceAlternative : Prop
  | trivial (actor : Subsingleton D)
  | quasisimple (quasisimple : IsQuasisimple (generalizedFitting D))
      (actions : QuasisimpleSourceConclusion ρ (generalizedFitting D))
  | symmetricThree (case : SymmetricThreeCase ρ)
  | twoFactors (case : SourceTwoFactorCase ρ)
  | outerSixThree (shape : ChapterB.OuterSixThreeShape D)
  | hyperplane (case : HyperplaneCase ρ)

/-- The old full source theorem implies the adequate interface by forgetting
only the four outer representation fields. -/
theorem SourceAlternative.toAdequate (h : SourceAlternative ρ) :
    AdequateSourceAlternative ρ := by
  cases h with
  | trivial h => exact .trivial h
  | quasisimple hq ha => exact .quasisimple hq ha
  | symmetricThree h => exact .symmetricThree h
  | twoFactors h => exact .twoFactors h
  | outerSixThree h => exact .outerSixThree h.toGroupShape
  | hyperplane h => exact .hyperplane h

/-- Extract the group cases needed by consumers. -/
theorem AdequateSourceAlternative.groupCases (h : AdequateSourceAlternative ρ) :
    Subsingleton D ∨
      (IsQuasisimple (generalizedFitting D) ∧ QuasisimpleModel (generalizedFitting D)) ∨
      AdequateNonQuasisimpleAlternative ρ := by
  cases h with
  | trivial h => exact Or.inl h
  | quasisimple hq ha => exact Or.inr (Or.inl ⟨hq, ha.fittingModel ρ⟩)
  | symmetricThree h => exact Or.inr (Or.inr (.symmetricThree h))
  | twoFactors h => exact Or.inr (Or.inr (.twoFactors h))
  | outerSixThree h => exact Or.inr (Or.inr (.outerSixThree h))
  | hyperplane h => exact Or.inr (Or.inr (.hyperplane h))

/-- An FF witness removes the degenerate adequate actor. -/
theorem AdequateSourceAlternative.groupCases_of_ff
    (h : AdequateSourceAlternative ρ) (hff : IsFFModule ρ) :
    (IsQuasisimple (generalizedFitting D) ∧ QuasisimpleModel (generalizedFitting D)) ∨
      AdequateNonQuasisimpleAlternative ρ := by
  rcases h.groupCases ρ with ht | h
  · let : Subsingleton D := ht
    let : Nontrivial D := nontrivial_of_ff ρ hff
    obtain ⟨g, hg⟩ := exists_ne (1 : D)
    exact (hg (Subsingleton.elim _ _)).elim
  · exact h

/-- Universal adequate B.5.6 input for a fixed source class. -/
def AdequateGeneralClassificationInput (K : GroupClass.{u}) : Prop :=
  ∀ (D : Type u) [Group D] [Finite D]
    (V : Type v) [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V),
    FFHypothesis K ρ → AdequateSourceAlternative ρ

/-- The quasisimple and adequate-general source implications. -/
structure AdequateCompleteClassificationInput (K : GroupClass.{u}) : Prop where
  quasisimple : QuasisimpleClassificationInput.{u,v} K
  general : AdequateGeneralClassificationInput.{u,v} K

theorem AdequateCompleteClassificationInput.groupCases [Finite D]
    {K : GroupClass.{u}} (h : AdequateCompleteClassificationInput.{u,v} K)
    (hyp : FFHypothesis K ρ) :
    Subsingleton D ∨
      (IsQuasisimple (generalizedFitting D) ∧ QuasisimpleModel (generalizedFitting D)) ∨
      AdequateNonQuasisimpleAlternative ρ :=
  (h.general D V ρ hyp).groupCases ρ

theorem AdequateCompleteClassificationInput.groupCases_of_ff [Finite D]
    {K : GroupClass.{u}} (h : AdequateCompleteClassificationInput.{u,v} K)
    (hyp : FFHypothesis K ρ) (hff : IsFFModule ρ) :
    (IsQuasisimple (generalizedFitting D) ∧ QuasisimpleModel (generalizedFitting D)) ∨
      AdequateNonQuasisimpleAlternative ρ :=
  (h.general D V ρ hyp).groupCases_of_ff ρ hff

/-! The group-only outer route used by core and order consumers. -/

theorem outerSixThreeShape_product_normal
    (c : ChapterB.OuterSixThreeShape D) :
    (c.first ⊔ c.second).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← c.generates]
  have hfirst : InducesOuter c.first c.element := c.firstOuter
  have hsecond : InducesOuter c.second c.element := c.secondOuter
  refine sup_le (c.first ⊔ c.second).le_normalizer (zpowers_le.mpr ?_)
  exact normalizer_inf_normalizer_le_normalizer_sup _ _
    ⟨hfirst.mem_normalizer, hsecond.mem_normalizer⟩

theorem outerSixThreeShape_quotient_isCyclic
    (c : ChapterB.OuterSixThreeShape D)
    [hn : (c.first ⊔ c.second).Normal] :
    IsCyclic (D ⧸ (c.first ⊔ c.second)) := by
  let q := QuotientGroup.mk' (c.first ⊔ c.second)
  apply isCyclic_iff_exists_zpowers_eq_top.mpr
  refine ⟨q c.element, ?_⟩
  have h := congrArg (Subgroup.map q) c.generates
  rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
    MonoidHom.map_zpowers,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
  exact h

variable [Finite D]

theorem outerSixThreeShape_threePrimeCore_eq_bot
    (c : ChapterB.OuterSixThreeShape D)
    (ρ : Representation (ZMod 2) D V)
    (hg : offenderSubgroup ρ = ⊤) (h₂ : pCore 2 D = ⊥) :
    pPrimeCore 3 D = ⊥ := by
  have hfirst : pPrimeCore 3 c.first = ⊥ :=
    pPrimeCore_eq_bot_of_equiv c.firstEquiv
      Theory.SpecificGroups.alternatingSix_threePrimeCore
  have hsecond : pPrimeCore 3 c.second = ⊥ :=
    pPrimeCore_eq_bot_of_equiv c.secondEquiv
      Theory.SpecificGroups.cyclicThree_threePrimeCore
  have hN : pPrimeCore 3 (c.first ⊔ c.second : Subgroup D) = ⊥ :=
    pPrimeCore_eq_bot_of_equiv c.product.symm (pPrimeCore_prod_eq_bot hfirst hsecond)
  let := outerSixThreeShape_product_normal c
  let := outerSixThreeShape_quotient_isCyclic c
  let := IsCyclic.commGroup (α := D ⧸ (c.first ⊔ c.second))
  have hQ := abelian_image_isTwoGroup ρ (QuotientGroup.mk' (c.first ⊔ c.second))
    (QuotientGroup.mk'_surjective _) hg
  exact pPrimeCore_eq_bot_of_pCore_eq_bot_of_quotient (p := 3) (q := 2)
    (c.first ⊔ c.second) hN hQ h₂

theorem AdequateNonQuasisimpleAlternative.threePrimeCore_eq_bot
    (c : AdequateNonQuasisimpleAlternative ρ)
    (hg : offenderSubgroup ρ = ⊤) (h₂ : pCore 2 D = ⊥) :
    pPrimeCore 3 D = ⊥ := by
  cases c with
  | symmetricThree c => exact c.threePrimeCore_eq_bot ρ
  | twoFactors c => exact c.toBasic ρ |>.threePrimeCore_eq_bot ρ
  | outerSixThree c => exact outerSixThreeShape_threePrimeCore_eq_bot c ρ hg h₂
  | hyperplane c => exact c.threePrimeCore_eq_bot ρ

theorem AdequateCompleteClassificationInput.threePrimeCore_eq_bot
    {K : GroupClass.{u}}
    (h : AdequateCompleteClassificationInput.{u,v} K)
    (hyp : FFHypothesis K ρ) (hff : IsFFModule ρ) :
    pPrimeCore 3 D = ⊥ := by
  rcases h.groupCases_of_ff ρ hyp hff with ⟨hq, hm⟩ | hnq
  · exact threePrimeCore_eq_bot_of_quasisimple_alternative hm
      (fun _ => Theory.SpecificGroups.g2_derived_two_center_isThreeGroup)
  · exact hnq.threePrimeCore_eq_bot ρ hyp.generated hyp.twoCore

/-- The old complete input gives an adequate input by forgetting only the
outer representation fields.  This direction is sound; no converse is
claimed. -/
theorem CompleteClassificationInput.toAdequate
    {K : GroupClass.{u}} (h : CompleteClassificationInput.{u,v} K) :
    AdequateCompleteClassificationInput.{u,v} K where
  quasisimple := h.quasisimple
  general := fun D _ _ V _ _ ρ hyp =>
    (h.general D V ρ hyp).toAdequate

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
