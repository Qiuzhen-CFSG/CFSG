module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.ClassifierCases.Models
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.MarkedModels.Groups
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Product
public import Theory.Representation.NormalInvariants

/-!
# The rank-one component in the hyperplane alternative

The actual internal product places the marked component in one of its two
factors. Component maximality and the order-four obstruction exclude the
first SL₃(2) factor and the repeated-SL₃ second factor, even at multiplicity
zero. In the SL₂ case, the marked component equals the second factor.

Its supplied second space is exactly [V,C]. The fixed subrepresentation for
the normal subgroup C therefore constructs a MovedSection whose central
quotient is the supplied reduced action, with the identity on representatives.
An actual field isomorphism transports the natural coordinates to the original
field. No complement or identification with the whole moved space is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.6(5),
printed p.105, and the first paragraph of 13.6.18, p.931 (PDF p.948).
The group-only comparisons are reused from the attributed marked-model proofs;
no legacy classification or module implication is invoked.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.ClassifierCases.Hyperplane
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.MarkedModels

universe u w
variable {D : Type u} [Group D] {A B C : Subgroup D}

private theorem first_normal (h : InternalProduct A B) : A.Normal := by
  have hk : h.snd.ker = A := by
    ext g
    obtain ⟨a, b, rfl⟩ := h.exists_mul g
    have hs : h.snd ((a : D) * (b : D)) = b := by
      rw [← h.apply_eq]
      exact congrArg Prod.snd (h.equiv.symm_apply_apply (a, b))
    change h.snd ((a : D) * (b : D)) = 1 ↔ (a : D) * (b : D) ∈ A
    rw [hs]
    constructor
    · rintro rfl
      simp
    · intro hab
      let c : A := ⟨(a : D) * (b : D), hab⟩
      have he : h.equiv (a, b) = h.equiv (c, 1) := by
        simp only [h.apply_eq, OneMemClass.coe_one, mul_one, c]
      exact congrArg Prod.snd (h.equiv.injective he)
  rw [← hk]
  infer_instance

private theorem component_le_factor (h : InternalProduct A B) (hc : IsComponent D C) :
    C ≤ A ∨ C ≤ B := by
  let : A.Normal := first_normal h
  let : B.Normal := h.second_normal
  let : IsQuasisimple C := hc.2
  let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
  let : Nontrivial C := (QuotientGroup.mk'_surjective (center C)).nontrivial
  rcases hc.normal_dichotomy A with ha | ha
  · exact Or.inl ha
  rcases hc.normal_dichotomy B with hb | hb
  · exact Or.inr hb
  have ht : (⊤ : Subgroup D) ≤ centralizer (C : Set D) := by
    rw [← h.sup_eq_top]
    exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp ha))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hb))
  have hcc : ⁅C, C⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr (le_top.trans ht)
  rw [commutator_eq_self] at hcc
  exact ((nontrivial_iff_ne_bot C).mp inferInstance hcc).elim

variable [Finite D] {V : Type w} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V}

/-- Preserve the carrier and every field operation when applying the existing
group-only comparisons. This does not transport a classification assertion. -/
private def comparisonField (F : BinaryField) :
    CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.BinaryField where
  Carrier := F.Carrier
  degree := F.degree
  degree_pos := F.degree_pos
  card_eq := F.card_eq

/-- The marked component is the actual second factor, and that factor has
the supplied natural central quotient. The repeated-SL₃ branch is excluded
using its actor, independently of its multiplicity. -/
theorem second_natural [C.Normal] (hc : IsQuasisimple C)
    (F : BinaryField) (hF : 1 < F.degree) (e : C ≃* SL(2,F.Carrier))
    (c : HyperplaneCase ρ) :
    C = c.second ∧ ∃ E : BinaryField,
      IsLinearNatural (reducedAction (c.secondSpace.toRepresentation.comp c.second.subtype)) E 2 := by
  have hC : IsComponent D C := ⟨(inferInstance : C.Normal).isSubnormal, hc⟩
  have hm : ClassicalGroup.IsPSL C 2 (2 ^ F.degree) :=
    ⟨F.Carrier, inferInstance, inferInstance, F.card_eq,
      ⟨e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL⟩⟩
  have hCB : C ≤ c.second := by
    rcases component_le_factor c.product hC with h | h
    · exact (GroupComparisons.not_linearThree hC h hm (comparisonField BinaryField.two)
        c.firstEquiv).elim
    · exact h
  cases c.secondCase with
  | linearThree r _ natural =>
    obtain ⟨a⟩ := natural
    exact (GroupComparisons.not_linearThree hC hCB hm (comparisonField BinaryField.two)
      a.groupEquiv).elim
  | linearTwo E natural =>
    obtain ⟨a⟩ := natural
    exact ⟨(GroupComparisons.linearTwo hC hCB hF hm (comparisonField E) a.groupEquiv).1,
      E, ⟨a⟩⟩

/-- The original second space and its actual second-factor fixed space,
both retaining the action of D. -/
noncomputable def secondSection (c : HyperplaneCase ρ) : MovedSection ρ c.second := by
  let : c.second.Normal := c.product.second_normal
  exact {
    space := c.secondSpace
    space_eq := c.secondSpace_eq
    central := fixedSubrepresentationOfNormal c.secondSpace.toRepresentation c.second
    central_eq := rfl }

/-- The literal central quotient is the supplied reduced action: both actor
and quotient maps are identities. -/
noncomputable def sectionReduced (c : HyperplaneCase ρ) :
    ActionEquiv ((secondSection c).action.comp c.second.subtype)
      (reducedAction (c.secondSpace.toRepresentation.comp c.second.subtype)) where
  groupEquiv := MulEquiv.refl _
  linearEquiv := LinearEquiv.refl _ _
  intertwines _ _ := rfl

/-- B.5.6(5) gives the natural constructor on the literal moved central
quotient, over the originally specified field. No further classification input
is needed once the hyperplane alternative is supplied. -/
theorem natural_quotient [C.Normal] (hc : IsQuasisimple C)
    (F : BinaryField) (hF : 1 < F.degree) (e : C ≃* SL(2,F.Carrier))
    (c : HyperplaneCase ρ) :
    ∃ s : MovedSection ρ C, Nonempty (ActionEquiv (s.action.comp C.subtype) (linearNatural F 2)) := by
  obtain ⟨hC, E, ⟨a⟩⟩ := second_natural hc F hF e c
  subst C
  let f := sectionReduced c
  let t := sameFieldNatural E F (a.groupEquiv.symm.trans e)
  refine ⟨secondSection c, ⟨⟨a.groupEquiv.trans t.groupEquiv,
    f.linearEquiv.trans (a.linearEquiv.trans t.linearEquiv), ?_⟩⟩⟩
  intro g v
  exact (congrArg t.linearEquiv (congrArg a.linearEquiv (f.intertwines g v))).trans
    ((congrArg t.linearEquiv (a.intertwines _ _)).trans (t.intertwines _ _))

/-- The hyperplane branch of the rank-one component classifier used in
13.6.18. Its conclusion is specifically the natural central-quotient case. -/
theorem component_case {𝒦 : GroupClass.{u}} [C.Normal] (_hyp : FFHypothesis 𝒦 ρ)
    (hc : IsQuasisimple C) (F : BinaryField) (hF : 1 < F.degree)
    (e : C ≃* SL(2,F.Carrier)) (c : HyperplaneCase ρ) : RankOneComponentCase ρ C F := by
  obtain ⟨s, ⟨a⟩⟩ := natural_quotient hc F hF e c
  exact .natural s a

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.ClassifierCases.Hyperplane
end
