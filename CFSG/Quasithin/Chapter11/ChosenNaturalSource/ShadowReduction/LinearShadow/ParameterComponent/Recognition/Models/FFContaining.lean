module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.RankOneFFSource
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.CorrectedCatalogue
public import Theory.SpecificGroups.AlternatingEight.ReducedCover
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder

/-!
# The complete FF containing-quotient shortlist

Apply the corrected B.5.1 classification to the actual full-normalizer offender
supplement on the unchanged chosen Irr⁺ space. The literal projection recovers
PSL₂, binary linear, derived G₂ and hexacode quotients. Nonbinary SL₃, Sp₄ and
G₂ rows retain their central-quotient action markings, including scalar covers.
An alternating-eight action recovers the original quotient through the universal
double cover. Every remaining finite row has two-part smaller than 64; oddness
of the entire central kernel proves this also for the small alternating covers.

FFSource applies this exhaustive shortlist to the original component embedding.
The actual FF witness remains an input; this is not a proof of 7.0.1.
Source: Aschbacher--Smith, B.5.1 and 11.3.5, printed pp.99--103,771--772.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.QuasisimpleNormalizer
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {J W : Subgroup G}

/-- The literal containing quotient, with natural markings in the three
nonbinary rows; the finite exceptional rows have two-part smaller than 64. -/
def FFContainingModels (E : Chapter12.Section02.ChosenModule T J W) : Prop :=
  (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 2 (2 ^ f)) ∨
  (∃ F : BinaryField, 1 < F.degree ∧ E.NaturalRankTwoAction F) ∨
  (∃ d : ℕ, (d = 3 ∨ d = 4 ∨ d = 5) ∧ ClassicalGroup.IsPSL (J ⧸ pCore 2 J) d 2) ∨
  ¬ 64 ∣ Nat.card (J ⧸ pCore 2 J)

private theorem small_alternating_cover {X : Type*} [Group X] [Finite X]
    (hc : pCore 2 X = ⊥) {n : ℕ} (hn : 5 ≤ n) (hu : n ≤ 7)
    (f : PerfectCentralCovering.Cover X (alternatingGroup (Fin n))) :
    ¬ 64 ∣ Nat.card X := by
  have hcop : Nat.Coprime 64 (Nat.card f.toMonoidHom.ker) := by
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr
      (PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot hc _ f.ker_le_center)).pow_left 6
  have he : Nat.card X = Nat.card (alternatingGroup (Fin n)) * Nat.card f.toMonoidHom.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      f.toMonoidHom f.surjective).toEquiv]
    exact card_eq_card_quotient_mul_card_subgroup _
  intro hd
  rw [he] at hd
  have ha := hcop.dvd_of_dvd_mul_right hd
  interval_cases n <;> rw [nat_card_alternatingGroup,Nat.card_fin] at ha <;> norm_num at ha

private theorem binary_model {X : Type*} [Group X] {d : ℕ}
    (hd : 0 < d) (e : X ≃* Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) :
    ClassicalGroup.IsPSL X d 2 :=
  ⟨ZMod 2,inferInstance,inferInstance,by simp,
    ⟨e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL hd).symm⟩⟩

variable {E : Chapter12.Section02.ChosenModule T J W}
    {A : Type*} [Group A] [Finite A]
    {ρ : Representation (ZMod 2) A E.space} {C : Subgroup A}

omit [Finite A] in
private theorem alternating_row
    (c : E.LiteralComparison ρ C) (hq : IsQuasisimple (J ⧸ pCore 2 J))
    {n : ℕ} (hn : 5 ≤ n) (hu : n ≤ 8) (e : C ≃* alternatingGroup (Fin n)) :
    FFContainingModels E := by
  by_cases he : n = 8
  · subst n
    let := hq
    let f := c.modelCover hq e
    have hi := AlternatingEight.reduced_cover_injective f.toMonoidHom f.surjective
      (pCore_quotient_pCore_eq_bot 2)
    let a := MulEquiv.ofBijective f.toMonoidHom ⟨hi,f.surjective⟩
    exact .inr (.inr (.inl ⟨4,.inr (.inl rfl),
      ⟨ZMod 2,inferInstance,inferInstance,by simp,
        ⟨a.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm⟩⟩⟩))
  · exact .inr (.inr (.inr (small_alternating_cover
      (pCore_quotient_pCore_eq_bot 2) hn (by omega) (c.modelCover hq e))))

private theorem classified_rows
    (c : E.LiteralComparison ρ C) (hq : IsQuasisimple (J ⧸ pCore 2 J))
    (b : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C) :
    FFContainingModels E := by
  have hbin {d : ℕ} (hd : d = 4 ∨ d = 5)
      (e : C ≃* Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) : FFContainingModels E := by
    have hp := c.projection_injective_of_binaryLinear hq hd e
    exact .inr (.inr (.inl ⟨d,.inr hd,binary_model (by omega)
      ((MulEquiv.ofBijective c.projection ⟨hp,c.surjective⟩).trans e)⟩))
  have hsmall (e : (J ⧸ pCore 2 J) ≃* Atlas.Codes.HexEvenAutomorphisms) :
      FFContainingModels E := by
    apply Or.inr ∘ Or.inr ∘ Or.inr
    rw [Nat.card_congr e.toEquiv,Atlas.Codes.hexEven_card]
    decide
  cases b.clause_one with
  | doubleThree F _ e _ _ => exact (c.not_doubleThree b.sectionData F e).elim
  | naturalDual d hd _ he => exact (c.not_naturalDual b.sectionData (by omega) he.some).elim
  | repeatedNatural d r hd _ _ _ he => exact hbin hd he.some.groupEquiv
  | irreducible hi hf hirr hs he =>
    rcases Chapter12.Section02.ChosenModule.LiteralComparison.corrected_catalogue_or_triple hs
      with hs | ⟨a⟩
    · cases Chapter12.Section02.ModuleClassification.sourceRow_of_irreducible hs with
      | rankOne F e =>
        obtain ⟨hF,hm⟩ := c.rankOne_marking hq F e.groupEquiv
        exact .inl ⟨F.degree,by omega,hm⟩
      | linearThree e =>
        have hp := c.projection_injective_of_linearThree hq e.groupEquiv
        exact .inr (.inr (.inl ⟨3,.inl rfl,binary_model (by decide)
          ((MulEquiv.ofBijective c.projection ⟨hp,c.surjective⟩).trans e.groupEquiv)⟩))
      | nonbinaryLinearThree F hF e =>
        have hp := c.projection_injective_of_nonbinary_linearThree hq F hF e.groupEquiv
        exact .inr (.inl ⟨F,hF,.sl3 ⟨(c.quotientMarking b.sectionData hp).trans e⟩⟩)
      | symplectic F hF e =>
        have hp := c.projection_injective_of_nonbinary_symplectic hq F hF e.groupEquiv
        exact .inr (.inl ⟨F,hF,.sp4 ⟨(c.quotientMarking b.sectionData hp).trans e⟩⟩)
      | g2 F hF e =>
        have hp := c.projection_injective_of_nonbinary_g2 hq F hF e.groupEquiv
        exact .inr (.inl ⟨F,hF,.g2 ⟨(c.quotientMarking b.sectionData hp).trans e⟩⟩)
      | derivedG2 e =>
        have hp := c.projection_injective_of_binaryDerivedG2 hq e.groupEquiv
        let a := (MulEquiv.ofBijective c.projection ⟨hp,c.surjective⟩).trans e.groupEquiv
        apply Or.inr ∘ Or.inr ∘ Or.inr
        rw [Nat.card_congr a.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
        decide
      | alternating n hn hu e => exact alternating_row c hq hn hu e.groupEquiv
      | alternatingSevenFour e _ => exact alternating_row c hq (by decide) (by decide) e
      | tripleSix a => exact hsmall (c.tripleSix_marking hq b.sectionData a).choose
      | binaryLinear d hd e => exact hbin hd e.groupEquiv
      | exteriorFive e _ => exact hbin (.inr rfl) e
    · exact hsmall (c.corrected_tripleSix_marking hq b.sectionData a.some).choose

/-- B.5.1 on the unchanged chosen space constructs a complete containing
quotient shortlist, including the actual nonbinary natural action. -/
theorem chosen_ff_containing_models (E : Chapter12.Section02.ChosenModule T J W)
    (hJ : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T J)
    (hff : IsFFModule (normalizerRepresentation E.chosenAction)) : FFContainingModels E := by
  obtain ⟨A,hA,hC,⟨b⟩⟩ := E.full_normalizer_source_conclusion hJ
    (E.chosen_normalizer_ff_iff_seedComponent.mp hff)
  let : Finite (supplement (E.seedRepresentation.comp E.componentImage.subtype) A) :=
    supplement_finite _ A
  exact classified_rows (E.normalizerOffenderComparison A hC) hJ.quasisimple b

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models
