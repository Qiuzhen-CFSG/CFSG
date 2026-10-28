module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedSylowSieve
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedSylowOffenderAssembly
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.SymplecticTwo

/-!
# The reduced B.4.2 table for the moved chosen seed

The invariant-model exclusions remove the natural SL₂ and G₂ rows and the
deleted permutation rows of degrees five, seven and eight. The derived Sp₄(2)
action is transported to the actual natural A₆ action, and the distinct
four-dimensional A₇ row is retained. Only the triple-A₆ and ten-dimensional
SL₅(2) exceptions remain beside the intended constituent models.

Both exceptional rows retain their literal action and offender information.
The source 3.2.5 and Chapter 12 applications discharge the FF premise and all
invariant-row exclusions. Exceptional-row exclusion, the two-type bound and
full-normalizer exhaustion remain local obligations of qt-baumann-fsu; these
conditional applications do not assert the completed source theorem.

Source: Aschbacher--Smith B.4.2, D.3.5(4--5), D.3.10, 3.2.5 and 12.2.2,
combined manuscript of 1 March 2004, printed pp.86,195--196,201,580 and794--795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The two exceptional B.4.2 rows left after the invariant-model exclusions.
The common ratio, actual action coordinates, group marking, and literal
offender subgroups are retained for the remaining D.3.5 argument. -/
@[expose] def SeedSieveExceptions (D : ChosenModule T L V) : Prop :=
  quadraticRatio D.seedRepresentation = 1 ∧
  offenderSubgroup D.seedRepresentation = D.componentImage ∧
  (Nonempty (ChapterB.SourceInduction.ProjectiveLine.TripleSixAction
    D.seedRepresentation D.componentImage) ∨
  (D.componentImage = ⊤ ∧
    ∃ e : D.componentImage ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2),
      Module.finrank (ZMod 2) D.space = 10 ∧
      ∀ A, IsBestOffender D.seedRepresentation A →
        IsEndNodeRadical ((A.subgroupOf D.componentImage).map e.toMonoidHom)))

/-- B.4.2 on a moved chosen seed leaves precisely the D.3.10 constituent
models and the two rows requiring the shared-actor offender exclusion. -/
theorem seed_constituentModel_or_exceptional_of_ff (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hff : IsFFModule D.seedRepresentation) :
    ConstituentModel (D.seedRepresentation.comp D.componentImage.subtype) ∨
      D.SeedSieveExceptions := by
  have hs := D.seed_b4_of_ff h hc hff
  cases hs with
  | linearTwo F _ e _ _ =>
    exact (D.seed_not_linearTwo_of_moved h.quasisimple hc hm F ⟨e⟩).elim
  | linearThree F _ e _ => exact Or.inl (Or.inl ⟨F,⟨e⟩⟩)
  | symplectic F hF _ e _ => exact Or.inl (Or.inr (Or.inl ⟨F,hF,⟨e⟩⟩))
  | symplecticTwo e _ =>
    exact Or.inl (Or.inr (Or.inr (Or.inl
      ⟨ExtensionConsequences.SymplecticTwo.markedAlternatingActionEquiv e⟩)))
  | g2 F hF _ e _ _ => exact (D.seed_not_g2_of_moved h.quasisimple hc hm F hF ⟨e⟩).elim
  | g2Two e _ _ =>
    exact (D.seed_not_g2Two_of_moved h.quasisimple hc hm
      ⟨ExtensionConsequences.markedRestriction e⟩).elim
  | symmetric n hn e _ _ =>
    have h5 : 5 ≤ n := by rcases hn with rfl | rfl <;> omega
    have h6 : n ≠ 6 := by rcases hn with rfl | rfl <;> omega
    exact (D.seed_not_alternatingNatural_of_moved h.quasisimple hc hm n h5 h6
      ⟨ExtensionConsequences.markedRestriction e⟩).elim
  | alternatingSix _ e _ _ => exact Or.inl (Or.inr (Or.inr (Or.inl ⟨e⟩)))
  | alternatingSeven _ _ e hd _ _ =>
    exact Or.inl (D.seed_constituentModel_of_alternatingSeven e hd)
  | tripleSix hg a hq => exact Or.inr ⟨hq,hg,Or.inl ⟨a⟩⟩
  | binaryLinear d hd _ e _ => exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨d,hd,⟨e⟩⟩))))
  | orthogonalSix _ _ e _ _ =>
    exact (D.seed_not_alternatingNatural_of_moved h.quasisimple hc hm 8
      (by decide) (by decide) ⟨e⟩).elim
  | symmetricEight _ e _ =>
    exact (D.seed_not_alternatingNatural_of_moved h.quasisimple hc hm 8
      (by decide) (by decide) ⟨ExtensionConsequences.markedRestriction e⟩).elim
  | exteriorFive hg ht e hd ho hq => exact Or.inr ⟨hq,hg,Or.inr ⟨ht,e,hd,ho⟩⟩

/-- The ambient multiple-overgroup hypothesis discharges the FF input, so
this reduced table applies to the literal moved chosen seed without callbacks. -/
theorem seed_constituentModel_or_exceptional_of_moved_of_many (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) :
    ConstituentModel (D.seedRepresentation.comp D.componentImage.subtype) ∨
      D.SeedSieveExceptions :=
  D.seed_constituentModel_or_exceptional_of_ff h.toHypothesis1221 hc hm
    (D.seed_ff_of_moved_of_many h hmany hc hm)

/-- Source 3.2.5 after removal of all invariant B.4.2 rows. The two exceptional
rows, the two-type bound and full-orbit exhaustion remain internal obligations
of qt-baumann-fsu. -/
theorem source325_of_exceptional_exclusion_types_and_exhaustion_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hexception : cubicRatio D.orbitRepresentation ≤ 2 →
      V ⊓ centralizer (L : Set G) = ⊥ → V < componentOrbit V (T : Subgroup G) →
      D.SeedSieveExceptions → False)
    (htypes : cubicRatio D.orbitRepresentation ≤ 2 →
      V ⊓ centralizer (L : Set G) = ⊥ → V < componentOrbit V (T : Subgroup G) →
      ConstituentModel (D.seedRepresentation.comp D.componentImage.subtype) →
      D.SylowTwoModuleTypes)
    (hexhaust : cubicRatio D.orbitRepresentation ≤ 2 →
      D.NormalizerOrbitCubicBound h.toHypothesis1221 →
      V ⊓ centralizer (L : Set G) = ⊥ → V < componentOrbit V (T : Subgroup G) →
      D.SylowMovedModel →
      componentOrbit V (normalizer (L : Set G)) = componentOrbit V (T : Subgroup G)) :
    D.Source325Alternatives := by
  apply D.source325_of_sieve_and_exhaustion_of_many h hmany _ hexhaust
  intro hq hc hm hff
  have hmodel : ConstituentModel (D.seedRepresentation.comp D.componentImage.subtype) :=
    (D.seed_constituentModel_or_exceptional_of_ff h.toHypothesis1221 hc hm hff).resolve_right
      (hexception hq hc hm)
  exact ⟨hmodel,htypes hq hc hm hmodel⟩

/-- Actual Chapter 12 application of the reduced table. Exceptional-row
exclusion, the type bound and exhaustion are retained by qt-baumann-fsu;
the final exclusion of the doubled branch is owned by qt-d-1222-source. -/
theorem structural_of_exceptional_exclusion_types_and_exhaustion_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hexception : cubicRatio D.orbitRepresentation ≤ 2 →
      V ⊓ centralizer (L : Set G) = ⊥ → V < componentOrbit V (T : Subgroup G) →
      D.SeedSieveExceptions → False)
    (htypes : cubicRatio D.orbitRepresentation ≤ 2 →
      V ⊓ centralizer (L : Set G) = ⊥ → V < componentOrbit V (T : Subgroup G) →
      ConstituentModel (D.seedRepresentation.comp D.componentImage.subtype) →
      D.SylowTwoModuleTypes)
    (hexhaust : cubicRatio D.orbitRepresentation ≤ 2 →
      D.NormalizerOrbitCubicBound h.toHypothesis1221 →
      V ⊓ centralizer (L : Set G) = ⊥ → V < componentOrbit V (T : Subgroup G) →
      D.SylowMovedModel →
      componentOrbit V (normalizer (L : Set G)) = componentOrbit V (T : Subgroup G))
    (hex : ¬ D.MarkedDoubled) :
    (T : Subgroup G) ≤ normalizer (V : Set G) ∧
    IsPReduced 2 (V.subgroupOf (L ⊔ (T : Subgroup G))) ∧
    (∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V) ∧
    ((normalizer (L : Set G)) ≤ normalizer (V : Set G) ∨
      V ⊓ centralizer (L : Set G) = ⊥) :=
  D.structural_of_source325_of_not_doubled_of_many h hmany
    (D.source325_of_exceptional_exclusion_types_and_exhaustion_of_many
      h hmany hexception htypes hexhaust) hex

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
