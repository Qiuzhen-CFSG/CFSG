module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.CoverModels
public import Theory.Mathieu.M22.BinaryCovers
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Ratios
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuFamily
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.TripleSevenExclusion

/-!
# Unmarked small-ratio group models for the F.9.18 application

The full Theorems A and C classify the central quotient of the actual
quasisimple generalized Fitting subgroup. The permitted alternating and
binary Lie families already give the required group models: perfection
identifies the symplectic and G2 models with their actual derived subgroups.
The Chapter K triple-seven exclusion supplies the omitted cover condition
uniformly. For M22, faithful binary irreducibility restricts the center to
order one or three, yielding the genuine simple or triple-cover alternatives.

The odd parameter sieves and the completed sporadic cubic exclusions leave
the ten explicit constructors of `RemainingModel`. This is a proved partial
reduction, not the full B.4.5 theorem. The small odd-linear, triality/Ree,
and M11/HS exclusions have independent source owners; J2 and M12/M23/M24
still need their unmarked quadratic exclusions. No small-displacement witness,
module marking, normalizer non-FF premise, or classification callback is assumed.
The literal local-source consumer is `SourceModels.SmallRatio`.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
B.4.5, printed p.87; Chapter K, pp.451--460; F.9.18(4), pp.325--326.
-/

public section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SmallRatioClassification.UnmarkedQuadratic
open Chapter13.Section08.Components Chapter1.Section02.LocalModels
open Models
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The whole ambient cubic source action excludes the genuine triple cover of A7. -/
theorem no_triple_seven (h : ChapterK.RankOne.SourceHypotheses ρ L) :
    ¬ IsAlternatingCover L 7 := by
  intro hc
  let : IsQuasisimple L := h.quasisimple
  obtain ⟨e⟩ := hc.2.2
  obtain ⟨a⟩ := GLS3.Chapter5.OddCentralCovers.triple_seven_equiv e
    (CoverModels.threeCover_center_card hc)
  exact ChapterK.Alternating.tripleSevenExclusion ρ KnownSimple.IsKnownSimple L
    ⟨h.sqtk, h.fitting.symm, h.quasisimple, h.faithful, h.irreducible,
      h.smallCubic, Or.inr ⟨e⟩⟩ a

private theorem of_quotient (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hm : F918QuotientModel (L ⧸ center L)) : F918Models L :=
  Or.inl ⟨hm, no_triple_seven h⟩

private noncomputable def derivedEquiv {A B : Type*} [Group A] [Group B]
    [Group.IsPerfect A] (e : A ≃* B) : A ≃* commutator B := by
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact e.trans ((MulEquiv.subgroupCongr (Group.IsPerfect.commutator_eq_top (G := B))).trans
    Subgroup.topEquiv).symm

private noncomputable def commutatorEquiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) : commutator A ≃* commutator B := by
  refine (e.subgroupMap _).trans (MulEquiv.subgroupCongr ?_)
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  rfl

private noncomputable def sixEquiv : alternatingGroup (Fin 6) ≃*
    commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) :=
  Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix.symm.trans
    (commutatorEquiv Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)

/-- Every alternating quotient in Theorem C gives an actual F.9.18 quotient model. -/
theorem of_alternating (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {n : ℕ} (hn : n ≤ 8) (e : L ⧸ center L ≃* alternatingGroup (Fin n)) :
    F918Models L := by
  have hlo := SourceClassification.alternating_degree_ge_five h e
  have hc : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
  apply of_quotient h
  rcases hc with rfl | rfl | rfl | rfl
  · exact .bender (.linear 2 (by decide) ⟨GaloisField 2 2, inferInstance, inferInstance,
      GaloisField.card 2 2 (by decide),
      ⟨e.trans Atlas.Comparisons.Exceptional.psl2FourEquivAlt5.symm⟩⟩)
  · exact .symplectic 1 (by decide) ⟨ZMod 2, inferInstance, inferInstance, by norm_num,
      ⟨e.trans sixEquiv⟩⟩
  · exact .alternating_seven ⟨e⟩
  · exact .linear_four ⟨ZMod 2, inferInstance, inferInstance, by norm_num,
      ⟨e.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm⟩⟩

/-- Perfection and the characteristic-two center comparison retain the derived group. -/
theorem of_symplectic (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {r : ℕ} (hr : 1 ≤ r) (hm : ClassicalGroup.IsPSp (L ⧸ center L) 2 (2 ^ r)) :
    F918Models L := by
  let : IsQuasisimple L := h.quasisimple
  let : Group.IsPerfect (L ⧸ center L) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center L))
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
  exact of_quotient h (.symplectic r hr ⟨F, inferInstance, inferInstance, hcard,
    ⟨derivedEquiv (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)⟩⟩)

/-- The actual G2 matrix model is perfect because the marked source quotient is perfect. -/
theorem of_g2 (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {r : ℕ} (hr : 1 ≤ r) (hm : ClassificationModels.IsG2At (L ⧸ center L) (2 ^ r)) :
    F918Models L := by
  let : IsQuasisimple L := h.quasisimple
  let : Group.IsPerfect (L ⧸ center L) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center L))
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hm
  exact of_quotient h (.g2 r hr ⟨F, inferInstance, inferInstance, hcard, ⟨derivedEquiv e⟩⟩)

/-- The small G2 endpoint is already the literal derived group in F.9.18. -/
theorem of_g2_derived (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (e : L ⧸ center L ≃* commutator (Atlas.G2.Model (ZMod 2))) : F918Models L :=
  of_quotient h (.g2 1 (by decide) ⟨ZMod 2, inferInstance, inferInstance, by norm_num, ⟨e⟩⟩)

omit [FiniteDimensional (ZMod 2) V] in
/-- Binary irreducibility gives the simple M22 or genuine central triple-cover alternative. -/
theorem of_mathieu_twentyTwo (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m22.Carrier)) :
    F918Models L := by
  let : IsQuasisimple L := h.quasisimple
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  obtain ⟨e⟩ := he
  rcases Sporadic.Mathieu.M22BinaryCovers.center_card_eq_one_or_three_of_binary_irreducible
      (ρ.comp L.subtype) (h.faithful.comp L.subtype_injective) e with hc | hc
  · exact Or.inr (Or.inl ⟨Sporadic.Mathieu.M22BinaryCovers.simpleEquiv e hc⟩)
  · exact Or.inr (Or.inr ⟨h.quasisimple,
      ⟨mulEquivOfPrimeCardEq hc (Nat.card_zmod 3)⟩, ⟨e⟩⟩)

/-- Unresolved source families, each with an actual central-quotient marking. -/
inductive RemainingModel (L : Type*) [Group L] : Prop
  | linear_two_twentyFive (model : ClassicalGroup.IsPSL (L ⧸ center L) 2 25)
  | linear_three_three (model : ClassicalGroup.IsPSL (L ⧸ center L) 3 3)
  | triality (r : ℕ) (hr : 1 ≤ r)
      (model : Triality.Standard.IsTrialityGroupAt (2 ^ r) (L ⧸ center L))
  | ree (m : ℕ) (hm : 1 ≤ m) (model : Nonempty ((L ⧸ center L) ≃* ReeF4.Model m))
  | mathieu_eleven (model : Nonempty ((L ⧸ center L) ≃* KnownSimple.SporadicName.m11.Carrier))
  | mathieu_twelve (model : Nonempty ((L ⧸ center L) ≃* KnownSimple.SporadicName.m12.Carrier))
  | mathieu_twentyThree (model : Nonempty ((L ⧸ center L) ≃* KnownSimple.SporadicName.m23.Carrier))
  | mathieu_twentyFour (model : Nonempty ((L ⧸ center L) ≃* KnownSimple.SporadicName.m24.Carrier))
  | janko_two (model : Nonempty ((L ⧸ center L) ≃* KnownSimple.SporadicName.j2.Carrier))
  | higman_sims (model : Nonempty ((L ⧸ center L) ≃* KnownSimple.SporadicName.hs.Carrier))

/-- The odd source catalogue leaves only PSL2(25) and PSL3(3) unresolved. -/
theorem odd_reduction (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hm : ChapterA.Section02.IsTheoremCOddModel (L ⧸ center L)) :
    F918Models L ∨ RemainingModel L := by
  cases hm with
  | linear_two p e hp ho he hm =>
    rcases Chapter7.NormalizedSource.NonMathieuFamily.odd_linear_two_parameters h hp ho he hm
        with hq | hq | hq | hq
    · rw [hq] at hm
      obtain ⟨e⟩ := ChapterK.OddCharacteristic.altFive_of_psl2_five hm
      exact Or.inl (of_alternating h (by decide) e)
    · rw [hq] at hm
      obtain ⟨e⟩ := ChapterK.OddCharacteristic.psl3Two_of_psl2_seven hm
      exact Or.inl (of_quotient h (.linear_three 1 (by decide)
        ⟨ZMod 2, inferInstance, inferInstance, by norm_num, ⟨e⟩⟩))
    · rw [hq] at hm
      obtain ⟨e⟩ := ChapterK.OddCharacteristic.altSix_of_psl2_nine hm
      exact Or.inl (of_alternating h (by decide) e)
    · exact Or.inr (.linear_two_twentyFive (hq ▸ hm))
  | linear_three p hp ho hm =>
    exact Or.inr (.linear_three_three
      ((Chapter7.NormalizedSource.NonMathieuFamily.odd_linear_three_parameter h hp ho hm) ▸ hm))
  | unitary_three p hp ho hm =>
    obtain ⟨e⟩ := ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.source_g2Derived_of_cubicRatio_le_two
      ρ L ⟨h.sqtk, h.fitting.symm, h.quasisimple, h.faithful, h.irreducible⟩
      hp ho hm h.smallCubic
    exact Or.inl (of_g2_derived h e)

/-- M22 is accepted and the proved cubic exclusions remove J1, J4, Held and Rudvalis. -/
theorem sporadic_reduction (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hm : ChapterA.Section02.IsTheoremCSporadicModel (L ⧸ center L)) :
    F918Models L ∨ RemainingModel L := by
  rcases h.fitting with rfl
  have hs : ChapterK.SporadicCatalogue.SourceHypotheses ρ :=
    ⟨h.sqtk, h.quasisimple, h.faithful, h.irreducible, h.smallCubic⟩
  rcases hm with ⟨name, hne, he⟩ | he
  · cases name with
    | m11 => exact Or.inr (.mathieu_eleven he)
    | m12 => exact Or.inr (.mathieu_twelve he)
    | m22 => exact Or.inl (of_mathieu_twentyTwo h he)
    | m23 => exact Or.inr (.mathieu_twentyThree he)
    | m24 => exact Or.inr (.mathieu_twentyFour he)
    | j2 => exact Or.inr (.janko_two he)
    | hs => exact Or.inr (.higman_sims he)
    | j3 => exact (hne rfl).elim
    | j4 => exact (ChapterK.SporadicCatalogue.sourceExclusion_j4_of_bounded_geometry
        ChapterK.SporadicCatalogue.boundedSourceExclusion_j4 ρ hs he).elim
    | he => exact (ChapterK.SporadicCatalogue.sourceExclusion_he ρ hs he).elim
    | ru => exact (ChapterK.SporadicCatalogue.sourceExclusion_ru ρ hs he).elim
  · exact (ChapterK.SporadicCatalogue.sourceExclusion_j1 ρ hs he).elim

/-- An unconditional partial sieve on the genuine Chapter K cubic source domain. -/
theorem models_or_remaining (h : ChapterK.RankOne.SourceHypotheses ρ L) :
    F918Models L ∨ RemainingModel L := by
  have hm := SourceClassification.quotient_model_of_theoremsAC
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremC_knownSimple h
  cases hm with
  | alternating n hn he => exact Or.inl (of_alternating h hn (Classical.choice he))
  | odd hm => exact odd_reduction h hm
  | bender hm => exact Or.inl (of_quotient h (.bender hm))
  | linear_binary n hn hm =>
    rcases hn with rfl | rfl
    · exact Or.inl (of_quotient h (.linear_four hm))
    · exact Or.inl (of_quotient h (.linear_five hm))
  | sporadic hm => exact sporadic_reduction h hm
  | rank_two r hm =>
    cases hm with
    | linear hr he => exact Or.inl (of_quotient h (.linear_three r hr he))
    | symplectic hr he => exact Or.inl (of_symplectic h (by omega) he)
    | g2 hr he => exact Or.inl (of_g2 h (by omega) he)
    | triality hr he => exact Or.inr (.triality r hr he)
    | ree_f4 m hm _ he => exact Or.inr (.ree m hm he)
    | symplectic_derived _ he => exact Or.inl (of_alternating h (by decide)
        ((Classical.choice he).trans
          Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix))
    | g2_derived _ he => exact Or.inl (of_g2_derived h (Classical.choice he))
    | tits _ he => exact (SourceClassification.tits_exclusion h (Classical.choice he)).elim

open Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases in
/-- The exact B.4 hypotheses and quadratic bound supply the cubic source domain. -/
theorem b4_models_or_remaining [Finite V]
    (h : B4Hypotheses KnownSimple.IsKnownSimple ρ) (hq : quadraticRatio ρ ≤ 2) :
    F918Models (generalizedFitting G) ∨ RemainingModel (generalizedFitting G) :=
  models_or_remaining ⟨h.sqtk, rfl, h.quasisimple, h.faithful, h.irreducible,
    (Representation.BinaryOffender.cubicRatio_le_quadraticRatio ρ).trans hq⟩

end CFSG.Quasithin.ChapterB.SmallRatioClassification.UnmarkedQuadratic
