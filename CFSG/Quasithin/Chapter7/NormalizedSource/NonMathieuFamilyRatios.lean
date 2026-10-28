module
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuFamily
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.JankoTwoSource

/-!
# The symplectic and J₂ cubic boundary on the original action

K.3.4 recognizes the actual symplectic component action as natural or a
half-field tensor. Non-FF of its full normalizer excludes the natural row.
For J₂ the odd-center theorem and faithful binary irreducibility kill the
center. The existing cubic degree argument gives degree twelve, and the
whole-action recognizer retains all outer actors. Both surviving models
have cubic ratio two and quadratic ratio strictly greater than two.

These numerical clauses are consumed by the ambient TI exclusion in
NonFFSourceNonMathieuFamilyComplete; they do not exclude the bare modules.
Source: Aschbacher--Smith K.3.4 and K.4.5, pp.456--457,460; 3.2.9, pp.582--583.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuFamily
variable {A E : Type*} [Group A] [Finite A] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E] {ρ : Representation (ZMod 2) A E} {Q : Subgroup A}

/-- K.3.4 on the unchanged non-FF component action. -/
theorem symplectic_ratios (hs : ChapterK.RankOne.SourceHypotheses ρ Q)
    (hnon : ¬ IsFFModule (normalizerRepresentation (ρ.comp Q.subtype)))
    {r : ℕ} (hr : 2 ≤ r) (he : ClassicalGroup.IsPSp (Q ⧸ center Q) 2 (2 ^ r)) :
    2 < quadraticRatio ρ ∧ cubicRatio ρ = 2 := by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := he
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have h : ChapterK.Symplectic.SourceHypothesis KnownSimple.IsKnownSimple ρ Q :=
    ⟨inferInstance, inferInstance, hs.sqtk, hs.fitting, hs.quasisimple,
      hs.faithful, hs.irreducible, hs.smallCubic⟩
  let := hs.irreducible
  obtain ⟨_,_,_,hnat | hten⟩ := ChapterK.Symplectic.source_complete h (by omega : 1 < r) hcard
    (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)
  · obtain ⟨_,_,hq,_⟩ := hnat
    apply (ambient_nonFF hs hnon ?_).elim
    apply (isFFModule_iff_quadraticRatio_le_one ρ).mpr
    rw [hq]
    norm_num [ENNReal.div_le_iff]
  · obtain ⟨s,_,_,a,M,hgeom⟩ := hten
    exact ⟨hgeom.2.1, hgeom.2.2.1⟩

/-- The actual J₂ central quotient gives both numerical clauses of K.4.5.
The existing cubic degree argument and whole-action recognizer preserve outer actors. -/
theorem janko_two_ratios (h : ChapterK.RankOne.SourceHypotheses ρ Q)
    (he : Nonempty (Q ⧸ center Q ≃* KnownSimple.SporadicName.j2.Carrier)) :
    2 < quadraticRatio ρ ∧ cubicRatio ρ = 2 := by
  let : IsQuasisimple Q := h.quasisimple
  have hz : center Q = ⊥ := by
    let : IsIrreducible (ρ.comp Q.subtype) := h.irreducible
    have hz2 := Theory.SpecificGroups.J2HSMultipliers.J2.center_isPGroup_of_quotient_equiv
      (Classical.choice he)
    have hk := normal_p_subgroup_le_ker (ρ.comp Q.subtype) (center Q) hz2
    apply bot_unique
    simpa only [(ρ.comp Q.subtype).ker_eq_bot_iff.mpr
      (h.faithful.comp Q.subtype_injective)] using hk
  have hd : Module.finrank (ZMod 2) E = 12 := by
    rcases h.fitting with rfl
    let e := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.trans
      (Classical.choice he)
    exact Chapter13.Section06.TerminalContradiction.Ratio.JankoTwoSource.finrank_eq_twelve h hz e
  obtain ⟨D⟩ := ChapterK.SporadicCatalogue.SourceFF.j2_marked_of_center_and_degree ρ Q h he hz hd
  exact ⟨D.two_lt_quadraticRatio (ChapterK.JankoTwo.NaturalLocalAction.b46RootFacts _)
    ChapterK.JankoTwo.NaturalLocalAction.b46LongRootModuleFacts_four,
    D.cubicRatio_eq_two (ChapterK.JankoTwo.NaturalLocalAction.b46RootFacts _)
    ChapterK.JankoTwo.NaturalLocalAction.b46LongRootModuleFacts_four⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuFamily
