module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.AssemblyFixedLine
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.BinarySmallDisplacement

/-!
# Original 15.3.25 using only rank-two selection and path replacement

The C.1.32 alternatives supply the full alternating-six and G₂ blocks.
Their natural-core contradictions are already proved. A binary intrinsic
quotient forces the binary parabolic marking by the orders of the three
actual star groups. The binary row is then excluded by prescribed critical
path replacement and the original first-line displacement argument.

This avoids C.1.34's complete module classification. C.1.32 at the original
small pair and prescribed replacement at its actual MS setup remain explicit;
the corrected B.5 classification, fixed-line identity and paired offender
contradiction are internal. All original residual choices are preserved.

Source: Aschbacher--Smith C.1.32 and 15.3.25--32, printed pp.135--136,
1130--1134; Meierfrankenfeld--Stellmacher (1993), sections 4 and 7.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension SmallExtension.MarkedMS
open SmallExtension.CentralCover SmallExtension.CentralCover.LinearThree
open ChapterC BinaryMS.MS93 BinaryMS.MS93.DistanceEight.PathCentrality
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Only C.1.32 at the actual original pair is used in this core comparison.
The field degree, exceptional cover and symplectic-four exclusions are internal. -/
theorem source_coreAlternatives_of_rankTwo
    {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (hcases : RankTwoAlternatives c.L d.S) : CoreAlternatives c.L d.S := by
  have h27 := Parabolics.not_tripleCoverAlternatingSix d s.minimal.1 c
    s.facts s.solvableControl s.normal
  change (_ ∧ _) ∨ (_ ∧ _) ∨ (_ ∧ _) ∨ (_ ∧ _) ∨ _ at hcases
  rcases hcases with h | h | h | h | ⟨n, hn, F, hField, hFinite, hF, ⟨e⟩⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact (MarkedMS.not_sp4FourBlock d c s.normal s.sylow s.sylow_eq hm h.2).elim
  · exact (MarkedMS.not_exceptionalAhat6Block d c s.characteristicTwo s.contains
      s.normal ⟨s.sylow, s.sylow_eq⟩ h27 h.2).elim
  · exact Or.inr (Or.inr (MarkedMS.linearThree_binary d c s.normal s.sylow
      s.sylow_eq hm n hn F hF e).2)

-- Retain the existing finite-ambient interface of this source adapter.
set_option linter.unusedSectionVars false in
/-- A binary intrinsic quotient selects the original binary parabolic row.
The other marked star carriers have orders 360 and 6048, whereas this quotient
has order 168. No module classification is needed for this comparison. -/
theorem source_binary_parabolic_of_coreQuotient
    {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    Nonempty (Parabolics.RankTwoParabolicMarking d I c.L
      (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
      Parabolics.linearThreeParabolic) := by
  let _ := coreAlternatives_simple c.core_quotient_quasisimple
    (show CoreAlternatives c.L d.S from Or.inr (Or.inr ⟨e⟩))
  have hc : Nat.card (d.starImage I c.L) = 168 :=
    (Nat.card_congr (coreQuotientEquivStar d c s.normal s.sylow s.sylow_eq).symm.toEquiv).trans
      ((Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_SL)
  cases hm with
  | linearThree m => exact ⟨m⟩
  | symplecticDerived m =>
    have hh := Nat.card_congr (m.equiv.trans
      (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
        (by simp))).toEquiv
    rw [nat_card_alternatingGroup] at hh
    norm_num at hh
    omega
  | g2Derived m =>
    have hh := Nat.card_congr m.equiv.toEquiv
    rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure,
      Atlas.G2.BinaryException.card_H] at hh
    omega

/-- The literal small source is excluded by C.1.32 and prescribed replacement.
All B.5 module markings and all nonbinary core calculations are already proved. -/
theorem source_small_false_of_rankTwo_and_replacement
    {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (hcases : RankTwoAlternatives c.L d.S)
    (replacement : ∀ (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
      (t : InputSetup (source_binaryMSInput s e)),
      CommonFacts t.reduction.radical t.source t.geometry →
      4 < t.geometry.b t.reduction.radical → ∀ {a a'}
      (p : CriticalPath t.reduction.radical t.geometry a a'),
      HasTurnConjugators t.reduction.radical p → PrescribedReplacement t.reduction.radical p) :
    False := by
  have hc := source_coreAlternatives_of_rankTwo s hm hcases
  have hs := coreAlternatives_simple c.core_quotient_quasisimple hc
  rcases hc with h | h | ⟨⟨e⟩⟩
  · exact source_small_false_of_MS_cases s hm (Or.inl h) hs
  · exact source_small_false_of_MS_cases s hm (Or.inr (Or.inl h)) hs
  · obtain ⟨m⟩ := source_binary_parabolic_of_coreQuotient s hm e
    exact source_linearThree_false_of_replacement s m replacement

/-- Original 15.3.25 without the full C.1.34 classification. The remaining
inputs refer only to original small components and their literal MS setups. -/
theorem source_lemma_15_3_25_of_rankTwo_and_replacement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    (rankTwo : ∀ {I : Subgroup G} (c : ComponentWitness d I),
      SourceData KnownSimple.IsKnownSimple d c →
      Parabolics.SmallParabolicMarking d I c.L → RankTwoAlternatives c.L d.S)
    (replacement : ∀ {I : Subgroup G} (c : ComponentWitness d I)
      (s : SourceData KnownSimple.IsKnownSimple d c)
      (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
      (t : InputSetup (source_binaryMSInput s e)),
      CommonFacts t.reduction.radical t.source t.geometry →
      4 < t.geometry.b t.reduction.radical → ∀ {a a'}
      (p : CriticalPath t.reduction.radical t.geometry a a'),
      HasTurnConjugators t.reduction.radical p → PrescribedReplacement t.reduction.radical p) :
    ∀ I ∈ d.Hplus, generalizedFitting I ≠ pCore 2 I := by
  apply source_not_characteristicTwo_of_branches hG d hempty hM hu hmany hshadow
  · intro I c s hm
    exact source_small_false_of_rankTwo_and_replacement s hm (rankTwo c s hm) (replacement c s)
  · intro I c e mark
    exact source_lemma_15_3_32_3 hG d hempty hM hu hmany hshadow
      e.source.minimal e.source.characteristicTwo c mark

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
