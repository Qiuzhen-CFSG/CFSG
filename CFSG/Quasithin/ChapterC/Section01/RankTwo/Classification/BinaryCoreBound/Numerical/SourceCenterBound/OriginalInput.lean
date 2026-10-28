module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Numerical.SourceCenterBound.DistanceFour
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Numerical.SourceCenterBound.DistanceGreaterFour

/-!
# The binary numerical alternative from the original MS input

The abelian core theorem supplies actual elementary models of dimensions
three, four or six. For a nonabelian core, the checked characteristic setup
and common reduction produce the actual amalgam geometry. Evenness and b>2
split the remaining proof into b=4 and b>4. The early and radius constructors
discharge the complete distance-four application.

The sole callback supplies two source estimates in the larger-distance case:
the image of the actual core center lies in U_alpha join H_alpha, and H_alpha
has order at most four. The callback receives the same InputSetup and
CommonFacts used by the application. The checked numerical transport then
recovers the original commutator core through InputSetup.coreEquiv.

The final unconditional binary core-bound consumer must instantiate this
callback from the genuine (4.4)--(4.5) source calculations. No elementary
model of a nonabelian center or final numerical alternative is assumed.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4)--(4.6), pp.890--912,
and Aschbacher--Smith C.1.31--34, printed pp.135--137 of the combined
manuscript of 1 March 2004.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.Numerical.SourceCenterBound
open Subgroup
open MS93
open scoped IsMulCommutative

universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L T : Subgroup J}

/-- Assemble the numerical alternative for the original BinaryMS.Input.
The sole remaining callback supplies the one-sided core-center containment
and the order bound for H from the actual b>4 source setup and common facts.
The PathCentrality/CoreFactors source arguments must instantiate this
callback before the unconditional binary core-bound theorem is obtained.
The abelian branch, source realization, common reduction, even-distance
split and complete b=4 numerical branch are all discharged internally. -/
theorem originalInput_bound_of_distance_greater_four
    (h : Input κ L T)
    (greaterFour : ∀ (s : InputSetup h)
      (_common : CommonFacts s.reduction.radical s.source s.geometry),
      4 < s.geometry.b s.reduction.radical →
      (center (core s.reduction.radical (alpha s.reduction.radical))).map
        (core s.reduction.radical (alpha s.reduction.radical)).subtype ≤
        U s.reduction.radical (alpha s.reduction.radical) ⊔
          H s.reduction.radical (alpha s.reduction.radical) ∧
      Nat.card (H s.reduction.radical (alpha s.reduction.radical)) ≤ 4) :
    Nat.card (center (commutatorCore L)) ≤ 32 ∨ Nat.card (commutatorCore L) = 64 := by
  classical
  by_cases hc : IsMulCommutative (commutatorCore L)
  · obtain ⟨d, hd, ⟨e⟩⟩ := h.abelianCore_model hc
    have hcard : Nat.card (commutatorCore L) = 2 ^ d := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Fin d → ZMod 2) = _
      simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    have hcenter : Nat.card (center (commutatorCore L)) ≤ Nat.card (commutatorCore L) :=
      Nat.card_le_card_of_injective _ (center (commutatorCore L)).subtype_injective
    rcases hd with rfl | rfl | rfl
    · left
      norm_num at hcard
      omega
    · left
      norm_num at hcard
      omega
    · right
      norm_num at hcard
      exact hcard
  · obtain ⟨s⟩ := exists_setup h hc
    obtain ⟨common⟩ := s.commonFacts hc
    by_cases hb : s.geometry.b s.reduction.radical = 4
    · let early := MS93.DistanceFour.earlyFacts s.source s.geometry common hb
      let radius := MS93.DistanceFour.Flags.radiusFacts s.source s.geometry common hb early
      exact Or.inl (DistanceFour.inputSetup_center_bound s common radius hb)
    · have heven := s.geometry.even (alpha s.reduction.radical) rfl
      change Even (s.geometry.b s.reduction.radical) at heven
      obtain ⟨n, hn⟩ := heven
      have hlarge := common.large_distance
      have hbig : 4 < s.geometry.b s.reduction.radical := by omega
      obtain ⟨hcenter, hH⟩ := greaterFour s common hbig
      exact Or.inl
        (DistanceGreaterFour.inputSetup_center_bound_of_center_containment s common hcenter hH)

end CFSG.Quasithin.ChapterC.BinaryMS.Numerical.SourceCenterBound
