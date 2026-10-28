module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ChiefObstruction.AlternatingBound
public import CFSG.Quasithin.ChapterC.Section01.ChiefSections.A7Quotient

/-!
# The literal intersection maps in the A7 chief obstruction

Use the original inclusion K → Lᵤ to intersect K with U(Lᵤ), then project to
the actual block module. The general representative construction discharges
both product-map premises of `every_complete_K_chief_count_le_one` for either
ordinary or exceptional A7 blocks.

The actual A5/A7 core markings and two-perfectness of K prove central binary
chief factors in K/(K intersect U(Lᵤ)). Thus every noncentral binary section
survives in the intersection filtration with its full K-action, and the pair
embedding has no remaining quotient or section-survival premise. The product
map chooses representatives; only the section isomorphisms are asserted to be
equivariant.

The count application retains the independent minimum-section-order premise,
proved in `AlternatingBound.A5Degree`. The A7 exclusion's assembly owner
`qt-14-07-fixed-a7-chief-bound` combines these results with the original
two-chief-factor obstruction. Both block types use exactly the same inclusion
and projection, without normality of K in Lᵤ.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
C.1.7, C.1.22 and 14.7.68(2), printed pp.123, 129 and 1071--1072.
-/

public section
noncomputable section

open Subgroup NoncentralChiefRefinement Theory.GroupTheory

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08

universe u
namespace Data

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u}
  [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- The source inclusion and fixed denominator supply the chief-pair injection
once the quotient above the intersection has central binary chief factors. -/
def KChiefPairEmbedding (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (hquot : HasCentralPChiefFactors 2
      (K F ⧸ (ChapterC.blockU Lu).comap (d.KToFixedComponent u h)))
    (s : ChiefSeries (K F)) (i j : Fin s.length) (hij : i ≠ j)
    (hi : IsNoncentralTwo (s i.castSucc) (s i.succ))
    (hj : IsNoncentralTwo (s j.castSucc) (s j.succ)) :
    Section (s i.castSucc) (s i.succ) × Section (s j.castSucc) (s j.succ) ↪
      ChapterC.BlockModule Lu :=
  ChapterC.chiefPairEmbedding (d.KToFixedComponent u h)
    (inclusion_injective h.larger.le) hquot s i j hij hi hj

/-- Consumer application for both A7 block possibilities. The numerical
factor bound and the earlier quotient-filtration input remain explicit. -/
theorem every_complete_K_chief_count_le_one_of_intersection_quotient
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (c27 : Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Conclusion
      KnownSimple.IsKnownSimple (d.fixedCentralizer u) Lu (d.fixedCore u)
        (F.H ⊓ d.fixedCentralizer u : Subgroup G))
    (hLu : Nonempty ((Lu ⧸ pCore 2 Lu) ≃* alternatingGroup (Fin 7)))
    (block : ChapterC.IsAlternatingBlock Lu 7 ∨ ChapterC.IsExceptionalA7Block Lu)
    (hquot : HasCentralPChiefFactors 2
      (K F ⧸ (ChapterC.blockU Lu).comap (d.KToFixedComponent u h)))
    (factor_card : ∀ (s : ChiefSeries (K F)) (i : Fin s.length),
      IsNoncentralTwo (s i.castSucc) (s i.succ) →
        16 ≤ Nat.card (Section (s i.castSucc) (s i.succ)))
    (s : ChiefSeries (K F)) (hs0 : s.head = ⊥) (hs1 : s.last = ⊤) :
    s.noncentralTwoCount ≤ 1 := by
  exact d.every_complete_K_chief_count_le_one u h c27 hLu block factor_card
    (fun s i j hij hi hj => d.KChiefPairEmbedding u h hquot s i j hij hi hj)
    (fun s i j hij hi hj => (d.KChiefPairEmbedding u h hquot s i j hij hi hj).injective)
    s hs0 hs1

/-- The actual A5/A7 quotients discharge the central-chief premise above the
literal intersection K ∩ U(Lᵤ), using two-perfectness of the original K. -/
theorem K_blockIntersection_hasCentralTwoChiefFactors_of_a7
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (hLu : Nonempty ((Lu ⧸ pCore 2 Lu) ≃* alternatingGroup (Fin 7))) :
    HasCentralPChiefFactors 2
      (K F ⧸ (ChapterC.blockU Lu).comap (d.KToFixedComponent u h)) := by
  obtain ⟨eLu⟩ := hLu
  exact ChapterC.a7_blockIntersection_hasCentralTwoChiefFactors
    (d.KToFixedComponent u h) (inclusion_injective h.larger.le)
    eLu d.KCoreA5 (K_twoPerfect F)

/-- The original K-action survives on each counted interval of the literal
intersection filtration, for either A7 block possibility. -/
def KChiefIntersectionEquiv_of_a7
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (hLu : Nonempty ((Lu ⧸ pCore 2 Lu) ≃* alternatingGroup (Fin 7)))
    (s : ChiefSeries (K F)) (i : Fin s.length)
    (hi : IsNoncentralTwo (s i.castSucc) (s i.succ)) :
    SectionEquiv
      ((s.intersectionFiltration
        (ChapterC.blockIntersection (d.KToFixedComponent u h))).term i.castSucc)
      ((s.intersectionFiltration
        (ChapterC.blockIntersection (d.KToFixedComponent u h))).term i.succ)
      (s i.castSucc) (s i.succ) :=
  ChapterC.a7_chiefIntersectionEquiv (d.KToFixedComponent u h)
    (inclusion_injective h.larger.le) hLu.some d.KCoreA5 (K_twoPerfect F) s i hi

/-- Two distinct noncentral binary K-chief sections inject into the actual
block module, with no central-chief, survival or cardinality premise. -/
def KChiefPairEmbedding_of_a7
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (hLu : Nonempty ((Lu ⧸ pCore 2 Lu) ≃* alternatingGroup (Fin 7)))
    (s : ChiefSeries (K F)) (i j : Fin s.length) (hij : i ≠ j)
    (hi : IsNoncentralTwo (s i.castSucc) (s i.succ))
    (hj : IsNoncentralTwo (s j.castSucc) (s j.succ)) :
    Section (s i.castSucc) (s i.succ) × Section (s j.castSucc) (s j.succ) ↪
      ChapterC.BlockModule Lu :=
  d.KChiefPairEmbedding u h (d.K_blockIntersection_hasCentralTwoChiefFactors_of_a7 u h hLu)
    s i j hij hi hj

/-- The literal intersection construction discharges both pair-map premises
for ordinary and exceptional A7 blocks. Only the independent degree bound remains. -/
theorem every_complete_K_chief_count_le_one_of_a7_intersection
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (c27 : Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Conclusion
      KnownSimple.IsKnownSimple (d.fixedCentralizer u) Lu (d.fixedCore u)
        (F.H ⊓ d.fixedCentralizer u : Subgroup G))
    (hLu : Nonempty ((Lu ⧸ pCore 2 Lu) ≃* alternatingGroup (Fin 7)))
    (block : ChapterC.IsAlternatingBlock Lu 7 ∨ ChapterC.IsExceptionalA7Block Lu)
    (factor_card : ∀ (s : ChiefSeries (K F)) (i : Fin s.length),
      IsNoncentralTwo (s i.castSucc) (s i.succ) →
        16 ≤ Nat.card (Section (s i.castSucc) (s i.succ)))
    (s : ChiefSeries (K F)) (hs0 : s.head = ⊥) (hs1 : s.last = ⊤) :
    s.noncentralTwoCount ≤ 1 :=
  d.every_complete_K_chief_count_le_one u h c27 hLu block factor_card
    (fun s i j hij hi hj => d.KChiefPairEmbedding_of_a7 u h hLu s i j hij hi hj)
    (fun s i j hij hi hj => (d.KChiefPairEmbedding_of_a7 u h hLu s i j hij hi hj).injective)
    s hs0 hs1

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
