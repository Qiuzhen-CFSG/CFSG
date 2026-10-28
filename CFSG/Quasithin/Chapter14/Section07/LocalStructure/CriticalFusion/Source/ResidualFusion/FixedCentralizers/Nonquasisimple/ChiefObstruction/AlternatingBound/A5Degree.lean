module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ChiefObstruction.AlternatingBound
public import Theory.SpecificGroups.Alternating.FiveChiefDegree

/-!
# The A₅ degree input on the original K-chief sections

The original marking `KCoreA5` identifies K/O₂(K) with the actual alternating
group on five letters. Together with `K_twoPerfect`, it gives order at least
sixteen for every noncentral binary section of K. This discharges the
`factor_card` premise in the A₇ chief-count consumer, for both block types.

The independent intersection filtration must still construct the injective
pair maps; no normality of K in Lᵤ is asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 14.7.68(2), printed pp.1071–1072.
-/

public section

open Subgroup NoncentralChiefRefinement

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u

namespace Data
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u}
  [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

include d in
/-- The original K marking supplies the minimum order of its actual sections. -/
theorem K_noncentral_two_section_card_ge_sixteen
    (A B : NormalNode (K F)) (h : IsNoncentralTwo A B) :
    16 ≤ Nat.card (Section A B) :=
  alternatingGroup.FiveChiefDegree.section_card_ge_sixteen
    (K_twoPerfect F) d.KCoreA5 A B h

/-- The A₇ bound with its minimum chief-factor degree now proved.
The remaining pair-map premise is the independent intersection-filtration input. -/
theorem every_complete_K_chief_count_le_one_of_pairMap
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (c27 : Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Conclusion
      KnownSimple.IsKnownSimple (d.fixedCentralizer u) Lu (d.fixedCore u)
        (F.H ⊓ d.fixedCentralizer u : Subgroup G))
    (hLu : Nonempty ((Lu ⧸ pCore 2 Lu) ≃* alternatingGroup (Fin 7)))
    (block : ChapterC.IsAlternatingBlock Lu 7 ∨
      ChapterC.IsExceptionalA7Block Lu)
    (pairMap : ∀ (s : ChiefSeries (K F)) (i j : Fin s.length),
      i ≠ j → IsNoncentralTwo (s i.castSucc) (s i.succ) →
      IsNoncentralTwo (s j.castSucc) (s j.succ) →
      Section (s i.castSucc) (s i.succ) ×
        Section (s j.castSucc) (s j.succ) → ChapterC.BlockModule Lu)
    (pairMap_injective : ∀ (s : ChiefSeries (K F)) (i j : Fin s.length)
      (hij : i ≠ j) (hi : IsNoncentralTwo (s i.castSucc) (s i.succ))
      (hj : IsNoncentralTwo (s j.castSucc) (s j.succ)),
      Function.Injective (pairMap s i j hij hi hj))
    (s : ChiefSeries (K F)) (hs0 : s.head = ⊥) (hs1 : s.last = ⊤) :
    s.noncentralTwoCount ≤ 1 :=
  d.every_complete_K_chief_count_le_one u h c27 hLu block
    (fun t i hi => d.K_noncentral_two_section_card_ge_sixteen
      (t i.castSucc) (t i.succ) hi)
    pairMap pairMap_injective s hs0 hs1

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
