module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.Sporadic.Reduction
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.J2Outer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InnerInvolutionCores
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterInvolutionCentralizer.PermutationComparison

/-!
# The complete J₂ seven-action inspection

The inner representatives have fixed groups of orders 240 and 1920; the
outer representative has fixed group of order 336. None is divisible by 2520,
so Cauchy's involution reduction excludes both seven models for every actual
two-subgroup of automorphisms.

Source: Aschbacher–Smith E.6.18 and 16.1.5(8), printed pp.252,1172.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SporadicInspection
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
open Sporadic.LeechRelated.J2.ExceptionalParabolics
open Sporadic.LeechRelated.J2.InnerInvolutionCores

/-- The actual J₂ fixed orders discharge all inner and outer table inputs. -/
theorem janko_two : SevenActionInspection Carrier := by
  apply of_involution_fixed_card
  intro r hr
  by_cases hi : ∃ g : Carrier, r = MulAut.conj g
  · rcases InnerInvolutionCores.inner_fixed_representatives r hr hi with he | he
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv, Nat.card_congr a_centralizer_equiv.toEquiv,
        Nat.card_prod,nat_card_alternatingGroup,Nat.card_fin]
      norm_num [E4,C2,Nat.card_fun,Nat.factorial]
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv]
      change ¬ 2520 ∣ Nat.card Seed.l₁
      rw [FirstParabolic.card_l₁]
      decide
  · obtain ⟨e⟩ := Chapter16.OtherPreliminaries.JankoTwoHigmanSims.J2Outer.outer_fixed_representative r hr hi
    rw [Nat.card_congr e.toEquiv,OuterInvolutionCentralizer.card_fixed]
    decide
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SporadicInspection
