module

public import CFSG.Quasithin.Chapter2.Section05.PSL2PairSource
public import CFSG.Quasithin.Chapter2.Section05.SourceCompletionInputs
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.NativeSource

/-!
# The proved ZD theorem in the source 2.5.21 pair argument

The completed Aschbacher strong-closure theorem excludes the literal source
PSL2 crossing pair and the disjoint strongly closed pair bounded by a proper
subgroup. These applications discharge the former universal ZD premise.
The Section 2.5 owner still constructs the original Incoming configuration
and completes its other branches; those conclusions are not assumed here.

Source: Aschbacher--Smith, proof of 2.5.21, printed pp.566--567.
-/

public section
open Subgroup Theory.GroupTheory
open BenderSuzuki.PFchapter1section1
open CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure
namespace CFSG.Quasithin.Chapter2
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original PSL2 crossing-pair source bundle is impossible, with the
Asc75 and ZD source theorems supplied. -/
theorem PSL2PairSource.Incoming.false_of_prime_crossing_pair_source
    {κ : GroupClass.{u}} {p : ℕ} [Fact p.Prime]
    (d : PSL2PairSource.Incoming κ G p) : False :=
  d.false_of_prime_crossing_pair_of_theoremZD Asc75.theoremZD

/-- The actual disjoint-pair application of the now unconditional Asc75
lemma, retaining both ranks and the literal intersection-generated bound. -/
theorem SourceCompletionInputs.false_of_disjoint_source_pair_source
    (T : Sylow 2 G) (A B Mplus : Subgroup G)
    (hA : A ≠ ⊥) (hB : B ≠ ⊥) (hd : Disjoint A B)
    (ha : A ≤ T) (hb : B ≤ T) (hc : ⁅A, B⁆ = ⊥)
    (hra : TwoRankAtLeastTwo A) (hrb : TwoRankAtLeastTwo B)
    (hclosed : IsStronglyClosedSet ((A : Set G) ∪ B) (T : Subgroup G) ⊤)
    (hproper : Mplus ≠ ⊤) (hbound : intersectionGenerated A B ≤ Mplus) : False :=
  false_of_disjoint_source_pair_of_theoremZD Asc75.theoremZD T A B Mplus
    hA hB hd ha hb hc hra hrb hclosed hproper hbound

end CFSG.Quasithin.Chapter2
