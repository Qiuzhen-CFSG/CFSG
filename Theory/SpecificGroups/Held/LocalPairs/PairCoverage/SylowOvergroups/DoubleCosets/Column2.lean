module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column2.Block00
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column2.Block01
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column2.Block02
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column2.Block03
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column2.Block04
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column2.Block05
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column2.Block06
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column2.Block07
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column2.Block08
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column2.Block09
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column2.Block10
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column2.Block11
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column2.Block12
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column2.Block13
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column2.Block14
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column2.Block15
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column2.Block16
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column2.Block17
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column2.Block18

/-!
# The third Held double-coset transition column

All 9,662 candidate factorizations have been checked in the unchanged Held
carrier. The nineteen representative blocks cover every index, and each
block treats both middle factors. Thus right multiplication by representative
4279 after either 1 or marked generator 3 lands in a published double coset.

Source: `source/column2.json` and `source/README.md`. The certificate proves
this transition column; the full coverage assembly also uses columns 0 and 1.
-/

namespace Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets

/-- Every representative has both certified transitions for the third move. -/
public theorem column2 : TransitionColumn 2 := by
  intro j e
  by_cases h0 : j.val < 256
  · exact Column2.block00 j (by omega) h0 e
  by_cases h1 : j.val < 512
  · exact Column2.block01 j (by omega) h1 e
  by_cases h2 : j.val < 768
  · exact Column2.block02 j (by omega) h2 e
  by_cases h3 : j.val < 1024
  · exact Column2.block03 j (by omega) h3 e
  by_cases h4 : j.val < 1280
  · exact Column2.block04 j (by omega) h4 e
  by_cases h5 : j.val < 1536
  · exact Column2.block05 j (by omega) h5 e
  by_cases h6 : j.val < 1792
  · exact Column2.block06 j (by omega) h6 e
  by_cases h7 : j.val < 2048
  · exact Column2.block07 j (by omega) h7 e
  by_cases h8 : j.val < 2304
  · exact Column2.block08 j (by omega) h8 e
  by_cases h9 : j.val < 2560
  · exact Column2.block09 j (by omega) h9 e
  by_cases h10 : j.val < 2816
  · exact Column2.block10 j (by omega) h10 e
  by_cases h11 : j.val < 3072
  · exact Column2.block11 j (by omega) h11 e
  by_cases h12 : j.val < 3328
  · exact Column2.block12 j (by omega) h12 e
  by_cases h13 : j.val < 3584
  · exact Column2.block13 j (by omega) h13 e
  by_cases h14 : j.val < 3840
  · exact Column2.block14 j (by omega) h14 e
  by_cases h15 : j.val < 4096
  · exact Column2.block15 j (by omega) h15 e
  by_cases h16 : j.val < 4352
  · exact Column2.block16 j (by omega) h16 e
  by_cases h17 : j.val < 4608
  · exact Column2.block17 j (by omega) h17 e
  exact Column2.block18 j (by omega) j.isLt e

end Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets
