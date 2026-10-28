module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column0.Rows00
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column0.Rows01
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column0.Rows02
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column0.Rows03
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column0.Rows04
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column0.Rows05
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column0.Rows06
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column0.Rows07
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column0.Rows08
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column0.Rows09
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column0.Rows10
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column0.Rows11
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column0.Rows12
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column0.Rows13
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column0.Rows14
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column0.Rows15
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column0.Rows16
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column0.Rows17
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column0.Rows18

/-!
# Certified Held double-coset transition column 0

For each of the 4,831 unchanged representatives and both middle factors,
right multiplication by `move 0 = representative 1` factors through another
published representative, with both outer factors in `markedSubgroup`.
The 9,662 equations are kernel-checked in the imported interval certificates.
Their soundness uses the proved four-point base of the actual Held carrier.

Source: the candidate words in `DoubleCosets/source/column0.json`, with
ATLAS attribution and source context in `DoubleCosets/source/README.md`.
This is one input to the separate assembly theorem `covers_of_columns`.
-/

namespace Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets

/-- Every transition in column 0, with no additional hypotheses. -/
public theorem column0 : TransitionColumn 0 := by
  intro j e
  by_cases h00 : j.val < 256
  · exact Column0Certificate.rows00 j (by omega) h00 e
  by_cases h01 : j.val < 512
  · exact Column0Certificate.rows01 j (by omega) h01 e
  by_cases h02 : j.val < 768
  · exact Column0Certificate.rows02 j (by omega) h02 e
  by_cases h03 : j.val < 1024
  · exact Column0Certificate.rows03 j (by omega) h03 e
  by_cases h04 : j.val < 1280
  · exact Column0Certificate.rows04 j (by omega) h04 e
  by_cases h05 : j.val < 1536
  · exact Column0Certificate.rows05 j (by omega) h05 e
  by_cases h06 : j.val < 1792
  · exact Column0Certificate.rows06 j (by omega) h06 e
  by_cases h07 : j.val < 2048
  · exact Column0Certificate.rows07 j (by omega) h07 e
  by_cases h08 : j.val < 2304
  · exact Column0Certificate.rows08 j (by omega) h08 e
  by_cases h09 : j.val < 2560
  · exact Column0Certificate.rows09 j (by omega) h09 e
  by_cases h10 : j.val < 2816
  · exact Column0Certificate.rows10 j (by omega) h10 e
  by_cases h11 : j.val < 3072
  · exact Column0Certificate.rows11 j (by omega) h11 e
  by_cases h12 : j.val < 3328
  · exact Column0Certificate.rows12 j (by omega) h12 e
  by_cases h13 : j.val < 3584
  · exact Column0Certificate.rows13 j (by omega) h13 e
  by_cases h14 : j.val < 3840
  · exact Column0Certificate.rows14 j (by omega) h14 e
  by_cases h15 : j.val < 4096
  · exact Column0Certificate.rows15 j (by omega) h15 e
  by_cases h16 : j.val < 4352
  · exact Column0Certificate.rows16 j (by omega) h16 e
  by_cases h17 : j.val < 4608
  · exact Column0Certificate.rows17 j (by omega) h17 e
  exact Column0Certificate.rows18 j (by omega) j.isLt e

end Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets
