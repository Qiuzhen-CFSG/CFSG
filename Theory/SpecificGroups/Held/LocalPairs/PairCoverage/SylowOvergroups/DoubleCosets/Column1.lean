module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column1.Block00
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column1.Block01
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column1.Block02
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column1.Block03
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column1.Block04
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column1.Block05
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column1.Block06
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column1.Block07
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column1.Block08
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column1.Block09
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column1.Block10
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column1.Block11
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column1.Block12
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column1.Block13
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column1.Block14
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column1.Block15
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column1.Block16
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column1.Block17
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column1.Block18

/-!
# The complete second Held double-coset transition column

Every one of the 4831 unchanged representatives, with each of the two middle
factors, is multiplied by representative 9 and factored through a published
representative with both outer factors in the marked subgroup. The 9662
candidate rows from `DoubleCosets/source/column1.json` are all certified by
Lean in the imported blocks; the interval split below exhausts their indices.

Source and conventions: `DoubleCosets/source/README.md`.
-/

namespace Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets

/-- Unconditional closure under the second move, for both middle factors. -/
public theorem column1 : TransitionColumn 1 := by
  intro j e
  have he : e.toNat ≤ 1 := by cases e <;> decide
  by_cases h0 : 2 * j.val + e.toNat < 512
  · exact Column1Certificate.block00 j e (by omega) h0
  by_cases h1 : 2 * j.val + e.toNat < 1024
  · exact Column1Certificate.block01 j e (by omega) h1
  by_cases h2 : 2 * j.val + e.toNat < 1536
  · exact Column1Certificate.block02 j e (by omega) h2
  by_cases h3 : 2 * j.val + e.toNat < 2048
  · exact Column1Certificate.block03 j e (by omega) h3
  by_cases h4 : 2 * j.val + e.toNat < 2560
  · exact Column1Certificate.block04 j e (by omega) h4
  by_cases h5 : 2 * j.val + e.toNat < 3072
  · exact Column1Certificate.block05 j e (by omega) h5
  by_cases h6 : 2 * j.val + e.toNat < 3584
  · exact Column1Certificate.block06 j e (by omega) h6
  by_cases h7 : 2 * j.val + e.toNat < 4096
  · exact Column1Certificate.block07 j e (by omega) h7
  by_cases h8 : 2 * j.val + e.toNat < 4608
  · exact Column1Certificate.block08 j e (by omega) h8
  by_cases h9 : 2 * j.val + e.toNat < 5120
  · exact Column1Certificate.block09 j e (by omega) h9
  by_cases h10 : 2 * j.val + e.toNat < 5632
  · exact Column1Certificate.block10 j e (by omega) h10
  by_cases h11 : 2 * j.val + e.toNat < 6144
  · exact Column1Certificate.block11 j e (by omega) h11
  by_cases h12 : 2 * j.val + e.toNat < 6656
  · exact Column1Certificate.block12 j e (by omega) h12
  by_cases h13 : 2 * j.val + e.toNat < 7168
  · exact Column1Certificate.block13 j e (by omega) h13
  by_cases h14 : 2 * j.val + e.toNat < 7680
  · exact Column1Certificate.block14 j e (by omega) h14
  by_cases h15 : 2 * j.val + e.toNat < 8192
  · exact Column1Certificate.block15 j e (by omega) h15
  by_cases h16 : 2 * j.val + e.toNat < 8704
  · exact Column1Certificate.block16 j e (by omega) h16
  by_cases h17 : 2 * j.val + e.toNat < 9216
  · exact Column1Certificate.block17 j e (by omega) h17
  exact Column1Certificate.block18 j e (by omega) (by omega)

end Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets
