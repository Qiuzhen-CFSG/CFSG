module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.Models
public import CFSG.Quasithin.ChapterF.Section01.SourceDefs

/-!
# The output of the larger-field parabolic inspection

The source first derives a maximal S-invariant parabolic, then uses the
three-prime residual to reduce it to a Borel in exactly these three model
families. This is an output contract for that inspection, not an extra
hypothesis of 15.3.43. Its producer must retain every incoming family and
central cover from `Model`.

The independent Borel-action calculation can consume this output before
the classification proof is available. The final assembly must construct
it from the incoming model and `ReducedConfiguration`.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
proof of 15.3.43, printed p.1140, the paragraph beginning `Assume that n > 1`.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels

variable {G : Type*} [Group G]

/-- The linear-three family is specified on the central quotient so that
the nontrivial two-covers at field order four remain available. -/
inductive BorelModel (L : Subgroup G) (n : ℕ) : Prop
  | linearTwo (even : Even n) (iso : ClassicalGroup.IsPSL L 2 (2 ^ n))
  | linearThree (even : Even n)
      (iso : ClassicalGroup.IsPSL (L ⧸ center L) 3 (2 ^ n))
  | unitaryThree (iso : ClassicalGroup.IsPSU L 3 (2 ^ n))

/-- Both the family and the actual upstairs Borel equality must be proved. -/
structure LargerFieldBorel (S M L : Subgroup G) (n : ℕ) : Prop where
  model : BorelModel L n
  intersection : M ⊓ L = ChapterF.Source.borel L S

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels
