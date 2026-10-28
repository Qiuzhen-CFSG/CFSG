module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.FullNormalizer.QuaternionExchange.Geometry
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.ElevenSubgroup.MarkedNormalizers.FullNormalizer.QuaternionExchange.MarkedFacts

/-!
# The remaining permutation calculation at the pivot

For a nonidentity even element b of the first fusion eight, the marked
involution zb is a triple transposition, and its centralizer together with
the transposition centralizer generates S. These are statements inside the
given marked S₆; they do not involve square roots or quaternion conjugators.
The contract here does not assert their existence. The root-and-four-group
calculation supplies all other fields of `MarkedGeometry` independently.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), Lemma 4.8, p.41.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.QuaternionExchange

open Subgroup

variable {G : Type*} [Group G] [Finite G] {z : G}
variable {h : Hypotheses z} {a : SourceGeometry h}

/-- The permutation statements still needed after constructing the root
and both literal even fusion groups. -/
public structure PivotPermutationGeometry (s : SymmetricSixData h a) (b : G) : Prop where
  t_mem : z * b ∈ s.S
  t_cycleType : (s.equiv ⟨z * b, t_mem⟩).cycleType = {2, 2, 2}
  generated : (s.S ⊓ Centralizer z) ⊔ (s.S ⊓ Centralizer (z * b)) = s.S

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.ElevenSubgroup.QuaternionExchange
