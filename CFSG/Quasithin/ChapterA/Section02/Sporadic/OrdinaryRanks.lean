module

public import Theory.Mathieu.M22.Properties.ThreeRank

/-!
# Ordinary sporadic ranks in A.2.19

The M22 calculation is proved on the concrete Steiner-system model, using an
explicit elementary abelian Sylow three-subgroup. This is the ordinary rank
used with A.2.14 in the central-cover branch of A.2.19.

The remaining J3 and McL rank calculations require their own concrete subgroup
and Sylow structure proofs; they are not inferred from descriptive rank tables.
This module retains final assembly of the three calculations.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), A.2.19, printed p. 41 (PDF p. 52).
-/

namespace CFSG.Quasithin.ChapterA

/-- M22 has ordinary three-rank two, as required in the cover branch of A.2.19. -/
public theorem m22_three_rank : primeRank 3 Sporadic.Mathieu.M22 = 2 :=
  Sporadic.Mathieu.m22_primeRank_three

end CFSG.Quasithin.ChapterA
