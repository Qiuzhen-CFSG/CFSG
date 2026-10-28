module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Basic
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Recognition.Inputs

/-!
# Remaining Sylow calculation for the first three-centralizer

The proof of Aschbacher, *Sporadic Groups* (1994), 47.3, printed p.262,
first puts a nonabelian ambient Sylow three-subgroup in C_G(X) and computes
the Sylow two-order there. These are intermediate conclusions to be proved
from 47.1–47.2, not additional assumptions of the source theorem.

The three-subgroup below is literally a Sylow subgroup of G, with its
containment in C_G(X) retained. In particular this contract cannot be
discharged using the later Sylow description obtained from the recognized
A₆ cover. `CoreRecognition` uses these facts to determine the order and
prove perfectness of that cover.
-/

@[expose] public section

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal

variable {G : Type*} [Group G] [Finite G]

/-- The independent Sylow facts preceding the index-six recognition. -/
structure CoreSylowData (D : Seed G) : Prop where
  two_card : ∀ T : Sylow 2 (C D), Nat.card T = 8
  three : ∃ P : Sylow 3 G, (P : Subgroup G) ≤ C D ∧ ¬ IsMulCommutative P

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
