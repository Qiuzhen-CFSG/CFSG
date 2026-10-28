module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.PrimeCore.CenterPreimage
public import Theory.GroupTheory.GeneralizedFitting.PerfectCentralSemisimple

/-!
# The central-kernel step of A.2.11

Apply the intrinsic perfect-cover lifting theorem to the original offending
ambient group. Its perfectness follows from minimal covering. Consequently,
once the source rank argument centralizes the chosen normal Sylow kernel and
induction identifies its quotient as semisimple, the original group is
semisimple as well. Neither of those earlier conclusions is inferred merely
from a quotient shape.

Source: Aschbacher–Smith A.2.11, printed p.35.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
    [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

/-- The literal central Sylow quotient makes the original minimal covering
semisimple, with its perfectness discharged by A.2.8. -/
theorem CounterexampleToTheoremA.isSemisimple_of_central_quotient
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (N : Subgroup G) [N.Normal] (hN : N ≤ center G)
    (hquot : IsSemisimple (G ⧸ N)) : IsSemisimple G := by
  let f : PerfectCentralCovering.Cover G (G ⧸ N) :=
    { toMonoidHom := QuotientGroup.mk' N
      surjective := QuotientGroup.mk'_surjective N
      isPerfect := h.isPerfect ih
      ker_le_center := by simpa only [QuotientGroup.ker_mk'] using hN }
  exact f.semisimple hquot

end CFSG.Quasithin.ChapterA.Section02
