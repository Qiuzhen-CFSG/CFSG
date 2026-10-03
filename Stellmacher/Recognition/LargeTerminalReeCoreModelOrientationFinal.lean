module

public import Stellmacher.Recognition.LargeTerminalInvertingSylowIdentification

/-!
# Actual terminal core orientation

The terminal five-fixed configuration supplies a concrete order-four element
of the second two-core and its marked square.  Once the supplied core
identification sends these elements to `Core.root 2` and `Core.root 9`, the
native terminal extension argument excludes inversion by every element of the
second local group.  This wrapper keeps all of the geometric hypotheses and
the actual identification explicit for the downstream fusion theorem.

Sources: Thompson VI, pp.629--630, and the verified neighboring-core
calculation in `LargeTerminalInvertingSylowIdentification`.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u

/-- The actual terminal core identification excludes local inversion of the
marked order-four root.  The proof uses the native neighboring-parabolic
extension, so it retains the original terminal context and all marked data.
-/
public theorem LargeTerminalContext.five_fixed_four_no_local_inversion
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (_hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (_hcyc : IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (_hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (t z : twoCoreIn ctx.second) (ht4 : orderOf (t : G) = 4)
    (htsq : t ^ 2 = z) (hz2 : orderOf (z : G) = 2)
    (hzgen : zpowers (z : G) = omegaOneCenter (S : Subgroup G))
    (htgen : zpowers (t : G) =
      twoCoreIn ctx.second ⊓ centralizer (A : Set G))
    (eQ : twoCoreIn ctx.second ≃* ReeTwo.Core)
    (het : eQ t = ReeTwo.Core.root 2)
    (hez : eQ z = ReeTwo.Core.root 9) :
    ∀ b ∈ ctx.second, b * (t : G) * b⁻¹ ≠ (t : G)⁻¹ := by
  intro b hb
  exact ctx.ree_no_local_inversion_of_marked_core hS A hA hAP hcard
    t z ht4 htsq hz2 hzgen htgen eQ het hez b hb

end Stellmacher.Recognition
