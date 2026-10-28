module

public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.Reduction
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.FirstRestrictions
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.SecondSeparator
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.SylowAutBound

/-!
# Full binary Ree amalgam rigidity

Every automorphism of the full Sylow overlap factors through separately
compatible automorphisms of the two endpoints. The automorphism upper bound
32768 and first-restriction lower bound 16384 give index at most two. The
constructed second restriction outside the first group then removes every
twist. The marked coordinate isomorphism retains both actual inclusion maps.

This proves the requested Tits-to-full-Ree implication independently of its
Tits premise, and even without faithfulness of the twist. Sylow normalization
therefore upgrades every parabolic equivalence with this full Ree model to
an amalgam isomorphism. The faithful-input application also records the exact
conditional interface for the source assembly owner.

Source: Aschbacher--Smith F.1.11--12, printed pp.262--263. The accompanying
`FullRee/source/README.md` records the exploratory computation and the distinction
between the full Ree model and its marked Tits subamalgam.
The full Ree case is (I)(5) at q = 2, distinct from the Tits case (I)(9).
This finite-model argument invokes no unverified formulation of Fan's theorem;
the source classification and its input alignment remain separate.
-/

public section
namespace Tits.AmalgamRigidity.FullRee
open Theory.GroupTheory RankTwoAmalgam

/-- Every automorphism of the actual full Ree overlap is a product of
separately compatible endpoint restrictions. All finite premises are discharged. -/
theorem factorsThrough (d : MulAut ExceptionalParabolics.FullRee.B) :
    FactorsThrough ExceptionalParabolics.FullRee.amalgam d :=
  factorsThrough_of_bounds sylowAut_card_le firstRestrictions_card_ge
    SecondSeparator.exists_separator d

/-- The requested transfer holds by the stronger unconditional full Ree result. -/
theorem factorsThrough_of_tits
    (_hTits : ∀ d : MulAut ExceptionalParabolics.overlap,
      FactorsThrough ExceptionalParabolics.amalgam d)
    (d : MulAut ExceptionalParabolics.FullRee.B)
    (_hf : Faithful (twistRight ExceptionalParabolics.FullRee.amalgam d)) :
    FactorsThrough ExceptionalParabolics.FullRee.amalgam d :=
  factorsThrough d

/-- Parabolic equivalence recognizes the full Ree amalgam whenever the actual
overlap maps embed Sylow two-subgroups. No faithfulness premise is needed. -/
theorem iso_of_parabolicEquiv
    {L B R : Type*} [Group L] [Group B] [Group R]
    {α : RankTwoAmalgam L B R} (hα : SylowEmbedded 2 α)
    (e : ParabolicEquiv α ExceptionalParabolics.FullRee.amalgam) :
    Nonempty (Iso α ExceptionalParabolics.FullRee.amalgam) :=
  iso_of_twist_factorization hα sylowEmbedded e factorsThrough

/-- The faithful source-input application, with only the Tits factorization
premise retained in its conditional interface. Both inclusion squares are kept. -/
theorem iso_of_tits
    (hTits : ∀ d : MulAut ExceptionalParabolics.overlap,
      FactorsThrough ExceptionalParabolics.amalgam d)
    {L B R : Type*} [Group L] [Group B] [Group R]
    {α : RankTwoAmalgam L B R} (hα : SylowEmbedded 2 α) (hf : Faithful α)
    (e : ParabolicEquiv α ExceptionalParabolics.FullRee.amalgam) :
    Nonempty (Iso α ExceptionalParabolics.FullRee.amalgam) :=
  iso_of_faithful_twist_factorization hα sylowEmbedded hf e
    (factorsThrough_of_tits hTits)

end Tits.AmalgamRigidity.FullRee
