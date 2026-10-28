module

public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.HigherLinear.Reduction
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.HigherLinear.ExceptionalAction

/-!
# Comparing the PSL₄(2) and PSL₅(2) residual rows

The supplied exact covering and table rows exclude all graph A₆ residuals,
the PSL₄(2) root/A₄ pair, and both PSL₅(2) inner rows, using the corrected
order-256 kernel in the j₂ case. The remaining case has equal ambient A₄
residuals and requires the actual exceptional S₈ normalizer action.
`HigherLinear.reduce_to_equal_a4` exposes precisely that remaining branch;
`HigherLinear.higher_linear_excluded` discharges it from the two marked
eight-point actions supplied by the earlier table rows.

Source: Aschbacher–Smith, 16.1.4 and the proof of 16.4.11(2),
combined manuscript (1 March 2004), printed pp.1170–1171 and 1193.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.HigherLinear

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta
open ExceptionalAction
open Theory.SpecificGroups.SymmetricEight.Involutions

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- The PSL₄(2) branch after the exact inner and outer residual rows have been
reduced to the equal-A₄ case.  The two cycle-type clauses are the genuine
marked action clauses from 16.1.4(3),(9); the contradiction is the actual
normalizer action on the two component quotients. -/
theorem four_excluded (d : Contrary T z L g R r) (hZ : center L = ⊥)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 4 2)
    (hin : InnerRow 4 (centralImage L (residual L r)))
    (hout : OuterRow 4
      (centralImage (L.conjBy g) (residual (L.conjBy g) z)))
    (hi : (automorphismPermutationEquiv (componentAlternatingEquiv d hZ hmodel)
      (action (d.setup.sylow_normalizes (d.setup.le_sylow d.mem)))).cycleType =
      {2, 2})
    (ho : (automorphismPermutationEquiv
      (conjugateAlternatingEquiv d hZ hmodel)
      (action d.z_normalizes)).cycleType = {2, 2, 2}) : False := by
  have _hred := reduce_to_equal_a4 d hZ hin hout
  exact equal_a4_excluded d hZ hmodel hi ho

/-- Uniform assembly for the two higher-linear dimensions.  In dimension
four, `hinner` and `houter` provide the exact marked j₂ and exceptional
three-transposition rows.  In dimension five the corrected two-kernel rows
are excluded by `five_excluded`; no false elementary-kernel presentation is
used. -/
theorem higher_linear_excluded (d : Contrary T z L g R r) (hZ : center L = ⊥)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) n 2)
    (hin : InnerRow n (centralImage L (residual L r)))
    (hout : OuterRow n
      (centralImage (L.conjBy g) (residual (L.conjBy g) z)))
    (hinner : ∀ h4 : n = 4,
      (automorphismPermutationEquiv
        (componentAlternatingEquiv d hZ (h4 ▸ hmodel))
        (action (d.setup.sylow_normalizes (d.setup.le_sylow d.mem)))).cycleType =
        {2, 2})
    (houter : ∀ h4 : n = 4,
      (automorphismPermutationEquiv
        (conjugateAlternatingEquiv d hZ (h4 ▸ hmodel))
        (action d.z_normalizes)).cycleType = {2, 2, 2}) : False := by
  rcases hn with h4 | h5
  · subst n
    exact four_excluded d hZ hmodel hin hout (hinner rfl) (houter rfl)
  · subst n
    exact five_excluded d hZ hin hout

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.HigherLinear
