module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.Basic

/-!
# Model alternatives for the orbit-persistence argument

The rank-one list retains the Fermat/Mersenne restriction inherited from
(E2), even though Lemma 16.2.5 suppresses it in its displayed list. All
alternatives refer to actual group isomorphisms. The covered Suzuki branch
is separate and retains the nontrivial two-core.

These are shared output specifications, not classification assertions.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
(E2) on p.1170 and Lemma 16.2.5 on p.1174.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry
open Subgroup Theory.GroupTheory
universe v

/-- The simple cases with their inherited source parameter restrictions. -/
inductive RankOneComponentModel (L : Type v) [Group L] : Prop
  | linear_even (n : ℕ) (hn : 2 ≤ n) (iso : ClassicalGroup.IsPSL L 2 (2 ^ n))
  | suzuki (m : ℕ) (hm : 1 ≤ m)
      (iso : Nonempty (L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
  | linear_odd (p : ℕ) (hp : IsFermatOrMersennePrime p) (hlarge : 5 ≤ p)
      (iso : ClassicalGroup.IsPSL L 2 p)

/-- The output of the list intersection, retaining the genuine cover. -/
inductive RefinedComponentAlternative (L : Type v) [Group L] : Prop
  | rank_one (model : RankOneComponentModel L)
  | covered_suzuki_eight (nontrivial_core : pCore 2 L ≠ ⊥)
      (iso : Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1))

/-- Forget only the extra restrictions suppressed in the displayed source list. -/
theorem RefinedComponentAlternative.to_componentAlternative
    {L : Type v} [Group L] (h : RefinedComponentAlternative L) :
    ComponentAlternative L := by
  cases h with
  | rank_one model =>
    cases model with
    | linear_even n hn iso => exact .linear_even n hn iso
    | suzuki m hm iso => exact .suzuki m hm iso
    | linear_odd p hp hlarge iso =>
      exact .linear_odd p hp.1 (hp.1.odd_of_ne_two (by omega)) iso
  | covered_suzuki_eight hc iso => exact .covered_suzuki_eight hc iso

end CFSG.Quasithin.Chapter16.CounterexampleGeometry
end
