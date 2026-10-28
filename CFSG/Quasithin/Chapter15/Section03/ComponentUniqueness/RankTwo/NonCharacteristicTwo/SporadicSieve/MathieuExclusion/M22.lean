module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion.Seed
public import Theory.Mathieu.M22.Properties.SolvableSylowOvergroups

/-!
# Exclusion of M₂₂ from the rank-two component configuration

The actual solvable image of Y₊ has order divisible by nine. Its normalizer
contains a Sylow two-subgroup, so the native solvable-normal-seed coverage
in M₂₂ forces that normalizer to have order 384. This is impossible.
The calculation occurs inside the component; it applies to every extension
acting on that component, including the full automorphism group.

Source: Aschbacher--Smith, 15.3.41--42, printed p.1138; GLS3 Table 5.3c.
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion

/-- The actual M₂₂ model, with every possible outer action, is excluded. -/
theorem not_m22 {G : Type*} [Group G] [Finite G]
    {I L M Y S : Subgroup G} [(L.subgroupOf I).Normal]
    (d : ComponentSetup I L M Y S) (e : L ⧸ pCore 2 L ≃* M22) : False := by
  let D := seed (Y := Y) e
  let X := normalizer (D : Set M22)
  have h9 : 9 ∣ Nat.card D := seed_nine_dvd d e
  have hc := M22SolvableSylow.card_eq_384_of_solvable_normal_three X D D.le_normalizer
    (normal_subgroupOf_of_le_normalizer (le_refl X)) (seed_solvable d e)
    ((by decide : 3 ∣ 9).trans h9) (seed_sylow d e)
  have hd := h9.trans (card_dvd_of_le D.le_normalizer)
  rw [hc] at hd
  norm_num at hd

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion
