module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Exceptional.SylowCubic.Certificate
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.FactorArgument.Basic

/-!
# Sylow-normalized two-perfect subgroups in the parity actor

Let P be a Sylow two-subgroup of the literal parity-matched subgroup of
S₆ × S₃. If P normalizes a two-perfect subgroup R, |R| divides 3 · 2ⁿ,
and R has nontrivial three-point image, then R is exactly the kernel of
the six-point projection.

Two-perfectness first supplies a cubic with nontrivial three-point image.
The kernel-checked six-word certificate and Sylow conjugacy show that a
nontrivial six-point coordinate would force an order-nine subgroup in R.
The order bound rules this out. The resulting canonical cubic lies in R,
and two-perfectness kills the remaining two-group quotient.

The final application retains the actual homomorphism from the star quotient
and the supplied Sylow image. The source-action construction and its nontrivial
three-point image remain with the parent assembly of 13.6.13.
Source: Aschbacher–Smith, B.5.6(4), B.5.7 and 13.6.13, pp.105–106 and 929.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SixPoint

/-- The cubic restriction for the literal parity actor, with no finite-certificate premise. -/
theorem eq_cubic_of_sylow_normalized
    (P : Sylow 2 Actor) (R : Subgroup Actor)
    (hn : (P : Subgroup Actor) ≤ normalizer (R : Set Actor))
    (hp : IsPPerfect 2 R) {n : ℕ} (hc : Nat.card R ∣ 3 * 2 ^ n)
    (hne : R.map secondProjection ≠ ⊥) : R = cubic :=
  eq_cubic_of_closure_restriction (fun P r hthree hsecond =>
    (closure_restriction P r hthree hsecond).imp_right Or.inl) P R hn hp hc hne

/-- Apply the restriction to the actual star image and its literal Sylow image.
This discharges the finite-group identification in the outer branch of 13.6.13. -/
theorem starLv_map_eq_cubic
    {G : Type*} [Group G] [Finite G] (L T : Subgroup G) (z v : G)
    (f : Gstar z v →* Actor) (P : Sylow 2 Actor)
    (hP : (starImage z v (Tv T v)).map f = (P : Subgroup Actor))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hcard : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (hne : ((starImage z v (Lv L v)).map f).map secondProjection ≠ ⊥) :
    (starImage z v (Lv L v)).map f = cubic := by
  let R := starImage z v (Lv L v)
  have hp : IsPPerfect 2 (R.map f) :=
    (FactorArgument.starLv_twoPerfect L z v).of_surjective
      (f.subgroupMap R) (by
        rintro ⟨y, x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩)
  obtain ⟨n, hn⟩ := FactorArgument.starLv_card_dvd L z v hcard
  have hc : Nat.card (R.map f) ∣ 3 * 2 ^ n := (card_map_dvd R f).trans hn
  have hnorm : (P : Subgroup Actor) ≤ normalizer (R.map f : Set Actor) := by
    rw [← hP]
    exact (map_mono (FactorArgument.starTv_normalizes_starLv L T z v hL)).trans
      (le_normalizer_map f)
  exact eq_cubic_of_sylow_normalized P (R.map f) hnorm hp hc hne

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SixPoint
