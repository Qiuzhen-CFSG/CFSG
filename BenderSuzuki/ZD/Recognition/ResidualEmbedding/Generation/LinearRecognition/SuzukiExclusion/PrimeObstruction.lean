module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Basic
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.GeometryContract
public import Theory.NumberTheory.BinarySuzukiCyclotomic

/-!
# The primitive-prime obstruction in the actual point stabilizer

From the normalizer bound in the local geometry, choose a prime `p` of
binary order `6*(2*m+1)`. It divides `q²-q+1` and does not divide the
actual pair stabilizer. Every nontrivial `p`-subgroup of `M` whose order
divides that cyclotomic factor fails the free split-torus orbit congruence.

This discharges (14D)–(14E) and the numerical part of Lemma 14.4(a),
GLS4, Chapter 2, `refs/KGroup/GLS4/Chapter2.tex`. The Sylow-order and
semiregularity arguments still have to establish the indicated subgroup
order divisor and the contradictory congruence. Construction of the
local geometry remains a separate premise, to be discharged in the
final Suzuki exclusion.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup Theory.NumberTheory.BinarySuzukiCyclotomic
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ} (d : Context Z M z t m)
include d

/-- The source primitive prime and its obstruction, applied to the literal
subgroups of the point stabilizer `M`. -/
public theorem Context.primitive_prime_obstruction (g : LocalGeometry Z M z t m) :
    ∃ p : ℕ, p.Prime ∧ 2 * m + 1 < p ∧ p ≠ 3 ∧
      orderOf (2 : ZMod p) = 6 * (2 * m + 1) ∧
      p ∣ (2 ^ (2 * m + 1)) ^ 2 - 2 ^ (2 * m + 1) + 1 ∧
      ¬ p ∣ Nat.card (residualPairStabilizer M t) ∧
      ∀ R : Subgroup M, IsPGroup p R → R ≠ ⊥ →
        Nat.card R ∣ (2 ^ (2 * m + 1)) ^ 2 - 2 ^ (2 * m + 1) + 1 →
          ¬ (2 ^ (2 * m + 1) - 1) ∣ (Nat.card R - 1) := by
  have hn : 3 ≤ 2 * m + 1 := by have := d.parameter_pos; omega
  obtain ⟨p, hp, hnp, hp3, ho, hdiv, hnot⟩ := primitive_prime_data (by omega : 2 ≤ 2 * m + 1)
  have hD := g.pair_card_dvd
  rw [d.card_residualGenerated] at hD
  refine ⟨p, hp, hnp, hp3, ho, hdiv, fun hd => hnot (hd.trans hD), ?_⟩
  intro R hRp hRne hRc
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hRp.exists_card_eq
  have hkpos : 0 < k := by
    by_contra hn
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero] at hk
    exact hRne (Subgroup.card_eq_one.mp hk)
  rw [hk] at hRc ⊢
  exact prime_power_not_congruent hn ⟨m, by omega⟩ hp hp3 hkpos hRc

end BenderSuzuki.ZD.SuzukiExclusion
