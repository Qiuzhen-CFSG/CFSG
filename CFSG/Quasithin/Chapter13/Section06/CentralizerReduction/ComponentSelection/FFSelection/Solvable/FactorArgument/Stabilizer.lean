module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.FactorArgument.Product

/-!
# The cubic-factor alternative inside its actual normalizer

A factor whose normalizer has index at most two is normalized by L_v*,
since L_v* is two-perfect. The normalizer is normal in G_v*, so the
intersection of T_v* with it is Sylow there and still normalizes L_v*.
The normal-S₃ theorem applies in this subgroup: the cubic order bound
forces L_v* to equal the factor residual or to centralize the factor.

The bound on the normalizer index remains explicit. Establishing it from
the one- or two-factor product and ruling out simultaneous centralization
are the remaining inputs to the projection argument. No ambient direct
product decomposition or ambient normality of an individual factor is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.6.13, printed p.929.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.FactorArgument
variable {G : Type*} [Group G] [Finite G]

/-- The literal L_v* is a factor residual or centralizes that factor,
using the induced Sylow subgroup of its normalizer. -/
theorem factor_alternative_of_small_normalizer_index (L T : Subgroup G) (z v : G)
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hcard : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    {X : Subgroup (Gstar z v)} (d : NormalS3Decomposition z v X)
    (i : Fin d.count) (hindex : (normalizer (d.factor i : Set (Gstar z v))).index ≤ 2) :
    starImage z v (Lv L v) = d.factorResidual i ∨
      starImage z v (Lv L v) ≤ centralizer (d.factor i : Set (Gstar z v)) := by
  let P := normalizer (d.factor i : Set (Gstar z v))
  let B := starImage z v (Lv L v)
  have hcases : P.index = 1 ∨ P.index = 2 := by
    have hp := P.index_ne_zero_of_finite
    change P.index ≤ 2 at hindex
    omega
  let hPn : P.Normal := by
    rcases hcases with h | h
    · rw [index_eq_one.mp h]; infer_instance
    · exact normal_of_index_eq_two h
  have hpq : IsPGroup 2 (Gstar z v ⧸ P) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [← index_eq_card]
    rcases hcases with h | h <;> rw [h] <;> decide
  have hBP : B ≤ P := by
    let f := (QuotientGroup.mk' P).comp B.subtype
    have hf := (starLv_twoPerfect L z v).hom_eq_one_of_isPGroup hpq f
    intro b hb
    apply (QuotientGroup.eq_one_iff b).mp
    exact congrArg (fun g : B →* Gstar z v ⧸ P => g ⟨b, hb⟩) hf
  obtain ⟨R, hR⟩ := exists_starSylow T z v S hS
  obtain ⟨Q, hQ⟩ := R.exists_subgroupOf_eq_of_normal P
  have hQB : (Q : Subgroup P) ≤ normalizer (B.subgroupOf P : Set P) := by
    rw [hQ, ← subgroupOf_normalizer_eq hBP]
    exact comap_mono (hR ▸ starTv_normalizes_starLv L T z v hL)
  have hpB : IsPPerfect 2 (B.subgroupOf P) :=
    (starLv_twoPerfect L z v).of_surjective
      (subgroupOfEquivOfLe hBP).symm.toMonoidHom (subgroupOfEquivOfLe hBP).symm.surjective
  have hcB : ∃ n : ℕ, Nat.card (B.subgroupOf P) ∣ 3 * 2 ^ n := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBP).toEquiv]
    exact starLv_card_dvd L z v hcard
  have hK : ((d.factor i).subgroupOf P).Normal :=
    normal_subgroupOf_of_le_normalizer le_rfl
  rcases Theory.GroupTheory.NormalSymmetricThreeMarked.eq_residual_or_centralizes_of_card_dvd
    ((d.factor i).subgroupOf P) ((subgroupOfEquivOfLe (d.factor i).le_normalizer).trans (d.model i))
    Q (B.subgroupOf P) hpB hQB hcB with he | hc
  · left
    have hh := congrArg (fun U : Subgroup P => U.map P.subtype) he
    rw [map_subgroupOf_eq_of_le hBP, map_embedded_pResidual,
      map_subgroupOf_eq_of_le (d.factor i).le_normalizer] at hh
    exact hh
  · right
    intro b hb k hk
    exact congrArg Subtype.val
      (hc (show (⟨b, hBP hb⟩ : P) ∈ B.subgroupOf P from hb)
        ⟨k, (d.factor i).le_normalizer hk⟩ hk)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.FactorArgument
end
