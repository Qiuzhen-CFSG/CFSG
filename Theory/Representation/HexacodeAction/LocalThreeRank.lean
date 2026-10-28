module
public import Theory.Representation.HexacodeAction.CubicLocalModel.Orders.PointStabilizer
public import Theory.Representation.HexacodeAction.CubicLocalModel.Orders.CentralCubicSymmetricFour.KleinReduction
public import Theory.Quasithin.Rank
public import Theory.Quasithin.LocalRank
public import Theory.GroupTheory.PrimeRankElementary
/-!
# Two-local three-rank in the actual triple cover of A₆

The stabilizer of a binary natural-module line maps onto S₄ with central
kernel of order three. Its Sylow three-subgroup has order nine; the checked
hexacode exponent calculation makes it elementary abelian. A normal Klein
four lifts through the cubic kernel, so this rank-two subgroup lies in an
actual ambient two-local.

The generic central-cubic S₄ statements retain the subgroup and map, and
are reusable for other concrete alternating-cover restrictions.

Source: Aschbacher–Smith A.2.12(I.i), printed p.36; the concrete point
stabilizer also occurs in 13.2.1–2, printed pp.876–877.
-/

public section
open Subgroup Theory.GroupTheory
namespace Representation.Hexacode.LocalThreeRank
open Representation.Hexacode.CubicLocalModel.Orders

theorem two_le_primeRank_cubic_s4 {X : Type*} [Group X] [Finite X]
    (f : X →* Equiv.Perm (Fin 4)) (hf : Function.Surjective f)
    (hk : Nat.card f.ker = 3) (h9 : ∀ x : X, x ^ 9 = 1 → x ^ 3 = 1) :
    2 ≤ primeRank 3 X := by
  have hcard : Nat.card X = 72 := by
    have hh := f.ker.card_mul_index
    rw [index_ker, MonoidHom.range_eq_top.mpr hf, card_top, hk,
      Nat.card_perm, Nat.card_fin] at hh
    norm_num at hh
    omega
  let P : Sylow 3 X := Classical.choice inferInstance
  have hcP : Nat.card (P : Subgroup X) = 9 := by
    rw [P.card_eq_multiplicity, hcard]
    rw [show 72 = 3 ^ 2 * 8 by decide,
      Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
    simp [Nat.Prime.factorization Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 8)]
  let : IsMulCommutative (P : Subgroup X) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by simpa using hcP)
  let : IsElementaryAbelian 3 (P : Subgroup X) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Subtype.ext
      apply h9 x
      exact congrArg Subtype.val (by simpa only [hcP] using pow_card_eq_one' (x := x))) }
  exact IsElementaryAbelian.primeRank_ge_of_card (P : Subgroup X) (by simpa using hcP)

theorem two_le_localRank_cubic_s4_subgroup
    {G : Type*} [Group G] [Finite G] (X : Subgroup G)
    (f : X →* Equiv.Perm (Fin 4)) (hf : Function.Surjective f)
    (hk : Nat.card f.ker = 3) (hc : f.ker ≤ center X)
    (h9 : ∀ x : X, x ^ 9 = 1 → x ^ 3 = 1) :
    2 ≤ twoLocalPrimeRank 3 G := by
  obtain ⟨Q, hQn, hQp, hQc, _, _⟩ :=
    CentralCubicSymmetricFour.exists_normal_klein_lift f hf hk hc
  let := hQn
  let R := Q.map X.subtype
  have hRne : R ≠ ⊥ := by
    intro hh
    have hQb := (map_eq_bot_iff_of_injective Q X.subtype_injective).mp hh
    rw [hQb, card_bot] at hQc
    omega
  have hXN : X ≤ normalizer (R : Set G) := by
    have hh := Q.le_normalizer_map X.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  exact (two_le_primeRank_cubic_s4 f hf hk h9).trans
    ((primeRank_mono 3 hXN).trans
      (IsTwoLocal.primeRank_le ⟨R, hRne, hQp.map X.subtype, rfl⟩ 3))

open Representation.Hexacode.CubicLocalModel
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry

theorem hex_even_local_three_rank_ge_two :
    2 ≤ twoLocalPrimeRank 3 Atlas.Codes.HexEvenAutomorphisms :=
  two_le_localRank_cubic_s4_subgroup (stabilizer canonicalLine)
    (symmetricFourMap canonicalLine canonicalLine_finrank)
    (symmetricFourMap_surjective canonicalLine canonicalLine_finrank)
    (symmetricFourMap_kernel_card canonicalLine canonicalLine_finrank)
    (symmetricFourMap_kernel_central canonicalLine canonicalLine_finrank)
    (fun _ hx => stabilizer_cube_eq_one_of_ninth canonicalLine hx)
end Representation.Hexacode.LocalThreeRank
