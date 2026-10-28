module
public import Theory.SpecificGroups.Triality.BinarySolvableCubic
public import Theory.SpecificGroups.Triality.RadicalCoordinates.FullLevi.Normalization
import all Theory.SpecificGroups.Triality.BinaryThreeFreeSylow

/-!
# A permuting cubic which moves a binary triality parabolic

In the genuine graph-field group ³D₄(2), the central Levi has order six.
Its cubic complements the positive Sylow in the central local factor,
so the two subgroups permute. The Borel torus of order seven centralizes
this Levi: its permutation action on the six Levi elements is trivial.
It is an odd Hall subgroup of the actual Borel. Nevertheless the cubic
moves the arms parabolic, since their intersection is the three-free Borel.

Thus Sylow permutability does not force parabolic normalization, even
with a cyclic odd actor centralized by a Borel Hall subgroup. This is an
intrinsic model calculation; it does not supply the ambient Input or
CartanPair of the quasithin source theorem. The source-facing application
with the literal residual is in
RankOneModuleGenericExceptionalCartanLocalBinaryObstruction.

Source: the inference in Aschbacher--Smith 5.1.13, printed p.636,
refs/quasithin.pdf; GLS3 §§2.3--2.6 for the graph-field parabolics.
The internal import reuses the central local-factor order calculation
without changing BinaryThreeFreeSylow's public boundary.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
namespace Triality.Standard.BinaryParabolicObstruction
open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.ConcreteBruhat
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "M" => BinaryCarrier 1 Nat.zero_lt_one

private theorem central_levi_card : Nat.card (levi P .central) = 6 := by
  let e := (leviCentralEquivPSL2 P rfl).trans
    (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 1)).symm
  rw [Nat.card_congr e.toEquiv, GorensteinWalter.sl2_card_formula,
    GaloisField.card 2 1 (by decide)]
  norm_num

private theorem torus_card : Nat.card (torus P) = 7 := by
  rw [TorusCoordinates.card_torus P rfl]
  rfl

private theorem torus_centralizes_levi :
    torus P ≤ centralizer (levi P .central : Set M) := by
  let C := levi P .central
  let f := (MulAut.toPerm C).comp
    (C.normalizerMonoidHom.comp (inclusion
      (RadicalCoordinates.torus_le_normalizer_levi P rfl .central)))
  have hc : Nat.Coprime (Nat.card (torus P)) (Nat.card (Equiv.Perm C)) := by
    rw [torus_card, Nat.card_perm, central_levi_card]
    decide
  have hc1 : Nat.card f.range = 1 := Nat.eq_one_of_dvd_coprimes hc
    (card_range_dvd f) f.range.card_subgroup_dvd_card
  have hf (t : torus P) : f t = 1 :=
    mem_bot.mp ((f.range.eq_bot_of_card_eq hc1) ▸ (show f t ∈ f.range from ⟨t,rfl⟩))
  intro t ht x hx
  have he := congrArg (fun s : Equiv.Perm C => (s ⟨x,hx⟩ : M)) (hf ⟨t,ht⟩)
  change t*x*t⁻¹ = x at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

private theorem permutes_of_card (D : Subgroup M) (hD : Nat.card D = 3)
    (hDK : D ≤ localFactor P .central) :
    (D : Set M) * unipotent P = (unipotent P : Set M) * D := by
  let K := localFactor P .central
  have hUK : unipotent P ≤ K := sylow_le_localFactor P .central (unipotentSylow P rfl)
    ((unipotent_le_borel P).trans (borel_le_parabolic P .central))
  have hDK' : D ≤ K := hDK
  let DK := D.subgroupOf K
  let UK := (unipotent P).subgroupOf K
  have hcD : Nat.card DK = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hDK).toEquiv).trans hD
  have hcU : Nat.card UK = 4096 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUK).toEquiv).trans (card_unipotent_binary P rfl)
  have hcomp : DK.IsComplement' UK := isComplement'_of_coprime
    (by rw [hcD,hcU,BinaryThreeFreeSylow.central_local_card])
    (by rw [hcD,hcU]; decide)
  have he : (DK : Set K) * UK = (UK : Set K) * DK := hcomp.mul_eq.trans hcomp.symm.mul_eq.symm
  have hh := congrArg (Set.image K.subtype) he
  simpa only [Set.image_mul, ← coe_map, DK, UK, map_subgroupOf_eq_of_le hDK',
    map_subgroupOf_eq_of_le hUK] using hh

private theorem torus_hall :
    IsHallSubgroup OddHall.oddPrimes ((torus P).subgroupOf (borel P)) := by
  let B := (torus P).subgroupOf (borel P)
  have hc : Nat.card B = 7 :=
    (Nat.card_congr (subgroupOfEquivOfLe (torus_le_borel P)).toEquiv).trans torus_card
  have hi : B.index = 4096 := by
    have he := B.card_mul_index
    rw [hc, FixedCellCount.card_borel] at he
    norm_num [binaryParameters_q] at he
    omega
  constructor
  · intro p hp he
    rw [hc] at hp
    have hp7 : (p : ℕ) = 7 := Nat.prime_eq_prime_of_dvd_pow p.property (by decide)
      (by simpa using hp : (p : ℕ) ∣ 7^1)
    change (p : ℕ) = 2 at he
    omega
  · intro p hp hp2
    rw [hi] at hp
    exact hp2 (Nat.prime_eq_prime_of_dvd_pow p.property Nat.prime_two
      (by simpa using hp : (p : ℕ) ∣ 2^12))

/-- The literal binary triality parabolics refute the unqualified
Sylow-permutability implication, even with a cyclic cubic centralized by
the Borel Hall torus. This asserts no original ambient Input or CartanPair. -/
theorem compatible_cubic_not_normalizes_arms :
    ∃ D : Subgroup M, Nat.card D = 3 ∧ IsCyclic D ∧
      D ≤ localFactor P .central ∧
      (D : Set M) * unipotent P = (unipotent P : Set M) * D ∧
      torus P ≤ centralizer (D : Set M) ∧
      IsHallSubgroup OddHall.oddPrimes ((torus P).subgroupOf (borel P)) ∧
      unipotent P ≤ normalizer (parabolic P .arms : Set M) ∧
      ¬ D ≤ normalizer (parabolic P .arms : Set M) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := levi P .central) 3
    (by rw [central_levi_card]; decide)
  let D := (zpowers x).map (levi P .central).subtype
  have hDL : D ≤ levi P .central := map_subtype_le _
  have hD : Nat.card D = 3 := by
    rw [card_map_of_injective (levi P .central).subtype_injective, Nat.card_zpowers,hx]
  have hDK := hDL.trans (RadicalCoordinates.levi_le_localFactor P rfl .central)
  exact ⟨D,hD,isCyclic_of_prime_card hD,hDK,permutes_of_card D hD hDK,
    torus_centralizes_levi.trans (centralizer_le hDL),torus_hall,
    ((unipotent_le_borel P).trans (borel_le_parabolic P .arms)).trans
      (parabolic P .arms).le_normalizer,
    Triality.Standard.BinarySolvableEscape.cubic_not_normalizes_arms D hD
      (hDK.trans (localFactor_le_parabolic P .central))⟩

end Triality.Standard.BinaryParabolicObstruction
