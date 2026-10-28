module
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.Quasithin.CoprimeRank
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.PrimeRankCubeFree
/-!
# Three-rank of a plane stabilizer in the binary four-space

The actual parabolic quotient by its two-core is GL₂(2) × GL₂(2), hence
S₃ × S₃. Each factor contains a cubic and the product order has no factor
27, giving exact three-rank two. Odd rank lifts through the two-core.

Source: Aschbacher–Smith, 13.7.6(1), printed p.939.
-/
public section
open Subgroup Theory.GroupTheory
namespace BinaryLinear.FourPlaneRank
open SmallParabolicLevi OuterCyclic
private theorem symmetric_pair_rank :
    primeRank 3 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) = 2 := by
  apply le_antisymm
  · apply primeRank_le_two_of_cube_not_dvd
    rw [Nat.card_prod,Nat.card_perm,Nat.card_fin]
    decide
  · rw [primeRank_prod_eq_add]
    have hne : primeRank 3 (Equiv.Perm (Fin 3)) ≠ 0 := by
      intro hz
      have hn := PrimeRank.eq_zero_iff_not_dvd_card.mp hz
      rw [Nat.card_perm,Nat.card_fin] at hn
      exact hn (by decide)
    omega

/-- Every two-dimensional subspace of the binary four-space has three-rank-two stabilizer. -/
theorem parabolic_rank {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (hd : Module.finrank (ZMod 2) V = 4)
    (W : Submodule (ZMod 2) V) (hW : Module.finrank (ZMod 2) W = 2) :
    primeRank 3 (parabolic W) = 2 := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (BinaryLinear.GL V) := Finite.of_injective
    (fun g : BinaryLinear.GL V => (g : V → V)) DFunLike.coe_injective
  have hQ : Module.finrank (ZMod 2) (V ⧸ W) = 2 := by
    have h := W.finrank_quotient_add_finrank
    rw [hW,hd] at h
    omega
  let a : W ≃ₗ[ZMod 2] Space 2 := LinearEquiv.ofFinrankEq _ _ (by simpa [Space] using hW)
  let b : (V ⧸ W) ≃ₗ[ZMod 2] Space 2 := LinearEquiv.ofFinrankEq _ _ (by simpa [Space] using hQ)
  let e := (quotientTwoCoreEquivOfCoordinates W a b).trans
    (linearTwoEquivSymmetricThree.prodCongr linearTwoEquivSymmetricThree)
  rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide)
    (pCore 2 (parabolic W)) pCore_isPGroup,primeRank_equiv 3 e]
  exact symmetric_pair_rank
end BinaryLinear.FourPlaneRank
