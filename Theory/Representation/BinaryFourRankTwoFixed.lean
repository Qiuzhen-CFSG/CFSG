module
public import Mathlib.RepresentationTheory.Basic
public import Theory.LinearAlgebra.BinaryFourPointStabilizer
public import Theory.Quasithin.CoprimeRank
public import Theory.GroupTheory.PrimeRankElementary

/-!
# Fixed vectors for three-rank two on a binary four-space

A nonzero vector stabilizer in GL₄(2) has order1344, with three-part3.
Faithfulness embeds every fixing subgroup into this stabilizer; a subgroup
of three-rank two therefore has no nonzero fixed vector.

Source: the four-space argument in Aschbacher–Smith C.1.23 and15.3.21,
printed pp.130,1127.
-/
public section
open Subgroup
namespace Representation
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

theorem binaryFour_rankTwo_fixed_eq_zero (ρ : Representation (ZMod 2) D W)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) W = 4)
    (H : Subgroup D) (hr : primeRank 3 H = 2)
    (v : W) (hv : ∀ h : H, ρ h v = v) : v = 0 := by
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let : Finite (W ≃ₗ[ZMod 2] W) :=
    Finite.of_injective (fun a : W ≃ₗ[ZMod 2] W => (a : W → W)) DFunLike.coe_injective
  by_contra hne
  let T := Theory.LinearAlgebra.BinaryFivePointStabilizer.stabilizer v
  have hc : Nat.card T = 1344 := Theory.LinearAlgebra.BinaryFourPointStabilizer.card_stabilizer v hne hd
  have hrT : primeRank 3 T ≤ 1 := by
    apply (primeRank_le_iff_elementary_card_le _).mpr
    intro E hE
    let : IsElementaryAbelian 3 E := hE
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 3 E).exists_card_eq
    have hd : Nat.card E ∣ 3 * 448 := by simpa only [hc] using E.card_subgroup_dvd_card
    have hp : Nat.Coprime (Nat.card E) 448 := by
      rw [hn]
      exact (by decide : Nat.Coprime 3 448).pow_left n
    exact Nat.le_of_dvd (by decide) (hp.dvd_mul_right.mp hd)
  let f := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).toMonoidHom.comp
    (ρ.asGroupHom.comp H.subtype)
  have hfix (h : H) : f h ∈ T := hv h
  let g := f.codRestrict T hfix
  have hi : Function.Injective g := by
    intro x y he
    apply Subtype.ext
    apply hf
    have hh := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).injective
      (congrArg Subtype.val he)
    exact congrArg Units.val hh
  have hh := (_root_.primeRank_le_of_injective 3 g hi).trans hrT
  omega
end Representation
