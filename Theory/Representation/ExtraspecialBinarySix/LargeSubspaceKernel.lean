module
public import Theory.Representation.ExtraspecialBinarySix.FixedPlanes

/-!
# Pointwise stabilizers of large subspaces in the extraspecial six-space

In a faithful binary representation of an extraspecial group of order 27
and degree six, a subspace of dimension greater than two has trivial
pointwise stabilizer in that group. A nontrivial three-group kernel contains
a cubic; a central cubic has no fixed vectors and a noncentral cubic fixes
exactly a plane.

This supplies the faithful moving-space comparison in the replacement
argument for Aschbacher--Smith 15.1.24(1), printed p.1101.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.ExtraspecialBinarySix
variable {D U : Type*} [Group D] [Finite D]
  [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]

/-- Every subspace of dimension at least three has trivial pointwise stabilizer. -/
theorem large_subspaceKernel_eq_bot
    (ρ : Representation (ZMod 2) D U) (hf : Function.Injective ρ)
    (P : Subgroup D) [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (hd : Module.finrank (ZMod 2) U = 6)
    (W : Submodule (ZMod 2) U) (hW : 2 < Module.finrank (ZMod 2) W) :
    subspaceKernel ρ W P = ⊥ := by
  let σ := ρ.comp P.subtype
  have hσ : Function.Injective σ := hf.comp P.subtype_injective
  let : IsIrreducible σ := RankTwo.ExtraspecialModel.irreducible_of_faithful_six σ hσ hP hd
  have hz : fixedSpace ρ ((center P).map P.subtype) = ⊥ := by
    rw [←fixedSpace_comp_map]
    change invariants (σ.comp (center P).subtype) = ⊥
    by_contra hn
    have hh := Representation.le_ker_of_normal_invariants_ne_bot σ (center P) hn
    have hb : center P = ⊥ := bot_unique (by
      simpa only [(MonoidHom.ker_eq_bot_iff σ).mpr hσ] using hh)
    have hc := IsExtraspecial.center_order_p 3 P
    rw [hb,card_bot] at hc
    omega
  let K := subspaceKernel ρ W P
  by_contra hk
  have hKP : K ≤ P := fun _ hx => hx.1
  have hpK := (IsExtraspecial.isPGroup 3 P).to_le hKP
  have hkcard : 3 ∣ Nat.card K := hpK.card_eq_or_dvd.resolve_left
    (fun hc => hk (card_eq_one.mp hc))
  obtain ⟨y,hy⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 hkcard
  let x : P := ⟨y,hKP y.property⟩
  have hx : orderOf x = 3 := by
    rw [←orderOf_injective P.subtype P.subtype_injective x]
    exact (orderOf_injective K.subtype K.subtype_injective y).trans hy
  let X := zpowers x
  have hcX : Nat.card X = 3 := by rw [Nat.card_zpowers,hx]
  have hXK : X.map P.subtype ≤ K := by
    apply map_le_iff_le_comap.mpr
    exact zpowers_le.mpr y.property
  have hfix : W ≤ fixedSpace ρ (X.map P.subtype) := by
    intro w hw a
    exact (hXK a.property).2 w hw
  by_cases he : X = center P
  · rw [he,hz] at hfix
    have hb : W = ⊥ := bot_unique hfix
    rw [hb,finrank_bot] at hW
    omega
  · have hdim := (noncentral_cubic_planes ρ hf P hP hd X hcX he).1
    have hb := Submodule.finrank_mono hfix
    rw [hdim] at hb
    omega
end Representation.ExtraspecialBinarySix
