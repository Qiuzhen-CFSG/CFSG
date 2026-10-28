module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Flags.Coordinates
public import Theory.Representation.BinaryPermutation.FiveAction
public import Mathlib.GroupTheory.Sylow

/-!
# Orbit geometry for invariant five-point flags

The nonsingular vectors of the even-weight core form an orbit of length ten
under every subgroup containing A₅. Hence a Sylow two-subgroup fixes only
singular vectors. A certificate on the 32 binary words supplies simultaneous
coordinates for a singular point and a nonsingular complementary pair.
Only thirty explicit coordinate permutations enter this certificate.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Notation 13.2.1
(p.877), the local index calculation in 13.2.6 (p.879), and the marking on p.926.
-/

@[expose] public section
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module.FlagCoordinates
open Subgroup BinaryPermutation BinaryPermutation.FiveGeometry BinaryPermutation.FiveCentralizerGeometry
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module.FlagCoordinates.SylowCalculation

private def weight (x : Space) : ℕ := (Finset.univ.filter fun i => x.val i ≠ 0).card

private theorem weight_invariant (g : Perm) (x : Space) : weight (rho g x) = weight x := by
  apply Finset.card_bij (fun i _ => g.symm i)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ h
    exact g.symm.injective h
  · intro j hj
    refine ⟨g j, ?_, g.symm_apply_apply j⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change x.val (g.symm (g j)) ≠ 0
    simpa only [Equiv.symm_apply_apply] using (Finset.mem_filter.mp hj).2

/-- Permutations preserve the quadratic form on the five-point core. -/
theorem form_invariant (g : Perm) (x : Space) : form (rho g x) = form x := by
  have hi : rho g x = 0 ↔ x = 0 := by
    constructor
    · intro h
      have he := (coordinateEquiv g).injective (show coordinateEquiv g (Multiplicative.ofAdd x) =
        coordinateEquiv g 1 by simpa using congrArg Multiplicative.ofAdd h)
      exact he
    · rintro rfl; exact map_zero _
  have hw := weight_invariant g x
  change (Finset.univ.filter fun i => (rho g x).val i ≠ 0).card =
    (Finset.univ.filter fun i => x.val i ≠ 0).card at hw
  have hq : form (rho g x) = 0 ↔ form x = 0 := by
    rw [singular_iff, singular_iff, hi, hw]
  exact (show ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b by decide) _ _ hq

private theorem nonsingular_card : Nat.card {x : Space // form x ≠ 0} = 10 := by
  let e : {x : Space // form x ≠ 0} ≃
      {x : Full (Fin 5) // (∑ i, x i) = 0 ∧
        (∑ i : Fin 5, ∑ j : Fin 5 with i < j, x i * x j) ≠ 0} :=
    { toFun x := ⟨x.val.val, x.val.property, x.property⟩
      invFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide

/-- The literal restriction of the coordinate action to a permutation subgroup. -/
abbrev vectorAction (H : Subgroup Perm) : MulAction H Space where
  smul h x := rho h.val x
  one_smul _ := rfl
  mul_smul h k x := by
    change rho (h.val * k.val) x = rho h.val (rho k.val x)
    rw [map_mul, Module.End.mul_apply]

/-- The nonsingular orbit has ten elements for every overgroup of A₅. -/
theorem nonsingular_index (H : Subgroup Perm) (hH : alternatingGroup (Fin 5) ≤ H)
    (x : Space) (hx : form x ≠ 0) : (stabilizer H x).index = 10 := by
  let := vectorAction H
  have horbit : MulAction.orbit H x = {y : Space | form y ≠ 0} := by
    ext y
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨h, rfl⟩
      change form (rho h.val x) ≠ 0
      rwa [form_invariant]
    · intro hy
      have hn (w : Space) (hw : form w ≠ 0) : w ≠ 0 := by
        rintro rfl
        exact hw (map_zero _)
      have he : form x = form y :=
        (show ∀ a b : ZMod 2, a ≠ 0 → b ≠ 0 → a = b by decide) _ _ hx hy
      obtain ⟨g, hg⟩ := exists_even_transport x y (hn x hx) (hn y hy) he
      exact ⟨⟨g.val, hH g.property⟩, hg⟩
  change (MulAction.stabilizer H x).index = 10
  rw [MulAction.index_stabilizer, horbit, ← Nat.card_coe_set_eq]
  exact nonsingular_card

/-- A Sylow-fixed vector is singular, since its stabilizer has odd index. -/
theorem sylow_fixed_singular (H : Subgroup Perm) (hH : alternatingGroup (Fin 5) ≤ H)
    (P : Sylow 2 H) (x : Space)
    (hx : ∀ p : H, p ∈ (P : Subgroup H) → rho p.val x = x) : form x = 0 := by
  by_contra hn
  have hle : (P : Subgroup H) ≤ stabilizer H x := hx
  have hd := Subgroup.index_dvd_of_le hle
  rw [nonsingular_index H hH x hn] at hd
  exact P.not_dvd_index ((by decide : 2 ∣ 10).trans hd)

private def rotation : Perm :=
  Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4

private def flagPermutation (i : Fin 5) (j : Fin 3) (t : Bool) : Perm :=
  rotation ^ i.val * Equiv.swap 1 ⟨j.val + 1, by omega⟩ *
    (if t then Equiv.swap 0 2 * Equiv.swap 1 3 else 1)

private theorem flag_certificate : ∀ x y : Full (Fin 5),
    (∑ i, x i) = 0 → (∑ i, y i) = 0 → x ≠ 0 →
    (∑ i : Fin 5, ∑ j : Fin 5 with i < j, x i * x j) = 0 →
    (∑ i : Fin 5, ∑ j : Fin 5 with i < j, y i * y j) ≠ 0 →
    (∑ i : Fin 5, ∑ j : Fin 5 with i < j, (x + y) i * (x + y) j) ≠ 0 →
    ∃ i : Fin 5, ∃ j : Fin 3, ∃ t : Bool,
      representation (Fin 5) (flagPermutation i j t) z.val = x ∧
      representation (Fin 5) (flagPermutation i j t) v.val = y := by decide

/-- Simultaneously mark a singular point and its nonsingular complementary pair. -/
theorem exists_flag_permutation (x y : Space) (hx : x ≠ 0)
    (hqx : form x = 0) (hqy : form y ≠ 0) (hqxy : form (x + y) ≠ 0) :
    ∃ g : Perm, rho g z = x ∧ rho g v = y := by
  obtain ⟨i, j, t, hi, hj⟩ := flag_certificate x.val y.val x.property y.property
    (fun h => hx (Subtype.ext h)) hqx hqy hqxy
  exact ⟨flagPermutation i j t, Subtype.ext hi, Subtype.ext hj⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module.FlagCoordinates.SylowCalculation
