module
public import Theory.GroupAction.FourAutomorphismOrbit
public import Theory.GroupTheory.PPerfectHom
public import Mathlib.RepresentationTheory.Basic
public import Theory.Representation.BinaryGroupAction
public import Theory.Representation.BinaryPlaneNormalizer
/-!
# Two-perfect actions on an elementary four-group

A nontrivial image of a two-perfect group in the automorphisms of an
 elementary four-group has order greater than two, so it is transitive
on the three nonidentity elements. The linear version retains the original
binary representation and the actual moving vector.
-/
public section
namespace MulAction
/-- A two-perfect action moving a point of a four-group has its full nonidentity orbit. -/
theorem four_orbit_of_twoPerfect
    {A W : Type*} [Group A] [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (hA : IsPPerfect 2 A) (hW : Nat.card W = 4)
    (f : A →* MulAut W) (x : W) (hx : x ≠ 1)
    (hmove : ∃ a, f a x ≠ x) : ∀ y : W, y ≠ 1 → ∃ a, f a x = y := by
  have hsize : 2 < Nat.card f.range := by
    by_contra hn
    have hpos := Nat.card_pos (α := f.range)
    have hsmall : Nat.card f.range = 1 ∨ Nat.card f.range = 2 := by omega
    have hp : IsPGroup 2 f.range := IsPGroup.of_card_dvd_pow (n := 1) (by
      rcases hsmall with h | h <;> rw [h] <;> decide)
    have hf := hA.hom_eq_one_of_isPGroup hp f.rangeRestrict
    obtain ⟨a, ha⟩ := hmove
    have he : f a = 1 := congrArg Subtype.val (DFunLike.congr_fun hf a)
    exact ha (by rw [he]; rfl)
  intro y hy
  obtain ⟨a, ha⟩ := mem_orbit_iff.mp
    (nonidentity_mem_orbit_of_four_automorphism_subgroup hW f.range hsize x hx y hy)
  change (a : MulAut W) x = y at ha
  obtain ⟨b, hb⟩ := a.property
  exact ⟨b, by simpa only [hb] using ha⟩
end MulAction
namespace Representation
/-- The nonzero orbit of a moving vector in the actual four-element binary module. -/
theorem four_orbit_of_twoPerfect
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (hA : IsPPerfect 2 A) (hW : Nat.card W = 4)
    (ρ : Representation (ZMod 2) A W) (x : W) (hx : x ≠ 0)
    (hmove : ∃ a, ρ a x ≠ x) : ∀ y : W, y ≠ 0 → ∃ a, ρ a x = y := by
  let f : A →* MulAut (Multiplicative W) := {
    toFun a := (LinearEquiv.ofBijective (ρ a) (ρ.apply_bijective a)).toAddEquiv.toMultiplicative
    map_one' := by
      ext w
      change Multiplicative.ofAdd (ρ 1 w.toAdd) = w
      simp
    map_mul' a b := by
      ext w
      change Multiplicative.ofAdd (ρ (a * b) w.toAdd) =
        Multiplicative.ofAdd (ρ a (ρ b w.toAdd))
      rw [map_mul, Module.End.mul_apply] }
  let : IsElementaryAbelian 2 (Multiplicative W) := BinaryGroupAction.elementary
  have hw : Nat.card (Multiplicative W) = 4 := hW
  intro y hy
  obtain ⟨a, ha⟩ := MulAction.four_orbit_of_twoPerfect hA hw f (Multiplicative.ofAdd x) hx
    hmove (Multiplicative.ofAdd y) hy
  exact ⟨a, congrArg Multiplicative.toAdd ha⟩
/-- A nontrivial two-perfect action on a binary plane is transitive on its nonzero vectors. -/
theorem nonzero_orbit_of_twoPerfect_plane
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (hA : IsPPerfect 2 A) (hd : Module.finrank (ZMod 2) W = 2)
    (ρ : Representation (ZMod 2) A W) (hρ : ∃ a, ρ a ≠ 1)
    (x : W) (hx : x ≠ 0) : ∀ y : W, y ≠ 0 → ∃ a, ρ a x = y := by
  let : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have hW : Nat.card W = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
    norm_num
  apply four_orbit_of_twoPerfect hA hW ρ x hx
  by_contra h
  push Not at h
  obtain ⟨a,ha⟩ := hρ
  exact ha (BinaryPlaneNormalizer.twoPerfect_plane_fixed ρ hA hd x hx h a)
end Representation
