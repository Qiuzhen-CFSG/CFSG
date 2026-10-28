module

public import Theory.Representation.SL2.PairedCubicAxes
public import Theory.Representation.BinaryOffender.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Literal Cartan-axis alignment in the natural A₅ generation branch

The source has a torus D = D₁ × D₂ of exponent three and an order-three
Cartan factor P with a nonzero fixed space. Its actual natural coordinates
force P into a coordinate kernel. The prescribed kernels inside D are the
opposite axes, and their equal orders give literal subgroup equality.
The fixed vectors need only embed in the paired natural module; no splitting
of an earlier central cover or identification of the whole alpha module with
that paired module is assumed.

Source: Aschbacher–Smith10.2.3(4), printed p.746. The original E.2.3 placement,
fixed-space dimension and marked coordinate maps remain earlier source inputs.
-/

public section

open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10

variable {G F : Type*} [Group G] [Finite G] [Field F] [CharP F 2]

/-- A Cartan subgroup of order three fixing a nonzero paired natural vector
is literally one of the prescribed order-three torus axes. -/
theorem source_natural_cartan_eq_axis
    (D D₁ D₂ P : Subgroup G) (q₁ q₂ : D →* SL(2,F))
    (hPD : P ≤ D) (hD : ∀ d : D, d ^ 3 = 1)
    (haxis₁ : q₂.ker.map D.subtype = D₁) (haxis₂ : q₁.ker.map D.subtype = D₂)
    (hP : Nat.card P = 3) (hD₁ : Nat.card D₁ = 3) (hD₂ : Nat.card D₂ = 3)
    (v : (Fin 2 → F) × (Fin 2 → F)) (hv : v ≠ 0)
    (hfix : ∀ p : D, (p : G) ∈ P →
      ((q₁ p).val *ᵥ v.1, (q₂ p).val *ᵥ v.2) = v) :
    P = D₁ ∨ P = D₂ := by
  rcases Representation.SL2.PairedCubicAxes.le_kernel_or_le_kernel_of_cube_eq_one
      q₁ q₂ (P.subgroupOf D) (fun p _ => hD p) v hv hfix with hk | hk
  · right
    apply eq_of_le_of_card_ge
    · intro p hp
      rw [← haxis₂]
      exact mem_map.mpr ⟨⟨p,hPD hp⟩,hk hp,rfl⟩
    · rw [hD₂,hP]
  · left
    apply eq_of_le_of_card_ge
    · intro p hp
      rw [← haxis₁]
      exact mem_map.mpr ⟨⟨p,hPD hp⟩,hk hp,rfl⟩
    · rw [hD₁,hP]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  [Algebra (ZMod 2) F]

/-- Application to the actual E.2.3 fixed space, through an injective natural
coordinate map. Its positive binary dimension supplies the common fixed
vector required for Cartan-axis alignment. -/
theorem source_natural_cartan_eq_axis_of_fixed_finrank_pos
    (D D₁ D₂ P : Subgroup G) (ρ : Representation (ZMod 2) D V)
    (q₁ q₂ : D →* SL(2,F))
    (hPD : P ≤ D) (hD : ∀ d : D, d ^ 3 = 1)
    (haxis₁ : q₂.ker.map D.subtype = D₁) (haxis₂ : q₁.ker.map D.subtype = D₂)
    (hP : Nat.card P = 3) (hD₁ : Nat.card D₁ = 3) (hD₂ : Nat.card D₂ = 3)
    (c : V →ₗ[ZMod 2] ((Fin 2 → F) × (Fin 2 → F)))
    (hc : Function.Injective c)
    (he : ∀ p : D, (p : G) ∈ P → ∀ x, c (ρ p x) =
      ((q₁ p).val *ᵥ (c x).1, (q₂ p).val *ᵥ (c x).2))
    (hfixed : 0 < Module.finrank (ZMod 2)
      (Representation.BinaryOffender.fixedSpace ρ (P.subgroupOf D))) :
    P = D₁ ∨ P = D₂ := by
  obtain ⟨x,hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hfixed
  have hxV : (x : V) ≠ 0 := fun hz => hx (Subtype.ext hz)
  apply source_natural_cartan_eq_axis D D₁ D₂ P q₁ q₂ hPD hD
    haxis₁ haxis₂ hP hD₁ hD₂ (c x)
  · exact fun hz => hxV (hc (hz.trans c.map_zero.symm))
  · intro p hp
    have hxfix : ρ p (x : V) = (x : V) := x.property ⟨p,hp⟩
    rw [← he p hp, hxfix]

end CFSG.Quasithin.Chapter10
