module
public import Theory.Representation.BinaryOffender.Defs
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.Exponent

/-!
# Cartan axes on two binary field lines

A subgroup acting by independent field scalars on two lines and fixing a
nonzero vector lies in one coordinate kernel. If the paired scalar action
is faithful and the subgroup is nontrivial, its fixed space is exactly the
other field line. The binary dimension is therefore the extension degree.
A cyclic subgroup of the paired torus has order dividing the order of the
field unit group, even before it is placed on an axis.

These calculations supply the general-field Cartan alignment and dimension
comparison in Aschbacher–Smith 10.2.3(4), printed p.746. The coordinate maps
are actual homomorphisms and the vector-space identification is equivariant.
-/

public section
open Subgroup
namespace Representation.PairedScalarAxes
variable {F H : Type*} [Field F] [Group H]

/-- A full paired torus has coordinate kernels of the field-unit order. -/
theorem card_coordinate_kernel (q₁ q₂ : H →* Fˣ)
    (hq : Function.Bijective (fun h => (q₁ h,q₂ h))) :
    Nat.card q₁.ker = Nat.card Fˣ := by
  let f := q₂.comp q₁.ker.subtype
  apply Nat.card_congr (MulEquiv.ofBijective f ?_).toEquiv
  constructor
  · intro a b hab
    apply Subtype.ext
    apply hq.injective
    exact Prod.ext (a.property.trans b.property.symm) hab
  · intro a
    obtain ⟨x,hx⟩ := hq.surjective (1,a)
    exact ⟨⟨x, congrArg Prod.fst hx⟩, congrArg Prod.snd hx⟩

/-- A cyclic subgroup of a faithful paired scalar torus has order dividing
the field-unit order; a scalar-axis conclusion is not needed here. -/
theorem cyclic_card_dvd_units (q₁ q₂ : H →* Fˣ)
    (hfaith : q₁.ker ⊓ q₂.ker = ⊥) (P : Subgroup H) [IsCyclic P] :
    Nat.card P ∣ Nat.card Fˣ := by
  rw [← IsCyclic.exponent_eq_card]
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro p
  apply Subtype.ext
  apply (show (p : H) ^ Nat.card Fˣ ∈ (⊥ : Subgroup H) →
    (p : H) ^ Nat.card Fˣ = 1 from fun h => h)
  rw [← hfaith]
  constructor <;> change _ = 1 <;> rw [map_pow] <;> exact pow_card_eq_one'

variable {V : Type*} [Algebra (ZMod 2) F]
  [AddCommGroup V] [Module (ZMod 2) V]

omit [Algebra (ZMod 2) F] in
/-- A nonzero common fixed vector forces one scalar coordinate to be trivial. -/
theorem le_kernel_or_le_kernel_of_nonzero_fixed
    (q₁ q₂ : H →* Fˣ) (P : Subgroup H)
    (v : F × F) (hv : v ≠ 0)
    (hfix : ∀ p ∈ P, ((q₁ p : F) * v.1, (q₂ p : F) * v.2) = v) :
    P ≤ q₁.ker ∨ P ≤ q₂.ker := by
  by_cases hv₁ : v.1 = 0
  · right
    have hv₂ : v.2 ≠ 0 := fun hz => hv (Prod.ext hv₁ hz)
    intro p hp
    change q₂ p = 1
    apply Units.ext
    exact (mul_right_cancel₀ hv₂ (by simpa using congrArg Prod.snd (hfix p hp)))
  · left
    intro p hp
    change q₁ p = 1
    apply Units.ext
    exact (mul_right_cancel₀ hv₁ (by simpa using congrArg Prod.fst (hfix p hp)))

/-- A nontrivial action on the second coordinate fixes precisely the first line. -/
theorem fixedSpace_eq_coordinate_kernel
    (ρ : Representation (ZMod 2) H V) (q₁ q₂ : H →* Fˣ)
    (c : V ≃ₗ[ZMod 2] F × F)
    (he : ∀ p : H, ∀ x, c (ρ p x) = ((q₁ p : F) * (c x).1, (q₂ p : F) * (c x).2))
    (P : Subgroup H) (h₁ : P ≤ q₁.ker) (h₂ : ¬ P ≤ q₂.ker) :
    BinaryOffender.fixedSpace ρ P = ((LinearMap.snd (ZMod 2) F F).comp c.toLinearMap).ker := by
  obtain ⟨p,hp,hp₂⟩ := SetLike.not_le_iff_exists.mp h₂
  have hp₂' : (q₂ p : F) ≠ 1 := by
    intro hh
    exact hp₂ (show q₂ p = 1 from Units.ext hh)
  ext x
  constructor
  · intro hx
    change (c x).2 = 0
    have hh := congrArg Prod.snd ((he p x).symm.trans (congrArg c (hx ⟨p,hp⟩)))
    change (q₂ p : F) * (c x).2 = (c x).2 at hh
    by_contra hx0
    exact hp₂' (mul_right_cancel₀ hx0 (by simpa using hh))
  · intro hx p
    have hx' : (c x).2 = 0 := hx
    apply c.injective
    change c (ρ (p : H) x) = c x
    rw [he, show q₁ p = 1 from h₁ p.property, Units.val_one, one_mul, hx', mul_zero]
    exact Prod.ext rfl hx'.symm

/-- Either marked field line has the binary dimension of the field. -/
theorem finrank_coordinate_kernel [FiniteDimensional (ZMod 2) F]
    (c : V ≃ₗ[ZMod 2] F × F) :
    Module.finrank (ZMod 2) ((LinearMap.snd (ZMod 2) F F).comp c.toLinearMap).ker =
      Module.finrank (ZMod 2) F := by
  let W := ((LinearMap.snd (ZMod 2) F F).comp c.toLinearMap).ker
  let f : W →ₗ[ZMod 2] F := (LinearMap.fst (ZMod 2) F F).comp
    (c.toLinearMap.comp W.subtype)
  apply (LinearEquiv.ofBijective f ?_).finrank_eq
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply c.injective
    apply Prod.ext hxy
    exact x.property.trans y.property.symm
  · intro a
    refine ⟨⟨c.symm (a,0), ?_⟩, ?_⟩
    · change (c (c.symm (a,0))).2 = 0
      rw [c.apply_symm_apply]
    · change (c (c.symm (a,0))).1 = a
      rw [c.apply_symm_apply]

/-- A faithful paired scalar action with a positive-dimensional fixed space
places a nontrivial subgroup on an axis and determines its fixed dimension. -/
theorem axis_and_fixed_finrank [FiniteDimensional (ZMod 2) F]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V) (q₁ q₂ : H →* Fˣ)
    (c : V ≃ₗ[ZMod 2] F × F)
    (he : ∀ p : H, ∀ x, c (ρ p x) = ((q₁ p : F) * (c x).1, (q₂ p : F) * (c x).2))
    (hfaith : q₁.ker ⊓ q₂.ker = ⊥)
    (P : Subgroup H) (hP : P ≠ ⊥)
    (hfixed : 0 < Module.finrank (ZMod 2) (BinaryOffender.fixedSpace ρ P)) :
    (P ≤ q₁.ker ∨ P ≤ q₂.ker) ∧
      Module.finrank (ZMod 2) (BinaryOffender.fixedSpace ρ P) =
        Module.finrank (ZMod 2) F := by
  obtain ⟨x,hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hfixed
  have hxV : (x : V) ≠ 0 := fun hz => hx (Subtype.ext hz)
  have hxc : c x ≠ 0 := fun hz => hxV (c.injective (hz.trans c.map_zero.symm))
  have hk := le_kernel_or_le_kernel_of_nonzero_fixed q₁ q₂ P (c x) hxc (by
    intro p hp
    rw [← he, show ρ p (x : V) = x from x.property ⟨p,hp⟩])
  refine ⟨hk, ?_⟩
  have hnot : ¬ (P ≤ q₁.ker ∧ P ≤ q₂.ker) := by
    rintro ⟨h₁,h₂⟩
    exact hP (le_bot_iff.mp (hfaith ▸ le_inf h₁ h₂))
  rcases hk with h₁ | h₂
  · rw [fixedSpace_eq_coordinate_kernel ρ q₁ q₂ c he P h₁ (fun h₂ => hnot ⟨h₁,h₂⟩)]
    exact finrank_coordinate_kernel c
  · let cs := c.trans (LinearEquiv.prodComm (ZMod 2) F F)
    have hes : ∀ p : H, ∀ x, cs (ρ p x) =
        ((q₂ p : F) * (cs x).1, (q₁ p : F) * (cs x).2) := by
      intro p x
      exact congrArg Prod.swap (he p x)
    rw [fixedSpace_eq_coordinate_kernel ρ q₂ q₁ cs hes P h₂ (fun h₁ => hnot ⟨h₁,h₂⟩)]
    exact finrank_coordinate_kernel cs

end Representation.PairedScalarAxes
