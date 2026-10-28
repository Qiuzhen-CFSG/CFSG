module

public import Theory.PGroupCore
public import Theory.ElementaryAbelian.Quotient
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Binary actions on a fixed-subgroup quotient

If a faithful action on an elementary abelian two-group fixes a subgroup
pointwise, the kernel of the induced quotient action is a two-group. Indeed,
an element of the kernel fixes all its displacements, and hence squares to
one. A trivial two-core consequently makes the quotient action faithful.
For a binary line this is the kernel of its point stabilizer acting on V/l.

The displacement argument also occurs in `SolvableSixteenFixedPointAction`;
this public version applies to the actual actor without solvability. Source
application: Aschbacher–Smith, proof of 14.2.21, printed p.988.
-/

open Subgroup
open scoped IsMulCommutative

namespace BinaryFixedLine
variable {A V : Type*} [Group A] [Group V] [IsElementaryAbelian 2 V]

@[expose] public def quotientAction (ρ : A →* MulAut V) (L : Subgroup V)
    (hfix : ∀ a : A, ∀ x ∈ L, ρ a x = x) : A →* MulAut (V ⧸ L) where
  toFun a := QuotientGroup.congr L L (ρ a) (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change ρ a y ∈ L
      rwa [hfix a y hy]
    · intro hx
      exact ⟨x, hx, hfix a x hx⟩)
  map_one' := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective L x
    change QuotientGroup.mk' L (ρ 1 x) = QuotientGroup.mk' L x
    rw [map_one]; rfl
  map_mul' a b := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective L x
    change QuotientGroup.mk' L (ρ (a * b) x) = QuotientGroup.mk' L (ρ a (ρ b x))
    rw [map_mul]; rfl

public theorem quotientAction_apply (ρ : A →* MulAut V) (L : Subgroup V)
    (hfix : ∀ a : A, ∀ x ∈ L, ρ a x = x) (a : A) (x : V) :
    quotientAction ρ L hfix a (QuotientGroup.mk' L x) =
      QuotientGroup.mk' L (ρ a x) := rfl

public theorem kernel_isPGroup (ρ : A →* MulAut V) (hρ : Function.Injective ρ)
    (L : Subgroup V) (hfix : ∀ a : A, ∀ x ∈ L, ρ a x = x) :
    IsPGroup 2 (quotientAction ρ L hfix).ker := by
  have hinv (x : V) : x⁻¹ = x := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) x
  intro a
  refine ⟨1, ?_⟩
  suffices ha : a ^ 2 = 1 by simpa using ha
  apply Subtype.ext
  apply hρ
  change ρ (a.val ^ 2) = ρ 1
  rw [map_pow, map_one]
  ext x
  have he := MulEquiv.congr_fun (MonoidHom.mem_ker.mp a.property)
    (QuotientGroup.mk' L x)
  have hdelta : x⁻¹ * ρ a.val x ∈ L := QuotientGroup.eq.mp he.symm
  have hh := hfix a.val _ hdelta
  simp only [map_mul, hinv] at hh
  change ρ a.val (ρ a.val x) = x
  apply mul_left_cancel (a := ρ a.val x)
  exact hh.trans (mul_comm _ _)

public theorem quotientAction_injective (ρ : A →* MulAut V) (hρ : Function.Injective ρ)
    (L : Subgroup V) (hfix : ∀ a : A, ∀ x ∈ L, ρ a x = x)
    (hcore : pCore 2 A = ⊥) : Function.Injective (quotientAction ρ L hfix) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply bot_unique
  calc
    _ ≤ pCore 2 A := le_sSup ⟨inferInstance, kernel_isPGroup ρ hρ L hfix⟩
    _ = ⊥ := hcore

/-- The complete point stabilizer acts on the quotient by its fixed line. -/
@[expose] public def stabilizerQuotientAction (z : V) :
    MulAction.stabilizer (MulAut V) z →* MulAut (V ⧸ zpowers z) :=
  quotientAction (MulAction.stabilizer (MulAut V) z).subtype (zpowers z) (by
    intro a x hx
    obtain ⟨n, rfl⟩ := hx
    change (a : MulAut V) (z ^ n) = z ^ n
    rw [map_zpow, show (a : MulAut V) z = z from a.property])

/-- For nonzero `z` in dimension four this is the two-group kernel of
the point stabilizer in GL₄(2) acting on the three-dimensional quotient. -/
public theorem stabilizerQuotientAction_kernel (z : V) :
    IsPGroup 2 (stabilizerQuotientAction z).ker :=
  kernel_isPGroup _ (Subgroup.subtype_injective _) _ _

/-- Multiplicative automorphisms are exactly linear automorphisms of the
associated binary vector space, with unchanged evaluation. -/
@[expose] public def linearAutEquiv :
    MulAut V ≃* (Additive V ≃ₗ[ZMod 2] Additive V) where
  toFun a := { a.toAdditive with map_smul' := ZMod.map_smul a.toAdditive }
  invFun a := MulEquiv.toAdditive.symm a.toAddEquiv
  left_inv := by intro a; ext; rfl
  right_inv := by intro a; ext; rfl
  map_mul' := by intro a b; ext; rfl

public theorem linearAutEquiv_apply (a : MulAut V) (x : V) :
    linearAutEquiv a (Additive.ofMul x) = Additive.ofMul (a x) := rfl

end BinaryFixedLine
