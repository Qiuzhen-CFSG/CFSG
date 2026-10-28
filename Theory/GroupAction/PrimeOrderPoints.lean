module

public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.FieldTheory.Finiteness

/-!
# Prime-order subgroup points and their original automorphism action

Subgroup points retain the actual subgroups of the original group. An
explicit automorphism homomorphism acts by subgroup images, and orbit
and stabilizer membership are expressed using exactly those maps.
For elementary abelian groups the usual projective-space count gives
the number of prime-order subgroups, including the thirteen points of E₂₇.

This is the projective geometry used in Aschbacher–Smith, J.2.7,
printed p.437 (PDF p.448).
-/

@[expose] public section
noncomputable section
namespace Subgroup

/-- The subgroups of a given order, retaining their original inclusion. -/
def OrderPoints (p : ℕ) (W : Type*) [Group W] := {U : Subgroup W // Nat.card U = p}

namespace OrderPoints
variable {p : ℕ} {A W : Type*} [Group A] [Group W]

/-- An automorphism action induces the literal image action on subgroup points. -/
@[instance_reducible] def action (ρ : A →* MulAut W) : MulAction A (OrderPoints p W) where
  smul a U := ⟨U.val.map (ρ a).toMonoidHom,
    (card_map_of_injective (ρ a).injective).trans U.property⟩
  one_smul U := by
    apply Subtype.ext
    change U.val.map (ρ 1).toMonoidHom = U.val
    rw [map_one]
    exact U.val.map_id
  mul_smul a b U := by
    apply Subtype.ext
    change U.val.map (ρ (a * b)).toMonoidHom =
      (U.val.map (ρ b).toMonoidHom).map (ρ a).toMonoidHom
    rw [map_map]
    congr 1
    ext x
    simp only [map_mul, MulEquiv.coe_toMonoidHom, MulAut.mul_apply, MonoidHom.comp_apply]

/-- The orbit under the given action, without choosing a replacement action. -/
def orbit (ρ : A →* MulAut W) (U : OrderPoints p W) : Set (OrderPoints p W) :=
  letI := action (p := p) ρ
  MulAction.orbit A U

/-- The literal stabilizer in the original actor group. -/
def stabilizer (ρ : A →* MulAut W) (U : OrderPoints p W) : Subgroup A :=
  letI := action (p := p) ρ
  MulAction.stabilizer A U

theorem mem_stabilizer_iff (ρ : A →* MulAut W) (U : OrderPoints p W) (a : A) :
    a ∈ stabilizer ρ U ↔ U.val.map (ρ a).toMonoidHom = U.val :=
  Subtype.ext_iff

theorem mem_orbit_iff (ρ : A →* MulAut W) (U V : OrderPoints p W) :
    V ∈ orbit ρ U ↔ ∃ a : A, U.val.map (ρ a).toMonoidHom = V.val := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

section Elementary
variable [Finite W] [Fact p.Prime] [IsElementaryAbelian p W]
open scoped IsMulCommutative LinearAlgebra.Projectivization

private def subspaceEquiv : Subgroup W ≃o Submodule (ZMod p) (Additive W) :=
  Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule p)

private theorem card_iff (U : Subgroup W) :
    Nat.card U = p ↔ Module.finrank (ZMod p) (subspaceEquiv (p := p) U) = 1 := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod p) (V := subspaceEquiv (p := p) U)
  change Nat.card U = _ at hc
  rw [Nat.card_zmod] at hc
  rw [hc]
  simpa only [pow_one] using
    (Nat.pow_right_injective (Fact.out : p.Prime).two_le).eq_iff
      (a := Module.finrank (ZMod p) (subspaceEquiv (p := p) U)) (b := 1)

/-- The projective count, stated directly for prime-order subgroups. -/
theorem card_formula : Nat.card W = Nat.card (OrderPoints p W) * (p - 1) + 1 := by
  let e := (Equiv.subtypeEquiv (subspaceEquiv (p := p)).toEquiv (card_iff (p := p) (W := W))).trans
    (Projectivization.equivSubmodule (ZMod p) (Additive W)).symm
  have hc := Projectivization.card' (ZMod p) (Additive W)
  change Nat.card W = _ at hc
  rwa [Nat.card_zmod, ← Nat.card_congr e] at hc

end Elementary

/-- The elementary group of order 27 has exactly thirteen order-three subgroups. -/
theorem card_thirteen [Finite W] [IsElementaryAbelian 3 W] (hW : Nat.card W = 27) :
    Nat.card (OrderPoints 3 W) = 13 := by
  have hc := card_formula (p := 3) (W := W)
  rw [hW] at hc
  omega

end OrderPoints
end Subgroup
