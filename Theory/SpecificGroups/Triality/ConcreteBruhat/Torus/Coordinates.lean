module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.Candidates
public import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# Multiplicative coordinates for the triality torus

The four coordinates are units, indexed by the original numbered simple
coroots. The product puts the three arms first, followed by the central
coroot. Graph-field fixed tuples consist of t, F(t), F²(t) on the arms
and a unit of the actual fixed field on the central node.

This module proves the scalar parametrization and its cardinality. The
matrix product is defined using the original coroot words; its faithfulness
and its full range are separate matrix assertions.

Source: GLS3 2.3.4(c), 2.3.8(a), and §2.4
(`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.ConcreteBruhat.TorusCoordinates
open Parabolics
open Theory.AlgebraicGroup.StandardRootSystem

abbrev Coordinates (P : Parameters) := Fin 4 → (ExtensionField P)ˣ

/-- Product of the original coroot words, with the central node last. -/
def product (P : Parameters) (a : Coordinates P) : SplitGroup P :=
  torusWord P 0 (a 0) * torusWord P 2 (a 2) * torusWord P 3 (a 3) *
    torusWord P 1 (a 1)

theorem product_mem (P : Parameters) (a : Coordinates P) :
    product P a ∈ splitTorus P := by
  have h (i : Fin 4) : torusWord P i (a i) ∈ splitTorus P :=
    Subgroup.subset_closure ⟨i, a i, rfl⟩
  exact (splitTorus P).mul_mem
    ((splitTorus P).mul_mem ((splitTorus P).mul_mem (h 0) (h 2)) (h 3)) (h 1)

/-- Frobenius on units, retaining the original field automorphism. -/
def frobenius (P : Parameters) : (ExtensionField P)ˣ →* (ExtensionField P)ˣ :=
  Units.map (fieldFrobenius P).toMonoidHom

theorem frobenius_three (P : Parameters) (t : (ExtensionField P)ˣ) :
    frobenius P (frobenius P (frobenius P t)) = t := by
  apply Units.ext
  exact fieldFrobenius_three P t

/-- The inclusion of units of the actual q-Frobenius fixed field. -/
def fixedUnit (P : Parameters) : (fixedField P)ˣ →* (ExtensionField P)ˣ :=
  Units.map (fixedField P).subtype.toMonoidHom

@[simp] theorem frobenius_fixedUnit (P : Parameters) (t : (fixedField P)ˣ) :
    frobenius P (fixedUnit P t) = fixedUnit P t := by
  apply Units.ext
  exact (t.val).property

/-- Pull back the pinned diagram permutation and apply Frobenius. -/
def twist (P : Parameters) (a : Coordinates P) : Coordinates P :=
  fun i => frobenius P (a (typeD4DiagramPermutation.symm i))

theorem twist_eq_self_iff (P : Parameters) (a : Coordinates P) :
    twist P a = a ↔ ∀ i, a (typeD4DiagramPermutation i) = frobenius P (a i) := by
  constructor
  · intro h i
    simpa only [twist, Equiv.symm_apply_apply] using
      (congrFun h (typeD4DiagramPermutation i)).symm
  · intro h
    funext i
    simpa only [twist, Equiv.apply_symm_apply] using (h (typeD4DiagramPermutation.symm i)).symm

abbrev FixedCoordinates (P : Parameters) := {a : Coordinates P // twist P a = a}
abbrev OrbitParameters (P : Parameters) := (ExtensionField P)ˣ × (fixedField P)ˣ

def expand (P : Parameters) (a : OrbitParameters P) : Coordinates P :=
  ![a.1, fixedUnit P a.2, frobenius P a.1, frobenius P (frobenius P a.1)]

theorem expand_mul (P : Parameters) (a b : OrbitParameters P) :
    expand P (a * b) = expand P a * expand P b := by
  funext i
  fin_cases i <;> simp [expand, map_mul]

theorem expand_fixed (P : Parameters) (a : OrbitParameters P) :
    twist P (expand P a) = expand P a := by
  rw [twist_eq_self_iff]
  intro i
  fin_cases i <;> simp [expand, typeD4DiagramPermutation, frobenius_three]

/-- A Frobenius-fixed unit is a unit in the fixed field, including its inverse. -/
def restrictUnit (P : Parameters) (t : (ExtensionField P)ˣ)
    (h : frobenius P t = t) : (fixedField P)ˣ where
  val := ⟨t.val, congrArg Units.val h⟩
  inv := ⟨↑t⁻¹, by
    rw [mem_fixedField, Units.val_inv_eq_inv_val]
    rw [map_inv₀, show fieldFrobenius P t.val = t.val from congrArg Units.val h]⟩
  val_inv := Subtype.ext (Units.val_inv t)
  inv_val := Subtype.ext (Units.inv_val t)

@[simp] theorem fixedUnit_restrictUnit (P : Parameters) (t : (ExtensionField P)ˣ)
    (h : frobenius P t = t) : fixedUnit P (restrictUnit P t h) = t :=
  Units.ext rfl

def restrict (P : Parameters) (a : FixedCoordinates P) : OrbitParameters P :=
  (a.val 0, restrictUnit P (a.val 1)
    (((twist_eq_self_iff P a.val).mp a.property 1).symm))

/-- One extension-field unit and one fixed-field unit give every fixed tuple. -/
def fixedCoordinatesEquiv (P : Parameters) : OrbitParameters P ≃ FixedCoordinates P where
  toFun a := ⟨expand P a, expand_fixed P a⟩
  invFun := restrict P
  left_inv a := by
    apply Prod.ext
    · rfl
    · apply Units.ext
      rfl
  right_inv a := by
    apply Subtype.ext
    funext i
    have h := (twist_eq_self_iff P a.val).mp a.property
    have h0 := h 0
    have h2 := h 2
    fin_cases i <;> simp_all [expand, restrict, typeD4DiagramPermutation]
    exact fixedUnit_restrictUnit P _ _

theorem card_coordinates (P : Parameters) :
    Nat.card (Coordinates P) = (P.q ^ 3 - 1) ^ 4 := by
  rw [Nat.card_fun, Nat.card_units, card_extensionField, Nat.card_fin]

theorem card_fixedCoordinates (P : Parameters) :
    Nat.card (FixedCoordinates P) = (P.q ^ 3 - 1) * (P.q - 1) := by
  rw [← Nat.card_congr (fixedCoordinatesEquiv P), Nat.card_prod,
    Nat.card_units, Nat.card_units, card_extensionField, card_fixedField]

end Triality.Standard.ConcreteBruhat.TorusCoordinates
