module
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.OddOrder
import Mathlib.Tactic.Group
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Checking identities with central errors

Words in the signed Parrott alphabet are evaluated in an arbitrary group.
An identity records its central error in seven integer coordinates. The
lemmas below justify every operation in the finite word derivations:
concatenation, inversion, cyclic rotation, and replacement of a subword.
Only ordinary group laws and centrality are used. Integer-coordinate
arithmetic and literal list identities are checked by definitional reduction.

This is the replay layer for Parrott (1972), §5, p.683; it assumes no
presentation relation or exact Weyl identity.
-/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations

inductive Letter | a | b | c | d | e | f | g | h | i | j | E | G | I
  deriving DecidableEq
open scoped IsMulCommutative
abbrev Word := List Letter
@[expose] def flip : Letter → Letter
  | .e => .E | .E => .e | .g => .G | .G => .g | .i => .I | .I => .i | x => x
@[expose] def winv (w : Word) : Word := w.reverse.map flip
abbrev Coeff := ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ

structure Context (G : Type*) [Group G] where
  gen : Letter → G
  inverse : ∀ x, gen (flip x) = (gen x)⁻¹
  central : Fin 7 → Subgroup.center G

namespace Context
variable {G : Type*} [Group G] (D : Context G)
@[expose] def value (w : Word) : G := (w.map D.gen).prod
@[expose] def scalar (v : Coeff) : Subgroup.center G :=
  D.central 0 ^ v.1 * D.central 1 ^ v.2.1 * D.central 2 ^ v.2.2.1 *
  D.central 3 ^ v.2.2.2.1 * D.central 4 ^ v.2.2.2.2.1 *
  D.central 5 ^ v.2.2.2.2.2.1 * D.central 6 ^ v.2.2.2.2.2.2

theorem value_append (w u : Word) : D.value (w ++ u) = D.value w * D.value u := by
  simp [value]

theorem value_inv (w : Word) : D.value (winv w) = (D.value w)⁻¹ := by
  simp only [winv, value, List.map_map, Function.comp_def, D.inverse]
  simp only [List.map_reverse, List.prod_inv_reverse, List.map_map, Function.comp_def]

theorem scalar_add (v u : Coeff) : D.scalar (v + u) = D.scalar v * D.scalar u := by
  simp only [scalar, Prod.fst_add, Prod.snd_add, zpow_add]
  ac_rfl

theorem scalar_zero : D.scalar 0 = 1 := by simp [scalar]

theorem scalar_neg (v : Coeff) : D.scalar (-v) = (D.scalar v)⁻¹ := by
  simp only [scalar, Prod.fst_neg, Prod.snd_neg, zpow_neg, mul_inv_rev]
  ac_rfl

structure Holds (v : Coeff) (w u : Word) : Prop where
  eq : D.value w = D.value u * (D.scalar v : G)

namespace Holds
variable {D} {v u : Coeff} {w x y : Word}
theorem refl (w : Word) : D.Holds 0 w w := by
  constructor
  simp only [scalar_zero, Subgroup.coe_one, mul_one]

theorem trans (h : D.Holds v w x) (k : D.Holds u x y) :
    D.Holds (v + u) w y := by
  rcases h with ⟨h⟩
  rcases k with ⟨k⟩
  constructor
  rw [h, k, scalar_add]
  simp only [Subgroup.coe_mul]
  rw [mul_assoc, ((D.scalar u).property.comm (D.scalar v)).eq]

theorem symm (h : D.Holds v w x) : D.Holds (-v) x w := by
  rcases h with ⟨h⟩
  constructor
  rw [h, scalar_neg]
  simp

theorem mul {w' x' : Word} (h : D.Holds v w x) (k : D.Holds u w' x') :
    D.Holds (v + u) (w ++ w') (x ++ x') := by
  rcases h with ⟨h⟩
  rcases k with ⟨k⟩
  constructor
  rw [value_append, value_append, h, k, scalar_add]
  simp only [Subgroup.coe_mul]
  have hc := (D.scalar v).property.comm (D.value x')
  calc
    _ = D.value x * ((D.scalar v : G) * D.value x') * (D.scalar u : G) := by group
    _ = D.value x * (D.value x' * (D.scalar v : G)) * (D.scalar u : G) := by rw [hc.eq]
    _ = _ := by group

theorem inv (h : D.Holds v w x) : D.Holds (-v) (winv w) (winv x) := by
  rcases h with ⟨h⟩
  constructor
  rw [value_inv, value_inv, h, scalar_neg]
  simp only [mul_inv_rev, Subgroup.coe_inv]
  exact ((D.scalar v)⁻¹).property.comm _ |>.eq

theorem relator (h : D.Holds v w x) : D.Holds v (w ++ winv x) [] := by
  rcases h with ⟨h⟩
  constructor
  rw [value_append, value_inv, h]
  simp only [value, List.map_nil, List.prod_nil, one_mul]
  have hc := (D.scalar v).property.comm (D.value x)⁻¹
  change (D.value x * (D.scalar v : G)) * (D.value x)⁻¹ = (D.scalar v : G)
  rw [mul_assoc, hc.eq, ← mul_assoc, mul_inv_cancel, one_mul]

theorem rotate (pre post : Word) (h : D.Holds v (pre ++ post) []) :
    D.Holds v (post ++ pre) [] := by
  rcases h with ⟨h⟩
  constructor
  rw [value_append] at h ⊢
  simp only [value, List.map_nil, List.prod_nil, one_mul] at h ⊢
  change D.value pre * D.value post = (D.scalar v : G) at h
  have hc := (D.scalar v).property.comm (D.value pre)
  change D.value post * D.value pre = (D.scalar v : G)
  have hh : D.value post = (D.value pre)⁻¹ * (D.scalar v : G) := by
    rw [← h]
    group
  rw [hh, mul_assoc, hc.eq]
  group

theorem cut (w x : Word) (h : D.Holds v (w ++ winv x) []) : D.Holds v w x := by
  rcases h with ⟨h⟩
  constructor
  rw [value_append, value_inv] at h
  simp only [value, List.map_nil, List.prod_nil, one_mul] at h
  change D.value w * (D.value x)⁻¹ = (D.scalar v : G) at h
  exact (mul_inv_eq_iff_eq_mul.mp h).trans ((D.scalar v).property.comm _).eq

theorem replace (pre post : Word) (h : D.Holds v w x) :
    D.Holds v (pre ++ w ++ post) (pre ++ x ++ post) := by
  simpa only [zero_add, add_zero] using ((refl pre).mul h).mul (refl post)
theorem cancel (D : Context G) (letter : Letter) : D.Holds 0 [letter, flip letter] [] := by
  constructor
  simp [value, D.inverse, scalar_zero]

theorem scalar_eq_one (h : D.Holds v w w) : D.scalar v = 1 := by
  apply Subtype.ext
  exact mul_eq_left.mp h.eq.symm

end Holds
end Context


end Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations

namespace Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations.Context
open scoped IsMulCommutative
variable {G : Type*} [Group G] {D : Context G} {v u : Coeff}

theorem vanishes_add (hv : D.scalar v = 1) (hu : D.scalar u = 1) :
    D.scalar (v + u) = 1 := by rw [scalar_add, hv, hu, one_mul]

theorem vanishes_smul (n : ℤ) (hv : D.scalar v = 1) : D.scalar (n • v) = 1 := by
  let f : Coeff →+ Additive (Subgroup.center G) :=
    { toFun := fun w => Additive.ofMul (D.scalar w)
      map_zero' := D.scalar_zero
      map_add' := D.scalar_add }
  have hh := map_zsmul f n v
  change D.scalar (n • v) = D.scalar v ^ n at hh
  rw [hh, hv, one_zpow]
end Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations.Context
