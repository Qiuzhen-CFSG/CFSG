module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Algebra.Field.ZMod

/-!
# Binary exterior coordinates for the native degree-44 comparison

Upper triangular coefficient arrays encode wedge combinations. The alternating
relations identify the induced coordinate action with the actual exterior-power
functor. These identities apply to any eleven vectors over the binary field;
no independence assumption is needed.

Used for the Golay kernel construction in James (1973), pp.57–111, and
GM02 Proposition 5.1, manuscript p.17.
-/

@[expose] public section
open scoped BigOperators
noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour.KernelAbsolute.NativeMap.CoordinateExterior
abbrev F := ZMod 2
variable {V : Type*} [AddCommGroup V] [Module F V]
abbrev Ext (V : Type*) [AddCommGroup V] [Module F V] := ⋀[F]^2 V

omit [AddCommGroup V] [Module F V] in
private theorem update_pair_zero (x y z : V) : Function.update ![x,y] 0 z = ![z,y] := by
  ext i; fin_cases i <;> simp
omit [AddCommGroup V] [Module F V] in
private theorem update_pair_one (x y z : V) : Function.update ![x,y] 1 z = ![x,z] := by
  ext i; fin_cases i <;> simp

def wedge : V →ₗ[F] V →ₗ[F] Ext V :=
  LinearMap.mk₂ F (fun x y => exteriorPower.ιMulti F 2 ![x,y])
    (by intro x y z; simpa only [update_pair_zero, update_pair_one] using (exteriorPower.ιMulti F 2 (M := V)).map_update_add ![x,z] 0 x y)
    (by intro c x y; simpa only [update_pair_zero, update_pair_one] using (exteriorPower.ιMulti F 2 (M := V)).map_update_smul ![x,y] 0 c x)
    (by intro x y z; simpa only [update_pair_zero, update_pair_one] using (exteriorPower.ιMulti F 2 (M := V)).map_update_add ![x,y] 1 y z)
    (by intro c x y; simpa only [update_pair_zero, update_pair_one] using (exteriorPower.ιMulti F 2 (M := V)).map_update_smul ![x,y] 1 c y)

theorem wedge_self (x : V) : wedge x x = 0 := by
  exact (exteriorPower.ιMulti F 2).map_eq_zero_of_eq ![x,x] (by simp : (![x,x] : Fin 2 → V) 0 = ![x,x] 1) (by decide : (0 : Fin 2) ≠ 1)

theorem wedge_comm (x y : V) : wedge x y = wedge y x := by
  have h := (exteriorPower.ιMulti F 2 (M := V)).map_swap ![y,x] (by decide : (0 : Fin 2) ≠ 1)
  have he : (![y,x] : Fin 2 → V) ∘ Equiv.swap 0 1 = ![x,y] := by ext i; fin_cases i <;> simp
  rw [he] at h
  change wedge x y = - wedge y x at h
  rw [← neg_one_smul F, show (-1 : F) = 1 by decide, one_smul] at h
  exact h

theorem sum_ordered {I V : Type*} [Fintype I] [LinearOrder I] [AddCommMonoid V]
    (f : I → I → V) (hf : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = ∑ i, ∑ j, if i < j then f i j + f j i else 0 := by
  have he (i j : I) : (if i < j then f i j + f j i else 0) =
      (if i < j then f i j else 0) + (if i < j then f j i else 0) := by split <;> simp
  simp_rw [he]
  simp_rw [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if i < j then f j i else 0)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rcases lt_trichotomy i j with h | h | h
  · simp [h, not_lt_of_gt h]
  · subst j; simp [hf]
  · simp [h, not_lt_of_gt h]

abbrev I := Fin 11
abbrev P := I × I
abbrev C := I → F
abbrev T := P → F

variable (r : I → V)

def codeLift : C →ₗ[F] V where
  toFun x := ∑ i, x i • r i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, mul_smul]

def lift : T →ₗ[F] Ext V where
  toFun t := ∑ p, t p • wedge (r p.1) (r p.2)
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, mul_smul]

def wedgeCoords (x y : C) : T := fun p =>
  if p.1 < p.2 then x p.1 * y p.2 + x p.2 * y p.1 else 0

theorem lift_wedgeCoords (x y : C) :
    lift r (wedgeCoords x y) = wedge (codeLift r x) (codeLift r y) := by
  have he : wedge (codeLift r x) (codeLift r y) =
      ∑ i, ∑ j, (x i * y j) • wedge (r i) (r j) := by
    simp only [codeLift, LinearMap.coe_mk, AddHom.coe_mk, map_sum, LinearMap.sum_apply,
      map_smul, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [he, sum_ordered (fun i j => (x i * y j) • wedge (r i) (r j))
    (fun i => by rw [wedge_self, smul_zero])]
  change (∑ p, wedgeCoords x y p • wedge (r p.1) (r p.2)) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp [wedgeCoords]
  split_ifs with h
  · rw [add_smul, wedge_comm (r j) (r i)]
  · simp

def coordsAction (a : I → C) : T →ₗ[F] T where
  toFun t := ∑ p, t p • wedgeCoords (a p.1) (a p.2)
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, mul_smul]

theorem map_wedge (g : V →ₗ[F] V) (x y : V) :
    exteriorPower.map 2 g (wedge x y) = wedge (g x) (g y) := by
  change exteriorPower.map 2 g (exteriorPower.ιMulti F 2 ![x,y]) = _
  rw [exteriorPower.map_apply_ιMulti]
  rfl

theorem lift_action (g : V →ₗ[F] V) (a : I → C)
    (h : ∀ i, g (r i) = codeLift r (a i)) (t : T) :
    exteriorPower.map 2 g (lift r t) = lift r (coordsAction a t) := by
  calc
    _ = ∑ p : P, t p • wedge (g (r p.1)) (g (r p.2)) := by
      simp only [lift, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, map_wedge]
    _ = ∑ p : P, t p • lift r (wedgeCoords (a p.1) (a p.2)) := by
      simp only [h, lift_wedgeCoords]
    _ = _ := by
      simp only [coordsAction, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul]

variable {J : Type*} [Fintype J]
def combine (cols : J → V) : (J → F) →ₗ[F] V where
  toFun t := ∑ j, t j • cols j
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, mul_smul]

@[simp] theorem combine_single [DecidableEq J] (cols : J → V) (j : J) (c : F) :
    combine cols (Pi.single j c) = c • cols j := by
  simp [combine, Pi.single_apply]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour.KernelAbsolute.NativeMap.CoordinateExterior
