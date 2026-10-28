module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalSubgroups
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.Residual
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Concrete plane groups for Held's extending actions

The diagonal subgroup consists of the independent nonzero scalars on the
coordinate axes over F₃. Adjoining the coordinate swap gives the monomial
subgroup. They have orders four and eight, and there is no intermediate
subgroup. An explicit faithful action identifies the latter with D₈.
The first coordinate axis is a proper nonzero subgroup fixed by the entire
diagonal group.

These are the coordinate calculations used by the local Held pair analysis
(Aschbacher–Smith, printed pp.509–511; GLS3, Table 5.3p). Identifying an
actual Held pair action with one of these subgroups remains a separate
calculation; no catalogue or action-image equality is assumed here.
-/

@[expose] public section

namespace Held.LocalPairs.PairCoverage.LocalActions
open Subgroup

abbrev Plane := Multiplicative (Fin 2 → ZMod 3)

/-- Independent nonzero scalars on the two coordinates. -/
def diagonalHom : (Fin 2 → (ZMod 3)ˣ) →* MulAut Plane where
  toFun u := AddEquiv.toMultiplicative {
    toFun := fun (x : Fin 2 → ZMod 3) i => (u i : ZMod 3) * x i
    invFun := fun (x : Fin 2 → ZMod 3) i => (((u i)⁻¹ : (ZMod 3)ˣ) : ZMod 3) * x i
    left_inv := by intro x; funext i; simp only [← mul_assoc, Units.inv_mul, one_mul]
    right_inv := by intro x; funext i; simp only [← mul_assoc, Units.mul_inv, one_mul]
    map_add' := by intro x y; funext i; exact mul_add _ _ _ }
  map_one' := by
    apply MulEquiv.ext
    intro x
    funext i
    change (1 : ZMod 3) * x.toAdd i = x.toAdd i
    exact one_mul _
  map_mul' u v := by
    apply MulEquiv.ext
    intro x
    funext i
    change ((u i : ZMod 3) * (v i : ZMod 3)) * x.toAdd i =
      (u i : ZMod 3) * ((v i : ZMod 3) * x.toAdd i)
    exact mul_assoc _ _ _

def diagonal : Subgroup (MulAut Plane) := diagonalHom.range

theorem diagonalHom_apply (u : Fin 2 → (ZMod 3)ˣ) (x : Plane) (i : Fin 2) :
    (diagonalHom u x).toAdd i = (u i : ZMod 3) * x.toAdd i := rfl

theorem diagonalHom_injective : Function.Injective diagonalHom := by
  intro u v h
  funext i
  apply Units.ext
  have he := congrArg (fun a : MulAut Plane => (a (Multiplicative.ofAdd (fun _ => 1))).toAdd i) h
  change (u i : ZMod 3) * 1 = (v i : ZMod 3) * 1 at he
  simpa only [mul_one] using he

def swap : MulAut Plane := AddEquiv.toMultiplicative {
  toFun := fun x i => x (Equiv.swap (0 : Fin 2) 1 i)
  invFun := fun x i => x (Equiv.swap (0 : Fin 2) 1 i)
  left_inv := by intro x; funext i; fin_cases i <;> rfl
  right_inv := by intro x; funext i; fin_cases i <;> rfl
  map_add' := by intro x y; rfl }

theorem swap_apply (x : Plane) (i : Fin 2) :
    (swap x).toAdd i = x.toAdd (Equiv.swap (0 : Fin 2) 1 i) := rfl

@[simp] theorem swap_inv : swap⁻¹ = swap := rfl

@[simp] theorem swap_sq : swap ^ 2 = 1 := by
  apply MulEquiv.ext
  intro x
  funext i
  fin_cases i <;> rfl

theorem swap_conj_diagonal (u : Fin 2 → (ZMod 3)ˣ) :
    swap * diagonalHom u * swap⁻¹ = diagonalHom (fun i => u (Equiv.swap 0 1 i)) := by
  apply MulEquiv.ext
  intro x
  funext i
  fin_cases i <;> rfl

def monomial : Subgroup (MulAut Plane) := diagonal ⊔ zpowers swap

theorem diagonal_card : Nat.card diagonal = 4 := by
  rw [diagonal, ← Nat.card_congr (MonoidHom.ofInjective diagonalHom_injective).toEquiv]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem swap_not_mem_diagonal : swap ∉ diagonal := by
  rintro ⟨u, hu⟩
  have he := congrArg (fun a : MulAut Plane =>
    (a (Multiplicative.ofAdd (fun i => if i = (0 : Fin 2) then 0 else 1))).toAdd 0) hu
  change (u 0 : ZMod 3) * 0 = 1 at he
  exact zero_ne_one (by simpa only [mul_zero] using he)

theorem swap_mem_normalizer_diagonal : swap ∈ normalizer (diagonal : Set (MulAut Plane)) := by
  rw [mem_normalizer_iff]
  intro a
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨_, (swap_conj_diagonal u).symm⟩
  · rintro ⟨u, hu⟩
    refine ⟨(fun i => u (Equiv.swap 0 1 i)), ?_⟩
    rw [← swap_conj_diagonal, hu, swap_inv]
    have hs : swap * swap = 1 := by simpa only [pow_two] using swap_sq
    calc
      swap * (swap * a * swap) * swap = (swap * swap) * a * (swap * swap) := by group
      _ = a := by rw [hs]; simp

theorem monomial_card : Nat.card monomial = 8 := by
  rw [monomial, card_sup_zpowers_of_normalizing_involution _ _ swap_sq
    swap_not_mem_diagonal swap_mem_normalizer_diagonal, diagonal_card]

theorem diagonal_le_monomial : diagonal ≤ monomial := le_sup_left

/-- There is no third intermediate image between the diagonal and monomial groups. -/
theorem eq_diagonal_or_monomial (H : Subgroup (MulAut Plane))
    (hD : diagonal ≤ H) (hM : H ≤ monomial) : H = diagonal ∨ H = monomial := by
  have hd := card_dvd_of_le hD
  rw [diagonal_card] at hd
  have hm := card_dvd_of_le hM
  rw [monomial_card] at hm
  have hp : 0 < Nat.card H := Nat.card_pos
  have hu : Nat.card H ≤ 8 := Nat.le_of_dvd (by decide) hm
  have hc : Nat.card H = 4 ∨ Nat.card H = 8 := by omega
  rcases hc with hc | hc
  · exact Or.inl (eq_of_le_of_card_ge hD (by rw [hc, diagonal_card])).symm
  · exact Or.inr (eq_of_le_of_card_ge hM (by rw [hc, monomial_card]))

/-- A specific invariant coordinate line, kept as a literal subgroup. -/
def axis : Subgroup Plane where
  carrier := {x | x.toAdd 1 = 0}
  one_mem' := rfl
  mul_mem' := by intro x y hx hy; change x.toAdd 1 + y.toAdd 1 = 0; rw [hx,hy]; rfl
  inv_mem' := by intro x hx; change -x.toAdd 1 = 0; rw [hx]; rfl

theorem axis_ne_bot : axis ≠ ⊥ := by
  intro h
  have hx : Multiplicative.ofAdd (fun i : Fin 2 => if i = 0 then (1 : ZMod 3) else 0) ∈ axis := by
    rfl
  rw [h, mem_bot] at hx
  have h0 := congrArg (fun x : Plane => x.toAdd 0) hx
  exact one_ne_zero h0

theorem axis_ne_top : axis ≠ ⊤ := by
  intro h
  have hx : Multiplicative.ofAdd (fun _ : Fin 2 => (1 : ZMod 3)) ∈ axis := by rw [h]; trivial
  exact one_ne_zero hx

theorem diagonal_preserves_axis (a : MulAut Plane) (ha : a ∈ diagonal)
    (x : Plane) (hx : x ∈ axis) : a x ∈ axis := by
  obtain ⟨u,rfl⟩ := ha
  change (u 1 : ZMod 3) * x.toAdd 1 = 0
  change x.toAdd 1 = 0 at hx
  rw [hx, mul_zero]

/-- A quarter-turn of the literal plane. -/
def rotation : MulAut Plane := diagonalHom (fun i => if i = 0 then -1 else 1) * swap

/-- Coordinate formula for all eight dihedral actors. -/
def dihedralMap : DihedralGroup 4 → MulAut Plane
  | .r i => rotation ^ i.val
  | .sr i => swap * rotation ^ i.val

theorem dihedralMap_mul (a b : DihedralGroup 4) :
    dihedralMap (a * b) = dihedralMap a * dihedralMap b := by
  apply MulEquiv.ext
  intro x
  funext i
  have h : ∀ a b : DihedralGroup 4, ∀ x : Plane, ∀ i : Fin 2,
      (dihedralMap (a * b) x).toAdd i = (dihedralMap a (dihedralMap b x)).toAdd i := by
    decide +kernel
  exact h a b x i

/-- The displayed rotations and reflections, acting on the actual plane. -/
def dihedralAction : DihedralGroup 4 →* MulAut Plane where
  toFun := dihedralMap
  map_one' := rfl
  map_mul' := dihedralMap_mul

theorem dihedralAction_injective : Function.Injective dihedralAction := by
  have h : ∀ a b : DihedralGroup 4,
      (∀ x : Plane, ∀ i : Fin 2, (dihedralMap a x).toAdd i = (dihedralMap b x).toAdd i) → a = b := by
    decide +kernel
  intro a b hab
  exact h a b (fun x i => congrArg (fun f : MulAut Plane => (f x).toAdd i) hab)

theorem dihedralAction_mem (a : DihedralGroup 4) : dihedralAction a ∈ monomial := by
  have hs : swap ∈ monomial := (show zpowers swap ≤ monomial from le_sup_right) (mem_zpowers swap)
  have hr : rotation ∈ monomial :=
    monomial.mul_mem (diagonal_le_monomial ⟨_, rfl⟩) hs
  cases a with
  | r i => exact monomial.pow_mem hr i.val
  | sr i => exact monomial.mul_mem hs (monomial.pow_mem hr i.val)

/-- An explicit faithful dihedral action exhausts the eight monomial matrices. -/
noncomputable def monomialEquivDihedral : monomial ≃* DihedralGroup 4 := by
  let f := dihedralAction.codRestrict monomial dihedralAction_mem
  have hinj : Function.Injective f := fun a b h =>
    dihedralAction_injective (congrArg Subtype.val h)
  have hcard : Nat.card monomial ≤ Nat.card (DihedralGroup 4) := by
    rw [monomial_card, DihedralGroup.nat_card]
  exact (MulEquiv.ofBijective f (hinj.bijective_of_nat_card_le hcard)).symm

end Held.LocalPairs.PairCoverage.LocalActions
