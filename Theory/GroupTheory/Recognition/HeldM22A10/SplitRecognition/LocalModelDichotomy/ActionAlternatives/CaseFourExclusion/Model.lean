module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.Coordinates
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# The two-group in Janko's Case IV

The actor is the dihedral group of order eight, embedded in the marked S4 by
r = b*d and s = d. Its binary action is exactly the Case IV action on E.
The semidirect product has order 128; H = E<a,b> has index two, and C_T(d)
has order sixteen. Every involution in H has a T-centralizer of order at
least 32, which packages the last local calculation in the exclusion.

All finite identities are checked by kernel reduction on this 128-element
model. The connection to the original ambient group is in `Ambient`.
Source: Janko, A characterization of the Mathieu simple groups, I,
J. Algebra 9 (1968), Section 1, printed pp.2–3,
DOI 10.1016/0021-8693(68)90002-1.
-/

namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseFour

@[expose] public def actor : DihedralGroup 4 →* SymmetricFour where
  toFun s := match s with
    | .r i => (jankoB * jankoD) ^ i.val
    | .sr i => jankoD * (jankoB * jankoD) ^ i.val
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

@[expose] public def bAut : MulAut BinaryFour where
  toFun := jankoSourceB .four
  invFun := jankoSourceB .four
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

@[expose] public def dAut : MulAut BinaryFour where
  toFun := jankoSourceD .four
  invFun := jankoSourceD .four
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

@[expose] public def actionFun : DihedralGroup 4 → MulAut BinaryFour
  | .r i => (bAut * dAut) ^ i.val
  | .sr i => dAut * (bAut * dAut) ^ i.val

@[expose] public def action : DihedralGroup 4 →* MulAut BinaryFour where
  toFun := actionFun
  map_one' := by apply MulEquiv.ext; intro v; rfl
  map_mul' := by
    have h : ∀ s t v, actionFun (s * t) v = actionFun s (actionFun t v) := by
      decide +kernel
    intro s t
    exact MulEquiv.ext (h s t)

public abbrev Model := BinaryFour ⋊[action] DihedralGroup 4
public instance : DecidableEq Model := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
public instance : Fintype Model := Fintype.ofEquiv (BinaryFour × DihedralGroup 4)
  SemidirectProduct.equivProd.symm

@[expose] public def d : Model := SemidirectProduct.inr (.sr 0)
@[expose] public def a : Model := SemidirectProduct.inr (.r 2)
@[expose] public def b : Model := SemidirectProduct.inr (.sr 3)
@[expose] public def z (i : Fin 4) : Model := SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single i 1))

@[expose] public def H : Subgroup Model where
  carrier := {x | x.right = 1 ∨ x.right = .r 2 ∨ x.right = .sr 1 ∨ x.right = .sr 3}
  one_mem' := Or.inl rfl
  mul_mem' := by
    have hh : ∀ s t : DihedralGroup 4,
        (s = 1 ∨ s = .r 2 ∨ s = .sr 1 ∨ s = .sr 3) →
        (t = 1 ∨ t = .r 2 ∨ t = .sr 1 ∨ t = .sr 3) →
        (s*t = 1 ∨ s*t = .r 2 ∨ s*t = .sr 1 ∨ s*t = .sr 3) := by decide +kernel
    exact fun _ _ hx hy => hh _ _ hx hy
  inv_mem' := by
    have hh : ∀ s : DihedralGroup 4,
        (s = 1 ∨ s = .r 2 ∨ s = .sr 1 ∨ s = .sr 3) →
        (s⁻¹ = 1 ∨ s⁻¹ = .r 2 ∨ s⁻¹ = .sr 1 ∨ s⁻¹ = .sr 3) := by decide +kernel
    exact fun _ hx => hh _ hx
public instance : DecidablePred (· ∈ H) := fun x =>
  inferInstanceAs (Decidable (x.right = 1 ∨ x.right = .r 2 ∨ x.right = .sr 1 ∨ x.right = .sr 3))

public theorem model_card : Nat.card Model = 128 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

public theorem H_card : Nat.card H = 64 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

@[expose] public def F : Subgroup Model := Subgroup.centralizer {d}
public instance : DecidablePred (· ∈ F) := fun x =>
  decidable_of_iff (x*d=d*x) Subgroup.mem_centralizer_singleton_iff.symm

public theorem F_card : Nat.card F = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- The uniform local bound used after Thompson transfer. -/
public theorem centralizer_bound : ∀ x : Model, x ∈ H → x*x=1 →
    32 ≤ (Finset.univ.filter (fun y : Model => y*x=x*y)).card := by
  decide +kernel

end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseFour
