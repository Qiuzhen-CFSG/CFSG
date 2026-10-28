module
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group

/-!
# A pair of factors with simultaneous involution and interchange

An involutive automorphism of a group acts on both factors of its square.
This action commutes with interchange of the factors, giving an extension by
four. The explicit coordinates below retain both involutions and provide
conjugators for the two interchanging cosets and the diagonal actor coset.

These elementary formulas are the local model calculations in
Aschbacher--Smith, proof of 2.4.34, printed p.548 of the 1 March 2004 manuscript.
-/

@[expose] public section
namespace Theory.GroupTheory.PairedInvolutiveExtension
abbrev Bit := Multiplicative (ZMod 2)
def on : Bit := .ofAdd 1
variable {K : Type*} [Group K]
theorem bit_cases (p : Bit) : p = 1 ∨ p = on := by revert p; decide
@[simp] theorem on_ne : on ≠ 1 := by decide
@[simp] theorem on_mul_on : on * on = 1 := by decide
@[simp] theorem on_inv : on⁻¹ = on := by decide
variable (α : MulAut K) (hα : Function.Involutive α)
def action : Bit × Bit →* MulAut (K × K) where
  toFun u := (if u.1 = 1 then 1 else α.prodCongr α) *
    (if u.2 = 1 then 1 else MulEquiv.prodComm)
  map_one' := by simp
  map_mul' u v := by
    rcases u with ⟨p,q⟩
    rcases v with ⟨r,s⟩
    rcases bit_cases p with rfl|rfl <;>
      rcases bit_cases q with rfl|rfl <;>
      rcases bit_cases r with rfl|rfl <;>
      rcases bit_cases s with rfl|rfl <;>
      ext a <;> simp [MulEquiv.prodCongr]
    all_goals exact (hα _).symm

abbrev Model := (K × K) ⋊[action α hα] (Bit × Bit)
def mk (a b : K) (p q : Bit) : Model α hα := ⟨(a,b),(p,q)⟩
def base (a b : K) : Model α hα := mk α hα a b 1 1
def graph : Model α hα := mk α hα 1 1 on 1
def swap : Model α hα := mk α hα 1 1 1 on
def graphSwap : Model α hα := mk α hα 1 1 on on

@[simp] theorem action_one (a b : K) : action α hα (1,1) (a,b) = (a,b) := by simp [action]
@[simp] theorem action_graph (a b : K) : action α hα (on,1) (a,b) = (α a,α b) := by simp [action, MulEquiv.prodCongr]
@[simp] theorem action_swap (a b : K) : action α hα (1,on) (a,b) = (b,a) := by simp [action, MulEquiv.prodCongr]
@[simp] theorem action_graphSwap (a b : K) : action α hα (on,on) (a,b) = (α b,α a) := by simp [action, MulEquiv.prodCongr]

@[simp] theorem mk_one : mk α hα 1 1 1 1 = 1 := rfl
@[simp] theorem mk_mul (a b c d : K) (p q r s : Bit) :
    mk α hα a b p q * mk α hα c d r s =
      mk α hα (a * (action α hα (p,q) (c,d)).1)
        (b * (action α hα (p,q) (c,d)).2) (p*r) (q*s) := rfl
@[simp] theorem mk_inv (a b : K) (p q : Bit) :
    (mk α hα a b p q)⁻¹ =
      mk α hα ((action α hα (p⁻¹,q⁻¹) (a⁻¹,b⁻¹)).1)
        ((action α hα (p⁻¹,q⁻¹) (a⁻¹,b⁻¹)).2) p⁻¹ q⁻¹ := rfl
@[simp] theorem base_inv (a b : K) : (base α hα a b)⁻¹ = base α hα a⁻¹ b⁻¹ := by simp [base]
@[simp] theorem base_conj (a b c d : K) :
  base α hα a b * base α hα c d * (base α hα a b)⁻¹ =
    base α hα (a*c*a⁻¹) (b*d*b⁻¹) := by simp [base]

theorem swap_conj_base (a b : K) :
  swap α hα * base α hα a b * (swap α hα)⁻¹ = base α hα b a := by
  simp [swap,base]

theorem conjugate_swap (a : K) :
  base α hα a⁻¹ 1 * mk α hα a a⁻¹ 1 on * (base α hα a⁻¹ 1)⁻¹ = swap α hα := by
  simp [swap,base]

theorem conjugate_graphSwap (a : K) :
  base α hα a⁻¹ 1 * mk α hα a (α a⁻¹) on on *
    (base α hα a⁻¹ 1)⁻¹ = graphSwap α hα := by
  simp [graphSwap,base]

theorem conjugate_graph (a b c d : K) :
  base α hα c d * mk α hα a b on 1 * (base α hα c d)⁻¹ =
    mk α hα (c*a*(α c)⁻¹) (d*b*(α d)⁻¹) on 1 := by
  simp [base]

end Theory.GroupTheory.PairedInvolutiveExtension
