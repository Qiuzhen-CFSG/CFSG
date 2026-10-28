module
public import Theory.SpecificGroups.GL2.DiagonalSwap
public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# A concrete cyclic-four wreath subgroup in GL₂(5)

The unit group of the five-element field is cyclic of order four. A regular
wreath-product element is sent to its diagonal pair of units followed by
the coordinate swap selected by its top coordinate. The two possible top
coordinates prove the multiplication law. Diagonal versus off-diagonal
entries recover that coordinate, and the nonzero entries recover both
base coordinates, so the matrix homomorphism is injective. Its image has
order 32.

The model is literally C₄ wr C₂, with cyclic four in each diagonal factor.
This supplies the GL₂(5) Sylow model used in the source normalizer action
of Aschbacher–Smith J.3. The general diagonal-and-swap matrices are from
`GL2.DiagonalSwap`; no matrix-group enumeration is used.
-/

@[expose] public noncomputable section
namespace Matrix.GeneralLinearGroup.FiveWreathSylow
open scoped Matrix
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
abbrev C2 := Multiplicative (ZMod 2)
abbrev C4 := Multiplicative (ZMod 4)
abbrev Wreath := RegularWreathProduct C4 C2
abbrev UnitWreath := RegularWreathProduct (ZMod 5)ˣ C2
abbrev tau : C2 := Multiplicative.ofAdd 1

theorem two_cases (x : C2) : x=1 ∨ x=tau := by
  change x.toAdd=0 ∨ x.toAdd=1
  exact (by decide +kernel : ∀ z : ZMod 2, z=0 ∨ z=1) x.toAdd

@[simp] theorem tau_ne_one : tau ≠ 1 := by decide
@[simp] theorem tau_mul_tau : tau*tau=1 := by decide
@[simp] theorem tau_inv : tau⁻¹=tau := by decide

def switch (x : C2) : GL (Fin 2) (ZMod 5) := if x=1 then 1 else coordinateSwap (ZMod 5)

def monomial (w : UnitWreath) : GL (Fin 2) (ZMod 5) :=
  diagonalPair (ZMod 5) (w.left 1,w.left tau) * switch w.right

theorem monomial_one : monomial 1 = 1 := by
  change diagonalPair (ZMod 5) 1 * switch 1 = 1
  rw [map_one,one_mul]
  simp [switch]

theorem monomial_mul (a b : UnitWreath) : monomial (a*b) = monomial a * monomial b := by
  rcases two_cases a.right with ha | ha <;> rcases two_cases b.right with hb | hb
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [monomial,switch,RegularWreathProduct.mul_def,ha,hb,
        diagonalPair_val,coordinateSwap_val,Matrix.mul_apply,Fin.sum_univ_two]

def monomialHom : UnitWreath →* GL (Fin 2) (ZMod 5) where
  toFun := monomial
  map_one' := monomial_one
  map_mul' := monomial_mul

theorem monomialHom_injective : Function.Injective monomialHom := by
  intro a b hab
  have hr : a.right=b.right := by
    rcases two_cases a.right with ha | ha <;> rcases two_cases b.right with hb | hb
    · exact ha.trans hb.symm
    · have hh := congrArg (fun x : GL (Fin 2) (ZMod 5) => x.val 0 0) hab
      simp [monomialHom,monomial,switch,ha,hb,diagonalPair_val,coordinateSwap_val,
        Matrix.mul_apply,Fin.sum_univ_two] at hh
    · have hh := congrArg (fun x : GL (Fin 2) (ZMod 5) => x.val 0 0) hab
      simp [monomialHom,monomial,switch,ha,hb,diagonalPair_val,coordinateSwap_val,
        Matrix.mul_apply,Fin.sum_univ_two] at hh
      exact ((b.left 1).ne_zero hh.symm).elim
    · exact ha.trans hb.symm
  apply RegularWreathProduct.ext ?_ hr
  have hd : diagonalPair (ZMod 5) (a.left 1,a.left tau) =
      diagonalPair (ZMod 5) (b.left 1,b.left tau) := by
    apply mul_right_cancel (b := switch b.right)
    simpa only [monomialHom,MonoidHom.coe_mk,OneHom.coe_mk,monomial,hr] using hab
  have hv := diagonalPair_injective (ZMod 5) hd
  funext x
  rcases two_cases x with rfl | rfl
  · exact congrArg Prod.fst hv
  · exact congrArg Prod.snd hv

def cyclicUnitEquiv : C4 ≃* (ZMod 5)ˣ :=
  mulEquivOfCyclicCardEq (by
    change Nat.card (ZMod 4) = Nat.card (ZMod 5)ˣ
    norm_num [Nat.card_units]
    decide)

def wreathUnitEquiv : Wreath ≃* UnitWreath :=
  RegularWreathProduct.congr cyclicUnitEquiv (MulEquiv.refl C2)

def wreathHom : Wreath →* GL (Fin 2) (ZMod 5) := monomialHom.comp wreathUnitEquiv.toMonoidHom

theorem wreathHom_injective : Function.Injective wreathHom :=
  monomialHom_injective.comp wreathUnitEquiv.injective

def monomialSubgroup : Subgroup (GL (Fin 2) (ZMod 5)) := wreathHom.range

def wreathSubgroupEquiv : Wreath ≃* monomialSubgroup := MonoidHom.ofInjective wreathHom_injective

theorem wreath_card : Nat.card Wreath = 32 := by
  rw [RegularWreathProduct.card]
  change Nat.card (ZMod 4) ^ Nat.card (ZMod 2) * Nat.card (ZMod 2) = 32
  norm_num

theorem monomialSubgroup_card : Nat.card monomialSubgroup = 32 :=
  (Nat.card_congr wreathSubgroupEquiv.toEquiv).symm.trans wreath_card

end Matrix.GeneralLinearGroup.FiveWreathSylow
