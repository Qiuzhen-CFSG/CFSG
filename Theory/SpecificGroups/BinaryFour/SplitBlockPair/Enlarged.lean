module
public import Theory.SpecificGroups.BinaryFour.SplitBlockPair
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.FieldTheory.Finiteness

/-!
# The split binary four-space enlarged by a trivial plane

The marked parabolic and its common four-group act on the first factor and
fix the second factor pointwise. The rotating-cubic predicate retains its
literal normalization of that common four-group, nontrivial action on it,
fixation of the marked point, and movement of both coordinate factors.
These are concrete action conditions, not a classification assertion.

Source: Aschbacher–Smith, proof of 14.4.4, printed p.1007; the enlarged
space retains the possible central kernel in the ambient source argument.
-/

@[expose] public section
namespace BinarySixSplitPair
open scoped IsMulCommutative
abbrev E₂ := Multiplicative (Fin 2 → ZMod 2)
abbrev E := BinaryFourSplitPair.E × E₂

def extend : MulAut BinaryFourSplitPair.E →* MulAut E where
  toFun x := x.prodCongr (MulEquiv.refl E₂)
  map_one' := by ext x <;> rfl
  map_mul' x y := by ext v <;> rfl

theorem extend_injective : Function.Injective extend := by
  intro f g he
  apply MulEquiv.ext
  intro v
  exact congrArg Prod.fst (DFunLike.congr_fun he (v,1))

def overlap : Subgroup (MulAut E) := BinaryFourSplitPair.overlap.map extend
def parabolic : Subgroup (MulAut E) := BinaryFourSplitPair.parabolic.map extend
def leftFactor : Subgroup E := (⊤ : Subgroup BinaryFourSplitPair.E).prod ⊥
def rightFactor : Subgroup E := (⊥ : Subgroup BinaryFourSplitPair.E).prod ⊤
def point : E := (BinaryFourSplitPair.point,1)

/-- Conditions on the actual enlarged cubic, stated entirely in one concrete
six-dimensional binary space. -/
def RotatingCubic (q : MulAut E) : Prop :=
  q^3=1 ∧ q point=point ∧
  q ∈ Subgroup.normalizer (overlap : Set (MulAut E)) ∧
  q ∉ Subgroup.centralizer (overlap : Set (MulAut E)) ∧
  leftFactor.map q.toMonoidHom ≠ leftFactor ∧
  rightFactor.map q.toMonoidHom ≠ rightFactor

/-- A binary four-group has the specified two-dimensional coordinates. -/
theorem coordinates_four (D : Type*) [Group D] [Finite D] [IsElementaryAbelian 2 D]
    (hD : Nat.card D=4) : Nonempty (D ≃* E₂) := by
  classical
  have hp : 2 ^ Module.finrank (ZMod 2) (Additive D) = 2 ^ 2 := by
    have hh := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive D)
    change Nat.card D = _ at hh
    simpa only [Nat.card_zmod,hD,show (2:ℕ)^2=4 from rfl] using hh.symm
  have hdim : Module.finrank (ZMod 2) (Additive D)=2 :=
    Nat.pow_right_injective (by decide : 1<2) hp
  exact ⟨(Module.finBasisOfFinrankEq (ZMod 2) (Additive D) hdim).equivFun.toAddEquiv.toMultiplicativeRight⟩
end BinarySixSplitPair
