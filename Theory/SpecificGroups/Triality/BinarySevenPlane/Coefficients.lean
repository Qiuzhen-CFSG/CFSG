module

public import Theory.SpecificGroups.Triality.BinarySevenPlane.Field
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.CharP.Two

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Eight-element coefficient arithmetic for the binary seven-plane

The tables implement F₂[T]/(T³+T+1). Their ring laws and three-coordinate
multiplication identities are checked by the kernel. Evaluation at a cubic
root is a ring homomorphism, proved structurally from those coordinate
identities. The final specialization maps into the literal triality extension
field and is injective. Thus matrix certificates over these coefficients can
be transported without replacing the triality carrier by a different model.

This supports the explicit nonsplit-torus construction at q = 2, motivated by
ATLAS, printed p.89. No subgroup or classification conclusion is assumed here.
-/

@[expose] public section
namespace Triality.Standard.BinarySevenPlane.Coefficients
structure Scalar where
  val : Fin 8
  deriving DecidableEq, Fintype

def addTable (a b : Fin 8) : Fin 8 :=
  ![![0,1,2,3,4,5,6,7], ![1,0,3,2,5,4,7,6],
    ![2,3,0,1,6,7,4,5], ![3,2,1,0,7,6,5,4],
    ![4,5,6,7,0,1,2,3], ![5,4,7,6,1,0,3,2],
    ![6,7,4,5,2,3,0,1], ![7,6,5,4,3,2,1,0]] a b

def mulTable (a b : Fin 8) : Fin 8 :=
  ![![0,0,0,0,0,0,0,0], ![0,1,2,3,4,5,6,7],
    ![0,2,4,6,3,1,7,5], ![0,3,6,5,7,4,1,2],
    ![0,4,3,7,6,2,5,1], ![0,5,1,4,2,7,3,6],
    ![0,6,7,1,5,3,2,4], ![0,7,5,2,1,6,4,3]] a b

instance : Zero Scalar := ⟨⟨0⟩⟩
instance : One Scalar := ⟨⟨1⟩⟩
instance : Add Scalar := ⟨fun a b => ⟨addTable a.val b.val⟩⟩
instance : Mul Scalar := ⟨fun a b => ⟨mulTable a.val b.val⟩⟩
instance : Neg Scalar := ⟨id⟩
private theorem raw_add_assoc : ∀ a b c : Fin 8, addTable (addTable a b) c = addTable a (addTable b c) := by decide +kernel
private theorem raw_zero_add : ∀ a : Fin 8, addTable 0 a = a := by decide +kernel
private theorem raw_add_zero : ∀ a : Fin 8, addTable a 0 = a := by decide +kernel
private theorem raw_add_comm : ∀ a b : Fin 8, addTable a b = addTable b a := by decide +kernel
private theorem raw_neg_add_cancel : ∀ a : Fin 8, addTable a a = 0 := by decide +kernel
private theorem raw_mul_assoc : ∀ a b c : Fin 8, mulTable (mulTable a b) c = mulTable a (mulTable b c) := by decide +kernel
private theorem raw_one_mul : ∀ a : Fin 8, mulTable 1 a = a := by decide +kernel
private theorem raw_mul_one : ∀ a : Fin 8, mulTable a 1 = a := by decide +kernel
private theorem raw_mul_zero : ∀ a : Fin 8, mulTable a 0 = 0 := by decide +kernel
private theorem raw_zero_mul : ∀ a : Fin 8, mulTable 0 a = 0 := by decide +kernel
private theorem raw_left_distrib : ∀ a b c : Fin 8, mulTable a (addTable b c) = addTable (mulTable a b) (mulTable a c) := by decide +kernel
private theorem raw_right_distrib : ∀ a b c : Fin 8, mulTable (addTable a b) c = addTable (mulTable a c) (mulTable b c) := by decide +kernel
private theorem raw_mul_comm : ∀ a b : Fin 8, mulTable a b = mulTable b a := by decide +kernel

instance : CommRing Scalar where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by exact fun ⟨a⟩ ⟨b⟩ ⟨c⟩ => congrArg Scalar.mk (raw_add_assoc a b c)
  zero_add := by exact fun ⟨a⟩ => congrArg Scalar.mk (raw_zero_add a)
  add_zero := by exact fun ⟨a⟩ => congrArg Scalar.mk (raw_add_zero a)
  add_comm := by exact fun ⟨a⟩ ⟨b⟩ => congrArg Scalar.mk (raw_add_comm a b)
  neg_add_cancel := by exact fun ⟨a⟩ => congrArg Scalar.mk (raw_neg_add_cancel a)
  mul_assoc := by exact fun ⟨a⟩ ⟨b⟩ ⟨c⟩ => congrArg Scalar.mk (raw_mul_assoc a b c)
  one_mul := by exact fun ⟨a⟩ => congrArg Scalar.mk (raw_one_mul a)
  mul_one := by exact fun ⟨a⟩ => congrArg Scalar.mk (raw_mul_one a)
  mul_zero := by exact fun ⟨a⟩ => congrArg Scalar.mk (raw_mul_zero a)
  zero_mul := by exact fun ⟨a⟩ => congrArg Scalar.mk (raw_zero_mul a)
  left_distrib := by exact fun ⟨a⟩ ⟨b⟩ ⟨c⟩ => congrArg Scalar.mk (raw_left_distrib a b c)
  right_distrib := by exact fun ⟨a⟩ ⟨b⟩ ⟨c⟩ => congrArg Scalar.mk (raw_right_distrib a b c)
  mul_comm := by exact fun ⟨a⟩ ⟨b⟩ => congrArg Scalar.mk (raw_mul_comm a b)


def bit0 (a : Fin 8) : ZMod 2 := ![0,1,0,1,0,1,0,1] a
def bit1 (a : Fin 8) : ZMod 2 := ![0,0,1,1,0,0,1,1] a
def bit2 (a : Fin 8) : ZMod 2 := ![0,0,0,0,1,1,1,1] a

private theorem bit0_add : ∀ a b, bit0 (addTable a b) = bit0 a + bit0 b := by decide +kernel
private theorem bit1_add : ∀ a b, bit1 (addTable a b) = bit1 a + bit1 b := by decide +kernel
private theorem bit2_add : ∀ a b, bit2 (addTable a b) = bit2 a + bit2 b := by decide +kernel
private theorem bit0_mul : ∀ a b, bit0 (mulTable a b) = bit0 a * bit0 b + bit1 a * bit2 b + bit2 a * bit1 b := by decide +kernel
private theorem bit1_mul : ∀ a b, bit1 (mulTable a b) = bit0 a * bit1 b + bit1 a * bit0 b + bit1 a * bit2 b + bit2 a * bit1 b + bit2 a * bit2 b := by decide +kernel
private theorem bit2_mul : ∀ a b, bit2 (mulTable a b) = bit0 a * bit2 b + bit1 a * bit1 b + bit2 a * bit0 b + bit2 a * bit2 b := by decide +kernel

instance scalarCharTwo : CharP Scalar 2 :=
  CharTwo.of_one_ne_zero_of_two_eq_zero
    (fun h => (show (1 : Fin 8) ≠ 0 by decide) (congrArg Scalar.val h))
    (congrArg Scalar.mk (show addTable 1 1 = 0 from rfl))

variable {F : Type*} [CommRing F] [CharP F 2]
def liftBit : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F

def eval (t : F) (a : Scalar) : F :=
  liftBit (bit0 a.val) + liftBit (bit1 a.val) * t + liftBit (bit2 a.val) * t^2

lemma eval_add (t : F) (a b : Scalar) : eval t (a+b) = eval t a + eval t b := by
  change liftBit (bit0 (addTable a.val b.val)) + liftBit (bit1 (addTable a.val b.val)) * t + liftBit (bit2 (addTable a.val b.val)) * t^2 = _
  rw [bit0_add, bit1_add, bit2_add]
  simp only [eval, map_add]
  ring

lemma eval_mul (t : F) (ht : t^3 = t+1) (a b : Scalar) :
    eval t (a*b) = eval t a * eval t b := by
  have ht4 : t^4 = t^2+t := by calc
    t^4 = t^3*t := by ring
    _ = t^2+t := by rw [ht]; ring
  change liftBit (bit0 (mulTable a.val b.val)) + liftBit (bit1 (mulTable a.val b.val)) * t + liftBit (bit2 (mulTable a.val b.val)) * t^2 = _
  rw [bit0_mul, bit1_mul, bit2_mul]
  simp only [eval, map_add, map_mul]
  linear_combination -(liftBit (bit1 a.val) * liftBit (bit2 b.val) +
    liftBit (bit2 a.val) * liftBit (bit1 b.val)) * ht -
    (liftBit (bit2 a.val) * liftBit (bit2 b.val)) * ht4

def evalHom (t : F) (ht : t^3=t+1) : Scalar →+* F where
  toFun := eval t
  map_zero' := by simp [eval, bit0, bit1, bit2, show (0 : Scalar).val = 0 from rfl]
  map_one' := by simp [eval, bit0, bit1, bit2, show (1 : Scalar).val = 1 from rfl]
  map_add' := eval_add t
  map_mul' := eval_mul t ht
private theorem inverse_table : ∀ a : Fin 8, a ≠ 0 →
    ∃ b : Fin 8, mulTable a b = 1 := by decide +kernel

/-- Evaluation is faithful in every nontrivial target admitting the cubic root. -/
theorem evalHom_injective [Nontrivial F] (t : F) (ht : t^3=t+1) :
    Function.Injective (evalHom t ht) := by
  apply (injective_iff_map_eq_zero (evalHom t ht).toAddMonoidHom).mpr
  intro a ha
  change evalHom t ht a = 0 at ha
  by_contra hn
  have hv : a.val ≠ 0 := fun h => hn (congrArg Scalar.mk h)
  obtain ⟨b, hb⟩ := inverse_table a.val hv
  have hm : a * (⟨b⟩ : Scalar) = 1 := congrArg Scalar.mk hb
  have hz : (1 : F) = 0 := by
    rw [← map_one (evalHom t ht), ← hm, map_mul, ha, zero_mul]
  exact one_ne_zero hz

/-- The certificate coefficients specialize to the field of the actual model. -/
noncomputable def actualMap : Scalar →+*
    ExtensionField (binaryParameters 1 Nat.zero_lt_one) :=
  evalHom generator generator_cubic

theorem actualMap_injective : Function.Injective actualMap :=
  evalHom_injective generator generator_cubic

end Triality.Standard.BinarySevenPlane.Coefficients
