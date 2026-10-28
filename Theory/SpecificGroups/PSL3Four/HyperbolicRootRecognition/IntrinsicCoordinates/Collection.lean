module

public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.BinaryModel
public import Mathlib.Tactic.Group

/-!
# Collecting binary words with central correction terms

The square and swap relations for four lifts imply exactly the multiplication
cocycle of `Word`. We collect two binary letters at a time, commuting central
corrections past later letters. This proves that ordered evaluation is a group
homomorphism without assuming a presentation or a normal-form theorem.

The intrinsic generator construction consumes these relations in `Frames`;
its final application constructs the marked coordinates of hyperbolic factors.
Source motivation: Aschbacher, *Sporadic Groups* (1994), 8.15 and
the proof of 45.3, printed pp.242–243.
-/

@[expose] public section
namespace Theory.GroupTheory.HyperbolicRecognition.Intrinsic
open Subgroup
variable {K : Type*} [Group K]

/-- Evaluate a binary central coordinate in an actual center. -/
def centralEval (e : Multiplicative Central →* center K) (r : Central) : K :=
  e (Multiplicative.ofAdd r)

@[simp] theorem centralEval_zero (e : Multiplicative Central →* center K) :
    centralEval e 0 = 1 := congrArg Subtype.val (map_one e)

theorem centralEval_add (e : Multiplicative Central →* center K) (r s : Central) :
    centralEval e (r+s) = centralEval e r * centralEval e s :=
  congrArg Subtype.val (map_mul e (Multiplicative.ofAdd r) (Multiplicative.ofAdd s))

theorem centralEval_comm (e : Multiplicative Central →* center K) (r : Central) (x : K) :
    centralEval e r * x = x * centralEval e r :=
  (mem_center_iff.mp (e (Multiplicative.ofAdd r)).property x).symm

/-- Multiplication by one binary coefficient in the central plane. -/
def scale (i : Bit) (r : Central) : Central := (i*r.1, i*r.2)

@[simp] theorem scale_zero (r : Central) : scale 0 r = 0 := by ext <;> simp [scale]
@[simp] theorem scale_one (r : Central) : scale 1 r = r := by ext <;> simp [scale]

def bitPower (x : K) (i : Bit) : K := x ^ i.val
@[simp] theorem bitPower_zero (x : K) : bitPower x 0 = 1 := by simp [bitPower]
@[simp] theorem bitPower_one (x : K) : bitPower x 1 = x := by simp [bitPower, ZMod.val_one]

variable (e : Multiplicative Central →* center K)

private theorem merge_central (x y : K) (r s : Central) :
    (x * centralEval e r) * (y * centralEval e s) =
      (x*y) * centralEval e (r+s) := by
  rw [centralEval_add]
  calc
    _ = x * (centralEval e r * y) * centralEval e s := by simp only [mul_assoc]
    _ = x * (y * centralEval e r) * centralEval e s := by rw [centralEval_comm]
    _ = _ := by simp only [mul_assoc]

private theorem collect (x y z t : K) (r : Central)
    (h : y*z = z*y*centralEval e r) :
    (x*y)*(z*t) = (x*z)*(y*t)*centralEval e r := by
  calc
    _ = x*(y*z)*t := by simp only [mul_assoc]
    _ = x*(z*y*centralEval e r)*t := by rw [h]
    _ = x*(z*y)*(centralEval e r*t) := by simp only [mul_assoc]
    _ = x*(z*y)*(t*centralEval e r) := by rw [centralEval_comm]
    _ = _ := by simp only [mul_assoc]

private theorem swap_product_left (x y z : K) (r s : Central)
    (hx : x*z = z*x*centralEval e r) (hy : y*z = z*y*centralEval e s) :
    (x*y)*z = z*(x*y)*centralEval e (r+s) := by
  calc
    _ = x*(y*z) := mul_assoc _ _ _
    _ = x*(z*y*centralEval e s) := by rw [hy]
    _ = (x*z)*y*centralEval e s := by simp only [mul_assoc]
    _ = (z*x*centralEval e r)*y*centralEval e s := by rw [hx]
    _ = (z*x)*(centralEval e r*y)*centralEval e s := by simp only [mul_assoc]
    _ = (z*x)*(y*centralEval e r)*centralEval e s := by rw [centralEval_comm]
    _ = _ := by rw [centralEval_add]; simp only [mul_assoc]

private theorem swap_product_right (x y z : K) (r s : Central)
    (hx : x*y = y*x*centralEval e r) (hy : x*z = z*x*centralEval e s) :
    x*(y*z) = (y*z)*x*centralEval e (r+s) := by
  calc
    _ = (x*y)*z := (mul_assoc _ _ _).symm
    _ = (y*x*centralEval e r)*z := by rw [hx]
    _ = (y*x)*(centralEval e r*z) := mul_assoc _ _ _
    _ = (y*x)*(z*centralEval e r) := by rw [centralEval_comm]
    _ = y*(x*z)*centralEval e r := by simp only [mul_assoc]
    _ = y*(z*x*centralEval e s)*centralEval e r := by rw [hy]
    _ = (y*z)*x*centralEval e (s+r) := by rw [centralEval_add]; simp only [mul_assoc]
    _ = _ := by rw [add_comm s r]

private theorem bitPower_mul (x : K) (r : Central) (hs : x^2 = centralEval e r)
    (i j : Bit) :
    bitPower x i * bitPower x j = bitPower x (i+j) * centralEval e (scale (i*j) r) := by
  fin_cases i <;> fin_cases j
  · change x^0*x^0 = x^0*centralEval e (scale 0 r); simp
  · change x^0*x^1 = x^1*centralEval e (scale 0 r); simp
  · change x^1*x^0 = x^1*centralEval e (scale 0 r); simp
  · change x^1*x^1 = x^0*centralEval e (scale 1 r); simpa [pow_two] using hs

private theorem bitPower_swap (x y : K) (r : Central)
    (hs : y*x = x*y*centralEval e r) (i j : Bit) :
    bitPower y j * bitPower x i =
      bitPower x i * bitPower y j * centralEval e (scale (j*i) r) := by
  fin_cases i <;> fin_cases j
  · change y^0*x^0 = x^0*y^0*centralEval e (scale 0 r); simp
  · change y^1*x^0 = x^0*y^1*centralEval e (scale 0 r); simp
  · change y^0*x^1 = x^1*y^0*centralEval e (scale 0 r); simp
  · change y^1*x^1 = x^1*y^1*centralEval e (scale 1 r); simpa using hs

def pairWord (a b : K) (v : Central) : K := bitPower a v.1 * bitPower b v.2

private theorem pairWord_mul (a b : K) (sa sb r : Central)
    (ha : a^2 = centralEval e sa) (hb : b^2 = centralEval e sb)
    (hs : b*a = a*b*centralEval e r) (v w : Central) :
    pairWord a b v * pairWord a b w =
      pairWord a b (v+w) * centralEval e
        (scale (v.1*w.1) sa + scale (v.2*w.2) sb + scale (v.2*w.1) r) := by
  unfold pairWord
  rw [collect e _ _ _ _ _ (bitPower_swap e a b r hs _ _),
    bitPower_mul e a sa ha, bitPower_mul e b sb hb, merge_central,
    mul_assoc, ← centralEval_add]
  rfl

private theorem pairWord_swap (a b c d : K) (M : Cross)
    (hac : c*a = a*c*centralEval e M.ac) (had : d*a = a*d*centralEval e M.ad)
    (hbc : c*b = b*c*centralEval e M.bc) (hbd : d*b = b*d*centralEval e M.bd)
    (v w : Central) :
    pairWord c d v * pairWord a b w = pairWord a b w * pairWord c d v *
      centralEval e (scale (v.1*w.1) M.ac + scale (v.2*w.1) M.ad +
        (scale (v.1*w.2) M.bc + scale (v.2*w.2) M.bd)) := by
  exact swap_product_right e _ _ _ _ _
    (swap_product_left e _ _ _ _ _ (bitPower_swap e _ _ _ hac _ _)
      (bitPower_swap e _ _ _ had _ _))
    (swap_product_left e _ _ _ _ _ (bitPower_swap e _ _ _ hbc _ _)
      (bitPower_swap e _ _ _ hbd _ _))

/-- The literal square and swap relations needed by the published cocycle. -/
structure CollectionRelations (M : Cross) (a b c d : K) : Prop where
  a_square : a^2 = centralEval e 0
  b_square : b^2 = centralEval e 0
  c_square : c^2 = centralEval e 0
  d_square : d^2 = centralEval e 0
  ba : b*a = a*b*centralEval e cz
  dc : d*c = c*d*centralEval e cu
  ca : c*a = a*c*centralEval e M.ac
  da : d*a = a*d*centralEval e M.ad
  cb : c*b = b*c*centralEval e M.bc
  db : d*b = b*d*centralEval e M.bd

def vectorWord (a b c d : K) (v : Vector) : K := pairWord a b v.1 * pairWord c d v.2

private theorem vectorWord_mul {a b c d : K} {M : Cross}
    (h : CollectionRelations e M a b c d) (v w : Vector) :
    vectorWord a b c d v * vectorWord a b c d w =
      vectorWord a b c d (v+w) * centralEval e (cocycle M v w) := by
  unfold vectorWord
  rw [collect e _ _ _ _ _ (pairWord_swap e _ _ _ _ M h.ca h.da h.cb h.db _ _),
    pairWord_mul e _ _ _ _ _ h.a_square h.b_square h.ba,
    pairWord_mul e _ _ _ _ _ h.c_square h.d_square h.dc,
    merge_central, mul_assoc, ← centralEval_add]
  congr 2
  ext <;> dsimp [scale, cz, cu, cocycle] <;> ring

/-- Ordered evaluation of a binary normal word. -/
def wordEval {M : Cross} (a b c d : K) (x : Word M) : K :=
  vectorWord a b c d x.vector * centralEval e x.central

def wordHom {M : Cross} {a b c d : K} (h : CollectionRelations e M a b c d) : Word M →* K where
  toFun := wordEval e a b c d
  map_one' := by simp [wordEval, vectorWord, pairWord]
  map_mul' x y := by
    change vectorWord a b c d (x.vector+y.vector) *
      centralEval e (x.central+y.central+cocycle M x.vector y.vector) = _
    rw [show wordEval e a b c d x * wordEval e a b c d y =
      (vectorWord a b c d x.vector * vectorWord a b c d y.vector) *
        centralEval e (x.central+y.central) from merge_central e _ _ _ _,
      vectorWord_mul e h, mul_assoc, ← centralEval_add, add_comm (cocycle M _ _)]

end Theory.GroupTheory.HyperbolicRecognition.Intrinsic
