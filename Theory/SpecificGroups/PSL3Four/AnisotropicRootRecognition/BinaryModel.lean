module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FinCases
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Binary multiplication laws for two anisotropic planes

The carrier consists of the ordered words a^i b^j c^k d^l z^m u^n,
with binary exponents. The internal squares and commutators of a,b are z,
and those of c,d are u. Four central cross commutators determine the
remaining multiplication, through the explicit bilinear collection cocycle.
The group laws and square map are proved directly from that cocycle.

This is a multiplication model, not an assumed coordinate system on an
arbitrary group. Constructing such coordinates from `AnisotropicFactors`
and identifying the surviving models with UT₃(F₄) are separate obligations.
Source motivation: Aschbacher, *Sporadic Groups* (1994), 8.15, 46.2–46.3
and the proof of 46.14, printed pp.29–30,251,257–258.
-/

@[expose] public section
namespace Theory.GroupTheory.AnisotropicRecognition

abbrev Bit := ZMod 2
abbrev Central := Bit × Bit
abbrev Vector := (Bit × Bit) × (Bit × Bit)

/-- The four cross commutators, in order ac, ad, bc, bd. -/
@[ext] structure Cross where
  ac : Central
  ad : Central
  bc : Central
  bd : Central
  deriving DecidableEq, Fintype

/-- The collection cocycle for the ordered word a^i b^j c^k d^l z^m u^n. -/
def cocycle (M : Cross) (v w : Vector) : Central :=
  (v.1.1 * w.1.1 + v.1.2 * w.1.2 + v.1.2 * w.1.1 +
    v.2.1 * w.1.1 * M.ac.1 + v.2.2 * w.1.1 * M.ad.1 +
    v.2.1 * w.1.2 * M.bc.1 + v.2.2 * w.1.2 * M.bd.1,
   v.2.1 * w.2.1 + v.2.2 * w.2.2 + v.2.2 * w.2.1 +
    v.2.1 * w.1.1 * M.ac.2 + v.2.2 * w.1.1 * M.ad.2 +
    v.2.1 * w.1.2 * M.bc.2 + v.2.2 * w.1.2 * M.bd.2)

@[simp] theorem cocycle_zero_left (M : Cross) (v : Vector) : cocycle M 0 v = 0 := by
  ext <;> simp [cocycle]
@[simp] theorem cocycle_zero_right (M : Cross) (v : Vector) : cocycle M v 0 = 0 := by
  ext <;> simp [cocycle]

theorem cocycle_add_left (M : Cross) (u v w : Vector) :
    cocycle M (u + v) w = cocycle M u w + cocycle M v w := by
  ext <;> dsimp [cocycle] <;> ring

theorem cocycle_add_right (M : Cross) (u v w : Vector) :
    cocycle M u (v + w) = cocycle M u v + cocycle M u w := by
  ext <;> dsimp [cocycle] <;> ring

/-- The 64 normal words equipped with their actual multiplication. -/
@[ext] structure Word (M : Cross) where
  vector : Vector
  central : Central
  deriving DecidableEq, Fintype

instance (M : Cross) : Mul (Word M) :=
  ⟨fun x y => ⟨x.vector + y.vector, x.central + y.central + cocycle M x.vector y.vector⟩⟩
instance (M : Cross) : One (Word M) := ⟨⟨0, 0⟩⟩
instance (M : Cross) : Inv (Word M) :=
  ⟨fun x => ⟨x.vector, x.central + cocycle M x.vector x.vector⟩⟩

theorem central_add_self (c : Central) : c + c = 0 := by
  ext <;> exact CharTwo.add_self_eq_zero _
theorem vector_add_self (v : Vector) : v + v = 0 := by
  ext <;> exact CharTwo.add_self_eq_zero _

instance (M : Cross) : Group (Word M) where
  mul_assoc x y z := by
    apply Word.ext
    · exact add_assoc _ _ _
    · change (x.central + y.central + cocycle M x.vector y.vector) + z.central +
        cocycle M (x.vector + y.vector) z.vector =
        x.central + (y.central + z.central + cocycle M y.vector z.vector) +
          cocycle M x.vector (y.vector + z.vector)
      rw [cocycle_add_left, cocycle_add_right]
      abel
  one_mul x := by
    apply Word.ext
    · exact zero_add _
    · change 0 + x.central + cocycle M 0 x.vector = _
      simp
  mul_one x := by
    apply Word.ext
    · exact add_zero _
    · change x.central + 0 + cocycle M x.vector 0 = _
      simp
  inv_mul_cancel x := by
    apply Word.ext
    · exact vector_add_self _
    · change (x.central + cocycle M x.vector x.vector) + x.central +
        cocycle M x.vector x.vector = 0
      calc
        _ = (x.central + x.central) +
            (cocycle M x.vector x.vector + cocycle M x.vector x.vector) := by abel
        _ = 0 := by rw [central_add_self, central_add_self, zero_add]

variable {M : Cross}

@[simp] theorem mul_vector (x y : Word M) : (x * y).vector = x.vector + y.vector := rfl
@[simp] theorem mul_central (x y : Word M) :
    (x * y).central = x.central + y.central + cocycle M x.vector y.vector := rfl
@[simp] theorem one_vector : (1 : Word M).vector = 0 := rfl
@[simp] theorem one_central : (1 : Word M).central = 0 := rfl

def centralWord (M : Cross) (c : Central) : Word M := ⟨0, c⟩
def lift (M : Cross) (v : Vector) : Word M := ⟨v, 0⟩
def quadratic (M : Cross) (v : Vector) : Central := cocycle M v v

theorem square_word (x : Word M) : x ^ 2 = centralWord M (quadratic M x.vector) := by
  rw [pow_two]
  apply Word.ext
  · exact vector_add_self _
  · change x.central + x.central + cocycle M x.vector x.vector = _
    rw [central_add_self, zero_add]
    rfl

theorem commute_iff (x y : Word M) :
    x * y = y * x ↔ cocycle M x.vector y.vector = cocycle M y.vector x.vector := by
  constructor
  · intro h
    have hc := congrArg Word.central h
    simpa only [mul_central, add_comm y.central x.central, add_left_cancel_iff] using hc
  · intro h
    apply Word.ext
    · exact add_comm _ _
    · simpa only [mul_central, add_comm y.central x.central] using
        congrArg (x.central + y.central + ·) h

def va : Vector := ((1, 0), (0, 0))
def vb : Vector := ((0, 1), (0, 0))
def cz : Central := (1, 0)
def cu : Central := (0, 1)
def czu : Central := (1, 1)

def FirstNondegenerate (M : Cross) : Prop :=
  ∀ v : Vector, cocycle M v va = cocycle M va v →
    cocycle M v vb = cocycle M vb v → v = 0

instance (M : Cross) : Decidable (FirstNondegenerate M) := by
  unfold FirstNondegenerate
  infer_instance

def fiberCount (M : Cross) (c : Central) : ℕ :=
  (Finset.univ.filter fun v : Vector => quadratic M v = c).card

def Balanced (M : Cross) : Prop :=
  fiberCount M cz = fiberCount M cu ∧ fiberCount M cu = fiberCount M czu

instance (M : Cross) : Decidable (Balanced M) := by
  unfold Balanced
  infer_instance

def SixCases (M : Cross) : Prop :=
  M = ⟨0, czu, czu, 0⟩ ∨ M = ⟨0, czu, czu, czu⟩ ∨
  M = ⟨czu, 0, 0, czu⟩ ∨ M = ⟨czu, 0, czu, czu⟩ ∨
  M = ⟨czu, czu, 0, czu⟩ ∨ M = ⟨czu, czu, czu, 0⟩

instance (M : Cross) : Decidable (SixCases M) := by
  unfold SixCases
  infer_instance

def wordEquivProd (M : Cross) : Word M ≃ Vector × Central where
  toFun x := (x.vector, x.central)
  invFun x := ⟨x.1, x.2⟩

@[simp] theorem card_Word (M : Cross) : Nat.card (Word M) = 64 := by
  rw [Nat.card_congr (wordEquivProd M), Nat.card_eq_fintype_card]
  decide

theorem centralWord_injective (M : Cross) : Function.Injective (centralWord M) :=
  fun _ _ h => congrArg Word.central h

@[simp] theorem centralWord_eq_one (M : Cross) (c : Central) :
    centralWord M c = 1 ↔ c = 0 := by
  constructor
  · exact fun h => congrArg Word.central h
  · rintro rfl
    rfl

theorem centralWord_mem_center (M : Cross) (c : Central) :
    centralWord M c ∈ Subgroup.center (Word M) := by
  apply Subgroup.mem_center_iff.mpr
  intro x
  apply (commute_iff _ _).mpr
  change cocycle M x.vector 0 = cocycle M 0 x.vector
  simp

/-- The subgroup spanned by a,b,z,u in the word model. -/
def firstPlane (M : Cross) : Subgroup (Word M) where
  carrier := {x | x.vector.2 = 0}
  one_mem' := rfl
  mul_mem' hx hy := by change _ + _ = _; rw [hx, hy, zero_add]
  inv_mem' hx := hx

@[simp] theorem mem_firstPlane (M : Cross) (x : Word M) :
    x ∈ firstPlane M ↔ x.vector.2 = 0 := Iff.rfl

theorem commute_firstPlane (M : Cross) (v : Vector)
    (ha : cocycle M v va = cocycle M va v)
    (hb : cocycle M v vb = cocycle M vb v)
    (w : Vector) (hw : w.2 = 0) : cocycle M v w = cocycle M w v := by
  rcases w with ⟨⟨a, b⟩, c⟩
  dsimp at hw
  subst c
  fin_cases a <;> fin_cases b
  · change cocycle M v 0 = cocycle M 0 v
    simp
  · exact hb
  · exact ha
  · change cocycle M v (va + vb) = cocycle M (va + vb) v
    rw [cocycle_add_left, cocycle_add_right, ha, hb]

def squareFiberCoordinates (M : Cross) (c : Central) :
    {x : Word M // x ^ 2 = centralWord M c} ≃
      {v : Vector // quadratic M v = c} × Central where
  toFun x := (⟨x.1.vector, (centralWord_injective M)
    ((square_word x.1).symm.trans x.2)⟩, x.1.central)
  invFun x := ⟨⟨x.1.1, x.2⟩, (square_word _).trans (congrArg (centralWord M) x.1.2)⟩
  left_inv _x := Subtype.ext rfl
  right_inv _x := rfl

theorem squareFiber_card (M : Cross) (c : Central) :
    Nat.card {x : Word M // x ^ 2 = centralWord M c} = 4 * fiberCount M c := by
  rw [Nat.card_congr (squareFiberCoordinates M c), Nat.card_prod]
  have hc : Nat.card Central = 4 := by rw [Nat.card_eq_fintype_card]; decide
  rw [hc, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact Nat.mul_comm _ _

end Theory.GroupTheory.AnisotropicRecognition
