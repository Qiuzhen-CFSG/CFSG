module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.Basic
public import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# A cyclic-coordinate Sylow three-subgroup of the actual Sp₄(3)

The symmetric matrices I, [-1,1;1,1], and [-1,-1;-1,1] form a basis of
Sym₂(F₃). The Levi element [1,1;0,1] cycles these three matrices. Thus their
upper-block unipotents and this Levi element give a concrete embedding of
C₃³ ⋊ C₃ into the literal symplectic matrix group. The additional Levi matrix
[1,1;1,-1] fixes the second basis vector and negates the first and third.
These relations supply partial inverters for the central-cover calculation.

Source: the defining-prime multiplier calculation underlying
Aschbacher–Smith I.1.4(1), printed p.408, and GLS3 §6.1. All matrices here
use the e₀,e₁,f₀,f₁ convention of `Matrix.symplecticGroup (Fin 2)`.
-/

@[expose] public section
noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.ThreePrimary
open Matrix
abbrev K := ZMod 3
abbrev V := Fin 3 → K
abbrev G := OddPrime.Sp K

/-- The cubic cyclic parametrization, for any group. -/
def cubicHom {H : Type*} [Group H] (g : H) (hg : g ^ 3 = 1) :
    Multiplicative K →* H where
  toFun x := g ^ x.toAdd.val
  map_one' := by simp
  map_mul' x y := by
    change g ^ (x.toAdd + y.toAdd).val = g ^ x.toAdd.val * g ^ y.toAdd.val
    rw [ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ hg).symm

@[simp] theorem cubicHom_one {H : Type*} [Group H] (g : H) (hg : g ^ 3 = 1) :
    cubicHom g hg (.ofAdd 1) = g := by change g ^ 1 = g; exact pow_one g

/-- Cyclic permutation of the three symmetric coordinates. -/
def rotate : MulAut (Multiplicative V) where
  toFun x := .ofAdd ![x.toAdd 2, x.toAdd 0, x.toAdd 1]
  invFun x := .ofAdd ![x.toAdd 1, x.toAdd 2, x.toAdd 0]
  left_inv x := by apply Multiplicative.toAdd.injective; funext i; fin_cases i <;> rfl
  right_inv x := by apply Multiplicative.toAdd.injective; funext i; fin_cases i <;> rfl
  map_mul' x y := by apply Multiplicative.toAdd.injective; funext i; fin_cases i <;> rfl

theorem rotate_cube : rotate ^ 3 = 1 := by
  ext x i
  fin_cases i <;> rfl

def action : Multiplicative K →* MulAut (Multiplicative V) := cubicHom rotate rotate_cube

/-- The abstract group only organizes coordinates; `embedding` connects it to matrices. -/
abbrev Model := SemidirectProduct (Multiplicative V) (Multiplicative K) action

/-- The elementary abelian subgroup of symmetric upper-block matrices. -/
def u (x : V) : G :=
  ⟨fromBlocks 1 !![x 0-x 1-x 2, x 1-x 2; x 1-x 2, x 0+x 1+x 2] 0 1, by
    rw [SymplecticGroup.fromBlocks_mem_iff]
    refine ⟨by simp, ?_, by simp⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp⟩

theorem u_add (x y : V) : u (x+y) = u x * u y := by
  apply Subtype.ext
  change _ = (u x).val * (u y).val
  simp only [u, fromBlocks_multiply, one_mul, mul_one, mul_zero, zero_mul, add_zero, zero_add]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

@[simp] theorem u_zero : u 0 = 1 := by
  apply Subtype.ext
  simp only [u, Pi.zero_apply, sub_zero, add_zero]
  have hz : (!![0, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K) = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [hz, fromBlocks_one]
  rfl

def uHom : Multiplicative V →* G where
  toFun x := u x.toAdd
  map_one' := u_zero
  map_mul' x y := u_add x.toAdd y.toAdd

theorem u_injective : Function.Injective u := by
  intro x y h
  have h00 := congrArg (fun g : G => g.val (.inl 0) (.inr 0)) h
  have h01 := congrArg (fun g : G => g.val (.inl 0) (.inr 1)) h
  have h11 := congrArg (fun g : G => g.val (.inl 1) (.inr 1)) h
  change x 0-x 1-x 2 = y 0-y 1-y 2 at h00
  change x 1-x 2 = y 1-y 2 at h01
  change x 0+x 1+x 2 = y 0+y 1+y 2 at h11
  funext i
  fin_cases i
  · change x 0 = y 0
    have hh : 2 * (x 0-y 0) = 0 := by linear_combination h00 + h11
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by decide))
  · change x 1 = y 1
    have hh : 4 * (x 1-y 1) = 0 := by linear_combination -h00 + 2*h01 + h11
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by decide))
  · change x 2 = y 2
    have hh : 4 * (x 2-y 2) = 0 := by linear_combination -h00 - 2*h01 + h11
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by decide))

/-- A short-root element cycling the chosen three coordinates. -/
def c : G :=
  ⟨fromBlocks !![1,1;0,1] 0 0 !![1,0;-1,1], by
    rw [SymplecticGroup.fromBlocks_mem_iff]; decide⟩

/-- A partial inverter in the actual Levi factor. -/
def h : G :=
  ⟨fromBlocks !![1,1;1,-1] 0 0 !![-1,-1;-1,1], by
    rw [SymplecticGroup.fromBlocks_mem_iff]; decide⟩

/-- The diagonal matrix inverting the short-root element. -/
def d : G :=
  ⟨fromBlocks !![-1,0;0,1] 0 0 !![-1,0;0,1], by
    rw [SymplecticGroup.fromBlocks_mem_iff]; decide⟩

theorem c_cube : c ^ 3 = 1 := by decide

theorem c_mul_u (x : V) : c * u x = u ![x 2,x 0,x 1] * c := by
  apply Subtype.ext
  change c.val * (u x).val = (u _).val * c.val
  simp only [c, u, fromBlocks_multiply, one_mul, mul_one, mul_zero, zero_mul, add_zero, zero_add]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;> simp only [show (2 : K) = -1 from rfl] <;> ring

theorem h_mul_u (x : V) : h * u x = u ![-x 0,x 1,-x 2] * h := by
  apply Subtype.ext
  change h.val * (u x).val = (u _).val * h.val
  simp only [h, u, fromBlocks_multiply, one_mul, mul_one, mul_zero, zero_mul, add_zero, zero_add]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem d_conjugate_c : d*c*d⁻¹ = c⁻¹ := by
  have hd : d⁻¹ = d := inv_eq_of_mul_eq_one_right (by decide : d * d = 1)
  rw [hd, eq_inv_iff_mul_eq_one]
  apply Subtype.ext
  change ((d.val * c.val) * d.val) * c.val = 1
  norm_num [d, c, fromBlocks_multiply, Matrix.mul_apply, Fin.sum_univ_two,
    ← Matrix.one_fin_two]

/-- Extend the generator conjugation relation to all its natural powers. -/
theorem conjugate_pow {A H : Type*} [Group A] [Group H]
    (v : A →* H) (r : MulAut A) (t : H)
    (ht : ∀ x, t * v x * t⁻¹ = v (r x)) (n : ℕ) (x : A) :
    t ^ n * v x * (t ^ n)⁻¹ = v ((r ^ n) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' t, _root_.mul_inv_rev]
    calc
      t * t ^ n * v x * ((t ^ n)⁻¹ * t⁻¹) =
          t * (t ^ n * v x * (t ^ n)⁻¹) * t⁻¹ := by simp only [mul_assoc]
      _ = v (r ((r ^ n) x)) := by rw [ih, ht]
      _ = v ((r ^ (n+1)) x) := by rw [pow_succ']; rfl

/-- The concrete matrix embedding of C₃³ ⋊ C₃. -/
def embedding : Model →* G :=
  SemidirectProduct.lift uHom (cubicHom c c_cube) (by
    intro k
    apply MonoidHom.ext
    intro x
    exact (conjugate_pow uHom rotate c (fun x => by
      change c * u x.toAdd * c⁻¹ = u _
      rw [c_mul_u, mul_inv_cancel_right]
      rfl) k.toAdd.val x).symm)

@[simp] theorem embedding_apply (x : Model) :
    embedding x = u x.left.toAdd * c ^ x.right.toAdd.val := rfl

/-- The upper-right entry of the Levi block recovers its cyclic parameter. -/
theorem cubic_c_matrix (k : K) :
    (c ^ k.val).val = fromBlocks !![1,k;0,1] 0 0 !![1,0;-k,1] := by
  fin_cases k <;> decide

theorem embedding_injective : Function.Injective embedding := by
  intro x y he
  have hk := congrArg (fun g : G => g.val (.inl 0) (.inl 1)) he
  have hr : x.right = y.right := by
    apply Multiplicative.toAdd.injective
    change ((u x.left.toAdd).val * (c ^ x.right.toAdd.val).val) (.inl 0) (.inl 1) =
      ((u y.left.toAdd).val * (c ^ y.right.toAdd.val).val) (.inl 0) (.inl 1) at hk
    rw [cubic_c_matrix, cubic_c_matrix] at hk
    simp only [u, fromBlocks_multiply, mul_zero, add_zero, one_mul] at hk
    exact hk
  have hl : x.left = y.left := by
    apply Multiplicative.toAdd.injective
    apply u_injective
    simpa only [embedding_apply, hr, mul_right_cancel_iff] using he
  exact SemidirectProduct.ext hl hr

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.ThreePrimary
end
