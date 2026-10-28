module
import Mathlib.Tactic.Group
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.CentralCollection.Basic

/-!
# Word rewriting with central exponent vectors

Every equation records a literal word equality and the seven central relator
powers. Context, overlap, inversion, and cyclic splitting preserve this meaning.
The seed correction accounts for a⁻¹ = a c₀⁻¹.

Source: the seven Wilson–Nickerson–Bray ATLAS words `S62G1-P1.M`.
The certificate and its concrete source adapter are in the companion modules.
-/

@[expose] public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection.PowerReplay

def readWord {G : Type*} [Group G] (g : Fin 3 → G) (w : List (Fin 3)) : G :=
  (w.map g).prod

@[simp] theorem readWord_nil {G : Type*} [Group G] (g : Fin 3 → G) : readWord g [] = 1 := rfl
@[simp] theorem readWord_cons {G : Type*} [Group G] (g : Fin 3 → G)
    (a : Fin 3) (w : List (Fin 3)) : readWord g (a :: w) = g a * readWord g w := rfl

theorem readWord_append {G : Type*} [Group G] (g : Fin 3 → G) (u v : List (Fin 3)) :
    readWord g (u ++ v) = readWord g u * readWord g v := by
  simp [readWord, List.map_append, List.prod_append]

def Eqn (g : Fin 3 → Central) (u v : List (Fin 3)) (z : Fin 7 → ℤ) : Prop :=
  readWord g u = readWord g v * (collect z : Central)

theorem collect_neg (z : Fin 7 → ℤ) : collect (-z) = (collect z)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← collect_add, neg_add_cancel, collect_zero]

theorem eqn_change {g : Fin 3 → Central} {u v : List (Fin 3)} {z : Fin 7 → ℤ}
    (t : Fin 7 → ℤ) (h : Eqn g u v z) (ht : z = t) : Eqn g u v t := ht ▸ h


theorem eqn_cast {g : Fin 3 → Central} {u v : List (Fin 3)} {z : Fin 7 → ℤ}
    (u' v' : List (Fin 3)) (t : Fin 7 → ℤ) (h : Eqn g u v z)
    (hu : u = u') (hv : v = v') (ht : z = t) : Eqn g u' v' t := by
  subst u'; subst v'; subst t
  exact h


theorem eqn_refl (g : Fin 3 → Central) (u : List (Fin 3)) : Eqn g u u 0 := by
  simp [Eqn]

theorem eqn_symm {g : Fin 3 → Central} {u v : List (Fin 3)} {z : Fin 7 → ℤ}
    (h : Eqn g u v z) : Eqn g v u (-z) := by
  dsimp [Eqn] at *
  rw [collect_neg, h]
  simp

theorem eqn_trans {g : Fin 3 → Central} {u v w : List (Fin 3)} {z t : Fin 7 → ℤ}
    (h : Eqn g u v z) (k : Eqn g v w t) : Eqn g u w (t + z) := by
  dsimp [Eqn] at *
  rw [h, k, collect_add]
  simp only [Subgroup.coe_mul, mul_assoc]

theorem eqn_context {g : Fin 3 → Central} {u v : List (Fin 3)} {z : Fin 7 → ℤ}
    (p s : List (Fin 3)) (h : Eqn g u v z) : Eqn g (p ++ u ++ s) (p ++ v ++ s) z := by
  dsimp [Eqn] at *
  simp only [readWord_append, h, mul_assoc]
  rw [← Subgroup.mem_center_iff.mp (collect z).property (readWord g s)]

theorem eqn_overlap {g : Fin 3 → Central} (p m q u v : List (Fin 3))
    {z t : Fin 7 → ℤ} (h : Eqn g (p ++ m) u z) (k : Eqn g (m ++ q) v t) :
    Eqn g (u ++ q) (p ++ v) (t + -z) := by
  have hh : Eqn g (u ++ q) (p ++ (m ++ q)) (-z) := by
    simpa only [List.nil_append, List.append_assoc] using eqn_context [] q (eqn_symm h)
  have hk : Eqn g (p ++ (m ++ q)) (p ++ v) t := by
    simpa only [List.append_nil] using eqn_context p [] k
  exact eqn_trans hh hk


theorem eqn_overlap_checked {g : Fin 3 → Central}
    (p m q u v a b : List (Fin 3)) {z t : Fin 7 → ℤ}
    (ha : a = p ++ m) (hb : b = m ++ q)
    (h : Eqn g a u z) (k : Eqn g b v t) :
    Eqn g (u ++ q) (p ++ v) (t + -z) :=
  eqn_overlap p m q u v (ha ▸ h) (hb ▸ k)


def inverseLetter (i : Fin 3) : Fin 3 := ![0, 2, 1] i
def inverseWord (w : List (Fin 3)) : List (Fin 3) := w.reverse.map inverseLetter

def countA (w : List (Fin 3)) : ℕ := w.count 0

theorem readWord_inverse {G : Type*} [Group G] (g : Fin 3 → G)
    (c : Subgroup.center G)
    (hi : ∀ i, g (inverseLetter i) = (g i)⁻¹ * (c : G) ^ (if i = 0 then 1 else 0 : ℕ))
    (w : List (Fin 3)) :
    readWord g (inverseWord w) = (readWord g w)⁻¹ * (c : G) ^ countA w := by
  induction w with
  | nil => simp [inverseWord, countA]
  | cons a w ih =>
    simp only [inverseWord, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, readWord_append, readWord_cons, readWord_nil, mul_one] at *
    rw [ih, hi]
    have hc : (c : G) ^ countA w * (g a)⁻¹ = (g a)⁻¹ * (c : G) ^ countA w :=
      (Subgroup.mem_center_iff.mp (c ^ countA w).property _).symm
    rw [mul_assoc, ← mul_assoc ((c : G) ^ countA w), hc]
    simp only [mul_assoc, ← pow_add, mul_inv_rev]
    fin_cases a <;> simp [countA, Nat.add_comm]

def rotate (w : List (Fin 3)) (n : ℕ) := w.drop n ++ w.take n

theorem rotate_central {G : Type*} [Group G] (g : Fin 3 → G)
    (w : List (Fin 3)) (n : ℕ) (c : Subgroup.center G) (h : readWord g w = c) :
    readWord g (rotate w n) = c := by
  have hp : readWord g (w.take n) * readWord g (w.drop n) = c := by
    rw [← readWord_append, List.take_append_drop, h]
  have hc := Subgroup.mem_center_iff.mp c.property (readWord g (w.take n))
  apply mul_left_cancel (a := readWord g (w.take n))
  rw [rotate, readWord_append, ← mul_assoc, hp, hc]



theorem seed {G : Type*} [Group G] (g : Fin 3 → G)
    (c : Subgroup.center G)
    (hi : ∀ i, g (inverseLetter i) = (g i)⁻¹ * (c : G) ^ (if i = 0 then 1 else 0 : ℕ))
    (r a b : List (Fin 3)) (rev : Bool) (n : ℕ) (z : Subgroup.center G)
    (hc : a ++ inverseWord b = rotate (if rev then inverseWord r else r) n)
    (hr : readWord g r = z) :
    readWord g a = readWord g b *
      ((if rev then z⁻¹ * c ^ countA r else z) * (c ^ countA b)⁻¹ : Subgroup.center G) := by
  have ho : readWord g (if rev then inverseWord r else r) =
      (if rev then z⁻¹ * c ^ countA r else z : Subgroup.center G) := by
    cases rev <;> simp [readWord_inverse g c hi, hr]
  have h := rotate_central g _ n _ ho
  rw [← hc, readWord_append, readWord_inverse g c hi] at h
  have he : readWord g a * (readWord g b)⁻¹ =
      (((if rev then z⁻¹ * c ^ countA r else z) * (c ^ countA b)⁻¹ : Subgroup.center G) : G) := by
    apply (mul_right_cancel_iff (a := (c : G) ^ countA b)).mp
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow,
      mul_assoc, inv_mul_cancel, mul_one] using h
  rw [mul_inv_eq_iff_eq_mul] at he
  rw [he, Subgroup.mem_center_iff.mp
    ((if rev then z⁻¹ * c ^ countA r else z) * (c ^ countA b)⁻¹).property]



def zeroCoordinate (n : ℤ) : Fin 7 → ℤ := ![n, 0, 0, 0, 0, 0, 0]

@[simp] theorem collect_zeroCoordinate (n : ℤ) :
    collect (zeroCoordinate n) = centralRelator 0 ^ n := by simp [collect, zeroCoordinate]

theorem seed_eqn (g : Fin 3 → Central)
    (hi : ∀ i, g (inverseLetter i) = (g i)⁻¹ * (centralRelator 0 : Central) ^
      (if i = 0 then 1 else 0 : ℕ))
    (r a b : List (Fin 3)) (rev : Bool) (n : ℕ) (z : Fin 7 → ℤ)
    (hc : a ++ inverseWord b = rotate (if rev then inverseWord r else r) n)
    (hr : Eqn g r [] z) :
    Eqn g a b ((if rev then -z + zeroCoordinate (countA r) else z) +
      -zeroCoordinate (countA b)) := by
  simp only [Eqn, readWord_nil, one_mul] at hr
  have hs := seed g (centralRelator 0) hi r a b rev n (collect z) hc hr
  dsimp only [Eqn]
  rw [collect_add, collect_neg, collect_zeroCoordinate]
  convert hs using 2
  cases rev <;> simp [collect_add, collect_neg]



theorem central_mul {G : Type*} [Group G] (x y : G) (c d : Subgroup.center G) :
    (x * c) * (y * d) = (x * y) * (c * d : Subgroup.center G) := by
  simp only [Subgroup.coe_mul, mul_assoc]
  rw [← mul_assoc (c : G), ← Subgroup.mem_center_iff.mp c.property y, mul_assoc]

def commWord (w : List (Fin 3)) : List (Fin 3) :=
  inverseWord [0] ++ inverseWord w ++ [0] ++ w

theorem readWord_commWord {G : Type*} [Group G] (g : Fin 3 → G)
    (c : Subgroup.center G)
    (hi : ∀ i, g (inverseLetter i) = (g i)⁻¹ * (c : G) ^ (if i = 0 then 1 else 0 : ℕ))
    (w : List (Fin 3)) :
    readWord g (commWord w) = sourceCommutator (g 0) (readWord g w) *
      (c : G) ^ (1 + countA w) := by
  simp only [commWord, readWord_append, readWord_inverse g c hi,
    readWord_cons, readWord_nil, mul_one]
  have h0 : countA [0] = 1 := rfl
  rw [h0, pow_one]
  rw [show (c : G) ^ countA w = (c ^ countA w : Subgroup.center G) from rfl,
    central_mul]
  have hc := Subgroup.mem_center_iff.mp (c * c ^ countA w).property
    (g 0 * readWord g w)
  simp only [mul_assoc] at *
  rw [← hc]
  simp only [sourceCommutator, Subgroup.coe_mul, Subgroup.coe_pow,
    pow_add, pow_one, mul_assoc]



theorem readWord_commWord_pow {G : Type*} [Group G] (g : Fin 3 → G)
    (c : Subgroup.center G)
    (hi : ∀ i, g (inverseLetter i) = (g i)⁻¹ * (c : G) ^ (if i = 0 then 1 else 0 : ℕ))
    (w : List (Fin 3)) (n : ℕ) :
    readWord g (commWord w) ^ n = sourceCommutator (g 0) (readWord g w) ^ n *
      (c : G) ^ ((1 + countA w) * n) := by
  rw [readWord_commWord g c hi]
  rw [(show Commute (sourceCommutator (g 0) (readWord g w)) ((c : G) ^ (1 + countA w))
    from Subgroup.mem_center_iff.mp (c ^ (1 + countA w)).property _).mul_pow]
  rw [← pow_mul]


theorem eqn_cycle {g : Fin 3 → Central} {w : List (Fin 3)} {z : Fin 7 → ℤ}
    (h : Eqn g w w z) : collect z = 1 := by
  apply Subtype.ext
  exact mul_eq_left.mp h.symm


end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection.PowerReplay
