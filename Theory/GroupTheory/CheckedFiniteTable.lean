module

public import Theory.GroupTheory.PGroup.InvariantFiberCoordinates
public import Theory.Frattini.BinarySquares
public import Theory.GroupTheory.SubgroupEnumeration
public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Checked finite multiplication tables

An injective table of elements in an existing group transfers its group laws
without an independent associativity search. Generator words identify its image
with the exact generated subgroup. Products of squares certify a binary
Frattini kernel, and element-order and commuting counts evaluate intrinsic fibers.

The final lemma caches an action on the enumerated elements when a semidirect
product uses only the identity and one specified acting element. All tables are
inputs to proofs, never trusted computation or replacement group axioms.

Source: elementary transport of group operations and the square-generation
formula for the Frattini subgroup of a finite two-group.
-/

@[expose] public section

namespace Theory.GroupTheory.CheckedFiniteTable
open Theory.GroupTheory.SubgroupEnumeration Theory.GroupTheory

structure Data (G : Type*) [Group G] (n : ℕ) where
  val : Fin n → G
  mul : Fin n → Fin n → Fin n
  inv : Fin n → Fin n
  unit : Fin n
  injective : Function.Injective val
  val_unit : val unit = 1
  val_mul : ∀ x y, val (mul x y) = val x * val y
  inv_mul : ∀ x, mul (inv x) x = unit

variable {G : Type*} [Group G] {n : ℕ}
def Carrier (_d : Data G n) := Fin n
instance (d : Data G n) : Fintype (Carrier d) := Fin.fintype n
instance (d : Data G n) : DecidableEq (Carrier d) := inferInstanceAs (DecidableEq (Fin n))
instance (d : Data G n) : Mul (Carrier d) := ⟨d.mul⟩
instance (d : Data G n) : One (Carrier d) := ⟨d.unit⟩
instance (d : Data G n) : Inv (Carrier d) := ⟨d.inv⟩
instance (d : Data G n) : Group (Carrier d) :=
  Group.ofLeftAxioms
    (fun x y z => d.injective (by
      change Fin n at x y z
      change d.val (d.mul (d.mul x y) z) = d.val (d.mul x (d.mul y z))
      simp only [d.val_mul, mul_assoc]))
    (fun x => d.injective (by
      change Fin n at x
      change d.val (d.mul d.unit x) = d.val x
      rw [d.val_mul, d.val_unit, one_mul]))
    (fun x => d.inv_mul x)

def embedding (d : Data G n) : Carrier d →* G where
  toFun := d.val
  map_one' := d.val_unit
  map_mul' := d.val_mul

noncomputable def equiv (d : Data G n) {k : ℕ} (gen : Fin k → G)
    (letter : Fin k → Carrier d)
    (hletter : ∀ j, d.val (letter j) = gen j)
    (words : Carrier d → List (Fin k))
    (hwords : ∀ x, evalWord letter (words x) = x) :
    Carrier d ≃* Subgroup.closure (Set.range gen) := by
  have hr : (embedding d).range = Subgroup.closure (Set.range gen) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      have hw : ∀ w : List (Fin k),
          (embedding d) (evalWord letter w) = evalWord gen w := by
        intro w
        induction w with
        | nil => exact map_one (embedding d)
        | cons j w ih =>
          change (embedding d) (letter j * evalWord letter w) = gen j * evalWord gen w
          rw [map_mul, ih]
          exact congrArg (fun z => z * evalWord gen w) (hletter j)
      rw [← hwords x, hw]
      exact evalWord_mem gen _ (fun j => Subgroup.subset_closure (Set.mem_range_self j)) _
    · apply (Subgroup.closure_le _).mpr
      rintro _ ⟨j, rfl⟩
      exact ⟨letter j, hletter j⟩
  exact (MonoidHom.ofInjective d.injective).trans (MulEquiv.subgroupCongr hr)

end Theory.GroupTheory.CheckedFiniteTable

namespace Theory.GroupTheory.CheckedFiniteTable
open Theory.GroupTheory.SubgroupEnumeration Theory.GroupTheory
variable {G V : Type*} [Group G] [Group V] [Finite G]

theorem kernel (hG : IsPGroup 2 G) (π : G →* V)
    (hV : ∀ v : V, v ^ 2 = 1)
    {n : ℕ} (val : Fin n → G) (words : G → List (Fin n))
    (hw : ∀ x, π x = 1 → evalWord (fun i => val i ^ 2) (words x) = x) :
    π.ker = frattini G := by
  rw [hG.frattini_eq_closure_squares]
  apply le_antisymm
  · intro x hx
    rw [← hw x hx]
    exact evalWord_mem _ _ (fun i => Subgroup.subset_closure (Set.mem_range_self (val i))) _
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨x, rfl⟩
    change π (x ^ 2) = 1
    rw [map_pow, hV]

theorem order_eq {W : Type*} [Group W] (x : W) (o : ℕ) (ho : 0 < o)
    (h : x ^ o = 1 ∧ ∀ j : Fin o, 0 < j.val → x ^ j.val ≠ 1) :
    orderOf x = o := by
  apply (orderOf_eq_iff ho).mpr
  exact ⟨h.1, fun j hj hp => h.2 ⟨j, hj⟩ hp⟩

theorem count {W : Type*} [Group W] [Fintype W] [DecidableEq W]
    [DecidableEq V] (π : W →* V) (ord cent : W → ℕ)
    (ho : ∀ x, orderOf x = ord x)
    (hc : ∀ x, MulAut.commutingCard x = cent x)
    (o c : ℕ) (v : V) :
    π.predicateFiberCard (MulAut.orderCentralizerTest (o,c,0)) v =
      (Finset.univ.filter (fun x => π x = v ∧ ord x = o ∧ cent x = c)).card := by
  have hp : MulAut.orderCentralizerTest (G := W) (o,c,0) =
      (fun x => ord x = o ∧ cent x = c) := by
    funext x
    apply propext
    simp only [MulAut.orderCentralizerTest, ho, hc, true_or, and_true]
  rw [hp, MonoidHom.predicateFiberCard_eq_card_filter]

end Theory.GroupTheory.CheckedFiniteTable

namespace Theory.GroupTheory.CheckedFiniteTable
variable {N K : Type*} [Group N] [Group K] [DecidableEq K]
    {φ : K →* MulAut N} {n : ℕ}

theorem mul_of_action (v : Fin n → N ⋊[φ] K) (m : Fin n → Fin n → Fin n)
    (a : K) (act : Fin n → N)
    (ha : ∀ y, φ a (v y).left = act y)
    (hv : ∀ x, (v x).right = 1 ∨ (v x).right = a)
    (hm : ∀ x y, v (m x y) =
      ⟨(v x).left * (if (v x).right = 1 then (v y).left else act y),
       (v x).right * (v y).right⟩) : ∀ x y, v (m x y) = v x * v y := by
  intro x y
  rw [hm]
  apply SemidirectProduct.ext
  · change (v x).left * (if (v x).right = 1 then (v y).left else act y) =
      (v x).left * φ (v x).right (v y).left
    congr 1
    by_cases h : (v x).right = 1
    · rw [if_pos h, h, map_one, MulAut.one_apply]
    · rw [if_neg h, (hv x).resolve_left h, ha]
  · rfl
end Theory.GroupTheory.CheckedFiniteTable
