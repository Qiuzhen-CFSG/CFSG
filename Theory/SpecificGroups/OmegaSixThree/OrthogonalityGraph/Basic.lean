module

public import Theory.LinearAlgebra.QuadraticForm.SixTernaryCoordinates
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Tactic.Ring

/-!
# Projective orthogonality in the six-dimensional ternary space

Vertices are vectors of norm `-1` modulo sign. Over `ZMod 3` this is exactly
projective equivalence. The graph records vanishing of the polar form of the
quadratic form with diagonal `(1,1,1,1,1,-1)`. The quotient construction and
bilinearity calculations make adjacency independent of representatives.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, §F.5,
Lemma F.5.8, printed pp. 303–304.
-/

@[expose] public section

open SixTernaryCoordinates
namespace OmegaSixThree.OrthogonalityGraph

def pairing (v w : Space) : ZMod 3 :=
  v 0*w 0 + v 1*w 1 + v 2*w 2 + v 3*w 3 + v 4*w 4 - v 5*w 5

theorem pairing_symm (v w : Space) : pairing v w = pairing w v := by
  simp [pairing, mul_comm]
theorem pairing_self (v : Space) : pairing v v = quadratic v := by
  simp [pairing, quadratic, pow_two]
theorem quadratic_neg (v : Space) : quadratic (-v) = quadratic v := by
  simp [quadratic]
theorem pairing_neg_left (v w : Space) : pairing (-v) w = -pairing v w := by
  simp only [pairing, Pi.neg_apply]; ring
theorem pairing_neg_right (v w : Space) : pairing v (-w) = -pairing v w := by
  rw [pairing_symm, pairing_neg_left, pairing_symm w v]
theorem polar_eq (v w : Space) :
    quadratic (v+w) - quadratic v - quadratic w = 2 * pairing v w := by
  simp only [quadratic, pairing, Pi.add_apply]; ring

def UnitVector := {v : Space // quadratic v = -1}
def signSetoid : Setoid UnitVector where
  r v w := v.val = w.val ∨ v.val = -w.val
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      intro v w h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h]; simp)
    trans := by
      intro u v w huv hvw
      rcases huv with h | h <;> rcases hvw with k | k
      · exact Or.inl (h.trans k)
      · exact Or.inr (h.trans k)
      · exact Or.inr (by rw [h, k])
      · exact Or.inl (by rw [h, k]; simp) }

def Point := Quotient signSetoid
def point (v : Space) (hv : quadratic v = -1) : Point := Quotient.mk signSetoid ⟨v,hv⟩
theorem point_eq_iff (v w : Space) (hv : quadratic v = -1) (hw : quadratic w = -1) :
    point v hv = point w hw ↔ v = w ∨ v = -w := Quotient.eq

def orthogonal : Point → Point → Prop := Quotient.lift₂
  (fun v w : UnitVector => pairing v.val w.val = 0)
  (by
    intro a b c d hac hbd
    apply propext
    rcases hac with h | h <;> rcases hbd with k | k <;>
      simp [h,k,pairing_neg_left,pairing_neg_right])

def graph : SimpleGraph Point where
  Adj := orthogonal
  symm := ⟨by
    intro x y
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        exact fun h => (pairing_symm _ _).symm.trans h⟩
  loopless := ⟨by
    intro x
    induction x using Quotient.inductionOn with | h x =>
      change pairing x.val x.val ≠ 0
      rw [pairing_self, x.property]
      decide⟩

theorem adj_point_iff (v w : Space) (hv : quadratic v = -1) (hw : quadratic w = -1) :
    graph.Adj (point v hv) (point w hw) ↔ pairing v w = 0 := Iff.rfl

end OmegaSixThree.OrthogonalityGraph

namespace OmegaSixThree.OrthogonalityGraph

theorem pairing_smul_left (c : ZMod 3) (v w : Space) :
    pairing (c • v) w = c * pairing v w := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul]; ring

theorem quadratic_ne_zero_vector (v : Space) (hv : quadratic v = -1) : v ≠ 0 := by
  intro h
  subst v
  norm_num [quadratic] at hv

theorem nonzero_scalar (c : ZMod 3) (hc : c ≠ 0) : c = 1 ∨ c = -1 := by
  revert c
  decide

theorem point_eq_iff_smul (v w : Space) (hv : quadratic v = -1) (hw : quadratic w = -1) :
    point v hv = point w hw ↔ ∃ c : ZMod 3, c ≠ 0 ∧ v = c • w := by
  rw [point_eq_iff]
  constructor
  · rintro (h | h)
    · exact ⟨1, one_ne_zero, by simpa using h⟩
    · exact ⟨-1, neg_ne_zero.mpr one_ne_zero, by simpa using h⟩
  · rintro ⟨c,hc,h⟩
    rcases nonzero_scalar c hc with rfl | rfl
    · exact Or.inl (by simpa using h)
    · exact Or.inr (by simpa using h)

theorem adj_point_polar_iff (v w : Space) (hv : quadratic v = -1) (hw : quadratic w = -1) :
    graph.Adj (point v hv) (point w hw) ↔ quadratic (v+w) - quadratic v - quadratic w = 0 := by
  rw [adj_point_iff, polar_eq]
  have ht : ∀ a : ZMod 3, a = 0 ↔ 2 * a = 0 := by decide
  exact ht _

end OmegaSixThree.OrthogonalityGraph
