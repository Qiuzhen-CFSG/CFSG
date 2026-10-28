module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.ExteriorVanishing.Reduction
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Exactness of the exterior-cube elementary relation system

The ten increasing triples give explicit coordinates for the third exterior
power of the natural SL₅(2) module. We check its elementary action directly
against the determinant minors in `Reduction`, using the three-by-three
determinant formula. In each row a transvection adds at most one coordinate.

For a triple S, take j = min(S) and i = min(Sᶜ), and define the coordinate of
our witness by v(S) = x(i,j)((S \ {j}) ∪ {i}). The proofs below express every
coordinate of (elementaryAction(i,j) - 1)v - x(i,j) as a sum of at most thirteen
coordinates of the diagonal, square, commuting, and Steinberg relations.
These sparse linear combinations are written out explicitly and checked by
ring normalization in characteristic two. The constant minor calculations
use kernel reduction; no enumeration of assignments to x is involved.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma I.1.6(7), printed p.408/PDF p.419, citing Jones--Parshall [JP76].
-/

namespace Representation.SL5TenDimensional
namespace CubeRelations

open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
/-- Lexicographically ordered increasing triples. -/
private def emb (s : Fin 10) : Fin 3 ↪o Fin 5 :=
  OrderEmbedding.ofStrictMono
    (![![0,1,2], ![0,1,3], ![0,1,4], ![0,2,3], ![0,2,4],
       ![0,3,4], ![1,2,3], ![1,2,4], ![1,3,4], ![2,3,4]] s)
    (by revert s; decide)
private def ix (s : Fin 10) : ExteriorIndex 3 := Set.powersetCard.ofFinEmbEquiv (emb s)
private theorem bij : Function.Bijective ix := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · decide +kernel
  · rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    change Nat.card (Fin 10) = Nat.card (Set.powersetCard (Fin 5) 3)
    rw [Set.powersetCard.card]
    simp only [Nat.card_fin]
    decide

private theorem elementary_entry (i j a b : Fin 5) : (elementary i j).val a b =
    (if a = b then 1 else 0) + (if i ≠ j ∧ a = i ∧ b = j then 1 else 0) := by
  by_cases hij : i = j
  · subst j
    simp [elementary, Matrix.one_apply]
  · simp [elementary, hij, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, eq_comm]

/-- Extra source coordinate in each row of a transvection. -/
private def source : Fin 5 → Fin 5 → Fin 10 → Option (Fin 10) := ![
  ![![none, none, none, none, none, none, none, none, none, none],
    ![none, none, none, some 6, some 7, some 8, none, none, none, none],
    ![none, some 6, some 7, none, none, some 9, none, none, none, none],
    ![some 6, none, some 8, none, some 9, none, none, none, none, none],
    ![some 7, some 8, none, some 9, none, none, none, none, none, none]],
  ![![none, none, none, none, none, none, some 3, some 4, some 5, none],
    ![none, none, none, none, none, none, none, none, none, none],
    ![none, some 3, some 4, none, none, none, none, none, some 9, none],
    ![some 3, none, some 5, none, none, none, none, some 9, none, none],
    ![some 4, some 5, none, none, none, none, some 9, none, none, none]],
  ![![none, none, none, none, none, none, some 1, some 2, none, some 5],
    ![none, none, none, some 1, some 2, none, none, none, none, some 8],
    ![none, none, none, none, none, none, none, none, none, none],
    ![some 1, none, none, none, some 5, none, none, some 8, none, none],
    ![some 2, none, none, some 5, none, none, some 8, none, none, none]],
  ![![none, none, none, none, none, none, some 0, none, some 2, some 4],
    ![none, none, none, some 0, none, some 2, none, none, none, some 7],
    ![none, some 0, none, none, none, some 4, none, none, some 7, none],
    ![none, none, none, none, none, none, none, none, none, none],
    ![none, some 2, none, some 4, none, none, some 7, none, none, none]],
  ![![none, none, none, none, none, none, none, some 0, some 1, some 3],
    ![none, none, none, none, some 0, some 1, none, none, none, some 6],
    ![none, none, some 0, none, none, some 3, none, none, some 6, none],
    ![none, none, some 1, none, some 3, none, none, some 6, none, none],
    ![none, none, none, none, none, none, none, none, none, none]]
 ]
private def act (i j : Fin 5) (v : Fin 10 → ZMod 2) (s : Fin 10) : ZMod 2 :=
  v s + (source i j s).elim 0 v

/-- The actual determinant minors agree with the sparse coordinate action. -/
private theorem matrix_entry (i j : Fin 5) (s t : Fin 10) :
    exteriorMatrix 3 (elementary i j) (ix s) (ix t) =
      act i j (fun k => if k = t then 1 else 0) s := by
  simp only [exteriorMatrix, ix, Equiv.symm_apply_apply, Matrix.det_fin_three,
    Matrix.of_apply, elementary_entry]
  revert i j s t
  decide +kernel

private theorem act_sum (i j : Fin 5) (v : Fin 10 → ZMod 2) (s : Fin 10) :
    (∑ t, act i j (fun k => if k = t then 1 else 0) s * v t) = act i j v s := by
  unfold act
  simp only [add_mul, Finset.sum_add_distrib]
  congr 1
  · simp
  · cases h : source i j s with
    | none => simp
    | some t => simp

private theorem action_coords (i j : Fin 5) (v : ExteriorCoordinates 3) (s : Fin 10) :
    elementaryAction 3 i j v (ix s) = act i j (fun t => v (ix t)) s := by
  unfold elementaryAction Matrix.mulVec dotProduct
  rw [← Fintype.sum_bijective ix bij _ _ (fun _ => rfl)]
  simp only [matrix_entry]
  exact act_sum i j _ s

open scoped CharTwo
/-- The ten coordinates selected by the least-element witness rule. -/
private def witness (x : Fin 5 → Fin 5 → ExteriorCoordinates 3) : Fin 10 → ZMod 2 :=
  ![x 3 0 (ix 6), x 2 0 (ix 6), x 2 0 (ix 7), x 1 0 (ix 6), x 1 0 (ix 7), x 1 0 (ix 8), x 0 1 (ix 3), x 0 1 (ix 4), x 0 1 (ix 5), x 0 2 (ix 5)]

/- Each block verifies one generator, coordinate by coordinate. -/
private theorem exact_0_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 3)
    (hx : ElementaryRelations 3 x) (s : Fin 10) :
    act 0 0 (witness x) s - witness x s = x 0 0 (ix s) := by
  fin_cases s
  · change ((x 3 0 (ix 6)) + 0) - (x 3 0 (ix 6)) = x 0 0 (ix 0)
    have h0 := congrFun (hx.diagonal 0) (ix 0)
    change x 0 0 (ix 0) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 6)) + 0) - (x 2 0 (ix 6)) = x 0 0 (ix 1)
    have h0 := congrFun (hx.diagonal 0) (ix 1)
    change x 0 0 (ix 1) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 7)) + 0) - (x 2 0 (ix 7)) = x 0 0 (ix 2)
    have h0 := congrFun (hx.diagonal 0) (ix 2)
    change x 0 0 (ix 2) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 6)) + 0) - (x 1 0 (ix 6)) = x 0 0 (ix 3)
    have h0 := congrFun (hx.diagonal 0) (ix 3)
    change x 0 0 (ix 3) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 7)) + 0) - (x 1 0 (ix 7)) = x 0 0 (ix 4)
    have h0 := congrFun (hx.diagonal 0) (ix 4)
    change x 0 0 (ix 4) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 8)) + 0) - (x 1 0 (ix 8)) = x 0 0 (ix 5)
    have h0 := congrFun (hx.diagonal 0) (ix 5)
    change x 0 0 (ix 5) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 3)) + 0) - (x 0 1 (ix 3)) = x 0 0 (ix 6)
    have h0 := congrFun (hx.diagonal 0) (ix 6)
    change x 0 0 (ix 6) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 4)) + 0) - (x 0 1 (ix 4)) = x 0 0 (ix 7)
    have h0 := congrFun (hx.diagonal 0) (ix 7)
    change x 0 0 (ix 7) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 5)) + 0) - (x 0 1 (ix 5)) = x 0 0 (ix 8)
    have h0 := congrFun (hx.diagonal 0) (ix 8)
    change x 0 0 (ix 8) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 2 (ix 5)) + 0) - (x 0 2 (ix 5)) = x 0 0 (ix 9)
    have h0 := congrFun (hx.diagonal 0) (ix 9)
    change x 0 0 (ix 9) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0

private theorem exact_0_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 3)
    (hx : ElementaryRelations 3 x) (s : Fin 10) :
    act 0 1 (witness x) s - witness x s = x 0 1 (ix s) := by
  fin_cases s
  · change ((x 3 0 (ix 6)) + 0) - (x 3 0 (ix 6)) = x 0 1 (ix 0)
    have h0 := congrFun (hx.commute 0 1 3 2 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 2 (ix 1)) + 0) + x 0 1 (ix 1) = ((x 0 1 (ix 1)) + (x 0 1 (ix 0))) + x 3 2 (ix 1) at h0
    linear_combination (norm := (ring)) h0
  · change ((x 2 0 (ix 6)) + 0) - (x 2 0 (ix 6)) = x 0 1 (ix 1)
    have h0 := congrFun (hx.commute 0 1 2 3 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 3 (ix 0)) + 0) + x 0 1 (ix 0) = ((x 0 1 (ix 0)) + (x 0 1 (ix 1))) + x 2 3 (ix 0) at h0
    linear_combination (norm := (ring)) h0
  · change ((x 2 0 (ix 7)) + 0) - (x 2 0 (ix 7)) = x 0 1 (ix 2)
    have h0 := congrFun (hx.commute 0 1 2 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 4 (ix 0)) + 0) + x 0 1 (ix 0) = ((x 0 1 (ix 0)) + (x 0 1 (ix 2))) + x 2 4 (ix 0) at h0
    linear_combination (norm := (ring)) h0
  · change ((x 1 0 (ix 6)) + (x 0 1 (ix 3))) - (x 1 0 (ix 6)) = x 0 1 (ix 3)
    ring
  · change ((x 1 0 (ix 7)) + (x 0 1 (ix 4))) - (x 1 0 (ix 7)) = x 0 1 (ix 4)
    ring
  · change ((x 1 0 (ix 8)) + (x 0 1 (ix 5))) - (x 1 0 (ix 8)) = x 0 1 (ix 5)
    ring
  · change ((x 0 1 (ix 3)) + 0) - (x 0 1 (ix 3)) = x 0 1 (ix 6)
    have h0 := congrFun (hx.square 0 1) (ix 3)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 3)) + (x 0 1 (ix 6))) + x 0 1 (ix 3) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 4)) + 0) - (x 0 1 (ix 4)) = x 0 1 (ix 7)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 5)) + 0) - (x 0 1 (ix 5)) = x 0 1 (ix 8)
    have h0 := congrFun (hx.square 0 1) (ix 5)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 5)) + (x 0 1 (ix 8))) + x 0 1 (ix 5) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 2 (ix 5)) + 0) - (x 0 2 (ix 5)) = x 0 1 (ix 9)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h1
    change ((((x 0 1 (ix 4)) + 0) + x 1 3 (ix 4)) + (((x 0 1 (ix 7)) + (x 0 1 (ix 9))) + x 1 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 3 (ix 4)) + 0) + x 1 3 (ix 4) at h1
    have h2 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 1 3 (ix 2)) + (x 1 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 5))) + x 1 3 (ix 2) at h2
    have h3 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 1 4 (ix 1)) + (x 1 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 5))) + x 1 4 (ix 1) at h3
    have h4 := congrFun (hx.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 1 4 (ix 0)) + (x 1 4 (ix 6))) + x 0 3 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 4))) + x 1 4 (ix 0) at h4
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4

private theorem exact_0_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 3)
    (hx : ElementaryRelations 3 x) (s : Fin 10) :
    act 0 2 (witness x) s - witness x s = x 0 2 (ix s) := by
  fin_cases s
  · change ((x 3 0 (ix 6)) + 0) - (x 3 0 (ix 6)) = x 0 2 (ix 0)
    have h0 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h0
    change ((((x 0 1 (ix 0)) + 0) + x 1 2 (ix 0)) + 0) + x 0 1 (ix 0) = ((x 0 2 (ix 0)) + 0) + x 1 2 (ix 0) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 6)) + (x 0 1 (ix 3))) - (x 2 0 (ix 6)) = x 0 2 (ix 1)
    have h0 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h0
    change ((((x 0 1 (ix 1)) + (x 0 1 (ix 3))) + x 1 2 (ix 1)) + 0) + x 0 1 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 3))) + x 1 2 (ix 1) at h0
    have h1 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 1 3 (ix 0)) + 0) + x 0 2 (ix 0) = ((x 0 2 (ix 0)) + (x 0 2 (ix 3))) + x 1 3 (ix 0) at h1
    linear_combination (norm := (ring_nf; simp)) h0 + h1
  · change ((x 2 0 (ix 7)) + (x 0 1 (ix 4))) - (x 2 0 (ix 7)) = x 0 2 (ix 2)
    have h0 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h0
    change ((((x 0 1 (ix 2)) + (x 0 1 (ix 4))) + x 1 2 (ix 2)) + 0) + x 0 1 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 4))) + x 1 2 (ix 2) at h0
    have h1 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 1 4 (ix 0)) + 0) + x 0 2 (ix 0) = ((x 0 2 (ix 0)) + (x 0 2 (ix 4))) + x 1 4 (ix 0) at h1
    linear_combination (norm := (ring_nf; simp)) h0 + h1
  · change ((x 1 0 (ix 6)) + 0) - (x 1 0 (ix 6)) = x 0 2 (ix 3)
    have h0 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 1 3 (ix 0)) + 0) + x 0 2 (ix 0) = ((x 0 2 (ix 0)) + (x 0 2 (ix 3))) + x 1 3 (ix 0) at h0
    linear_combination (norm := (ring)) h0
  · change ((x 1 0 (ix 7)) + 0) - (x 1 0 (ix 7)) = x 0 2 (ix 4)
    have h0 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 1 4 (ix 0)) + 0) + x 0 2 (ix 0) = ((x 0 2 (ix 0)) + (x 0 2 (ix 4))) + x 1 4 (ix 0) at h0
    linear_combination (norm := (ring)) h0
  · change ((x 1 0 (ix 8)) + (x 0 2 (ix 5))) - (x 1 0 (ix 8)) = x 0 2 (ix 5)
    ring
  · change ((x 0 1 (ix 3)) + 0) - (x 0 1 (ix 3)) = x 0 2 (ix 6)
    have h0 := congrFun (hx.commute 0 1 0 2 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 0 2 (ix 3)) + (x 0 2 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + 0) + x 0 2 (ix 3) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 4)) + 0) - (x 0 1 (ix 4)) = x 0 2 (ix 7)
    have h0 := congrFun (hx.commute 0 1 0 2 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 0 2 (ix 4)) + (x 0 2 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + 0) + x 0 2 (ix 4) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 5)) + 0) - (x 0 1 (ix 5)) = x 0 2 (ix 8)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.commute 0 1 0 2 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 0 2 (ix 5)) + (x 0 2 (ix 8))) + x 0 1 (ix 5) = ((x 0 1 (ix 5)) + (x 0 1 (ix 9))) + x 0 2 (ix 5) at h1
    have h2 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h2
    change ((((x 0 1 (ix 4)) + 0) + x 1 3 (ix 4)) + (((x 0 1 (ix 7)) + (x 0 1 (ix 9))) + x 1 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 3 (ix 4)) + 0) + x 1 3 (ix 4) at h2
    have h3 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 1 3 (ix 2)) + (x 1 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 5))) + x 1 3 (ix 2) at h3
    have h4 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 1 4 (ix 1)) + (x 1 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 5))) + x 1 4 (ix 1) at h4
    have h5 := congrFun (hx.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h5
    change ((x 1 4 (ix 0)) + (x 1 4 (ix 6))) + x 0 3 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 4))) + x 1 4 (ix 0) at h5
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5
  · change ((x 0 2 (ix 5)) + 0) - (x 0 2 (ix 5)) = x 0 2 (ix 9)
    have h0 := congrFun (hx.commute 0 1 0 2 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 0 2 (ix 5)) + (x 0 2 (ix 8))) + x 0 1 (ix 5) = ((x 0 1 (ix 5)) + (x 0 1 (ix 9))) + x 0 2 (ix 5) at h0
    have h1 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h1
    change ((((x 0 1 (ix 8)) + (x 0 1 (ix 9))) + x 1 2 (ix 8)) + 0) + x 0 1 (ix 8) = ((x 0 2 (ix 8)) + (x 0 2 (ix 9))) + x 1 2 (ix 8) at h1
    linear_combination (norm := (ring_nf; simp)) h0 + h1

private theorem exact_0_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 3)
    (hx : ElementaryRelations 3 x) (s : Fin 10) :
    act 0 3 (witness x) s - witness x s = x 0 3 (ix s) := by
  fin_cases s
  · change ((x 3 0 (ix 6)) + (x 0 1 (ix 3))) - (x 3 0 (ix 6)) = x 0 3 (ix 0)
    have h0 := congrFun (hx.square 0 1) (ix 3)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 3)) + (x 0 1 (ix 6))) + x 0 1 (ix 3) = 0 at h0
    have h1 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h1
    change ((((x 0 1 (ix 0)) + (x 0 1 (ix 3))) + x 1 3 (ix 0)) + 0) + x 0 1 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 3))) + x 1 3 (ix 0) at h1
    have h2 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h2
    change ((((x 0 1 (ix 3)) + 0) + x 1 3 (ix 3)) + (((x 0 1 (ix 6)) + 0) + x 1 3 (ix 6))) + x 0 1 (ix 3) = ((x 0 3 (ix 3)) + 0) + x 1 3 (ix 3) at h2
    have h3 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 1 3 (ix 1)) + (x 1 3 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + 0) + x 1 3 (ix 1) at h3
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3
  · change ((x 2 0 (ix 6)) + 0) - (x 2 0 (ix 6)) = x 0 3 (ix 1)
    have h0 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h0
    change ((((x 0 1 (ix 1)) + 0) + x 1 3 (ix 1)) + 0) + x 0 1 (ix 1) = ((x 0 3 (ix 1)) + 0) + x 1 3 (ix 1) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 7)) + (x 0 1 (ix 5))) - (x 2 0 (ix 7)) = x 0 3 (ix 2)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.commute 0 1 0 2 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 0 2 (ix 4)) + (x 0 2 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + 0) + x 0 2 (ix 4) at h1
    have h2 := congrFun (hx.commute 0 1 0 2 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 0 2 (ix 5)) + (x 0 2 (ix 8))) + x 0 1 (ix 5) = ((x 0 1 (ix 5)) + (x 0 1 (ix 9))) + x 0 2 (ix 5) at h2
    have h3 := congrFun (hx.commute 0 1 2 3 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 2 3 (ix 4)) + (x 2 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + (x 0 1 (ix 5))) + x 2 3 (ix 4) at h3
    have h4 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h4
    change ((((x 0 1 (ix 4)) + 0) + x 1 3 (ix 4)) + (((x 0 1 (ix 7)) + (x 0 1 (ix 9))) + x 1 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 3 (ix 4)) + 0) + x 1 3 (ix 4) at h4
    have h5 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h5
    change ((x 1 3 (ix 2)) + (x 1 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 5))) + x 1 3 (ix 2) at h5
    have h6 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h6
    change ((x 1 4 (ix 1)) + (x 1 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 5))) + x 1 4 (ix 1) at h6
    have h7 := congrFun (hx.steinberg 0 2 3 (by decide) (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h7
    change ((((x 0 2 (ix 2)) + 0) + x 2 3 (ix 2)) + (((x 0 2 (ix 7)) + (x 0 2 (ix 8))) + x 2 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 3 (ix 2)) + 0) + x 2 3 (ix 2) at h7
    have h8 := congrFun (hx.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h8
    change ((x 1 4 (ix 0)) + (x 1 4 (ix 6))) + x 0 3 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 4))) + x 1 4 (ix 0) at h8
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8
  · change ((x 1 0 (ix 6)) + 0) - (x 1 0 (ix 6)) = x 0 3 (ix 3)
    have h0 := congrFun (hx.square 0 1) (ix 3)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 3)) + (x 0 1 (ix 6))) + x 0 1 (ix 3) = 0 at h0
    have h1 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h1
    change ((((x 0 1 (ix 3)) + 0) + x 1 3 (ix 3)) + (((x 0 1 (ix 6)) + 0) + x 1 3 (ix 6))) + x 0 1 (ix 3) = ((x 0 3 (ix 3)) + 0) + x 1 3 (ix 3) at h1
    have h2 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 1 3 (ix 1)) + (x 1 3 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + 0) + x 1 3 (ix 1) at h2
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2
  · change ((x 1 0 (ix 7)) + (x 0 2 (ix 5))) - (x 1 0 (ix 7)) = x 0 3 (ix 4)
    have h0 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 1 4 (ix 1)) + (x 1 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 5))) + x 1 4 (ix 1) at h0
    have h1 := congrFun (hx.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 1 4 (ix 0)) + (x 1 4 (ix 6))) + x 0 3 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 4))) + x 1 4 (ix 0) at h1
    linear_combination (norm := (ring_nf; simp)) h0 + h1
  · change ((x 1 0 (ix 8)) + 0) - (x 1 0 (ix 8)) = x 0 3 (ix 5)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.commute 0 1 0 2 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 0 2 (ix 4)) + (x 0 2 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + 0) + x 0 2 (ix 4) at h1
    have h2 := congrFun (hx.commute 0 1 0 2 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 0 2 (ix 5)) + (x 0 2 (ix 8))) + x 0 1 (ix 5) = ((x 0 1 (ix 5)) + (x 0 1 (ix 9))) + x 0 2 (ix 5) at h2
    have h3 := congrFun (hx.commute 0 1 2 3 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 2 3 (ix 4)) + (x 2 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + (x 0 1 (ix 5))) + x 2 3 (ix 4) at h3
    have h4 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h4
    change ((((x 0 1 (ix 2)) + (x 0 1 (ix 5))) + x 1 3 (ix 2)) + 0) + x 0 1 (ix 2) = ((x 0 3 (ix 2)) + (x 0 3 (ix 5))) + x 1 3 (ix 2) at h4
    have h5 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h5
    change ((((x 0 1 (ix 4)) + 0) + x 1 3 (ix 4)) + (((x 0 1 (ix 7)) + (x 0 1 (ix 9))) + x 1 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 3 (ix 4)) + 0) + x 1 3 (ix 4) at h5
    have h6 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h6
    change ((x 1 3 (ix 2)) + (x 1 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 5))) + x 1 3 (ix 2) at h6
    have h7 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h7
    change ((x 1 4 (ix 1)) + (x 1 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 5))) + x 1 4 (ix 1) at h7
    have h8 := congrFun (hx.steinberg 0 2 3 (by decide) (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h8
    change ((((x 0 2 (ix 2)) + 0) + x 2 3 (ix 2)) + (((x 0 2 (ix 7)) + (x 0 2 (ix 8))) + x 2 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 3 (ix 2)) + 0) + x 2 3 (ix 2) at h8
    have h9 := congrFun (hx.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h9
    change ((x 1 4 (ix 0)) + (x 1 4 (ix 6))) + x 0 3 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 4))) + x 1 4 (ix 0) at h9
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8 + h9
  · change ((x 0 1 (ix 3)) + 0) - (x 0 1 (ix 3)) = x 0 3 (ix 6)
    have h0 := congrFun (hx.commute 0 1 0 3 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 0 3 (ix 3)) + (x 0 3 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + 0) + x 0 3 (ix 3) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 4)) + 0) - (x 0 1 (ix 4)) = x 0 3 (ix 7)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.commute 0 1 0 3 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 0 3 (ix 4)) + (x 0 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + (x 0 1 (ix 9))) + x 0 3 (ix 4) at h1
    have h2 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h2
    change ((((x 0 1 (ix 4)) + 0) + x 1 3 (ix 4)) + (((x 0 1 (ix 7)) + (x 0 1 (ix 9))) + x 1 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 3 (ix 4)) + 0) + x 1 3 (ix 4) at h2
    have h3 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 1 3 (ix 2)) + (x 1 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 5))) + x 1 3 (ix 2) at h3
    have h4 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 1 4 (ix 1)) + (x 1 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 5))) + x 1 4 (ix 1) at h4
    have h5 := congrFun (hx.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h5
    change ((x 1 4 (ix 0)) + (x 1 4 (ix 6))) + x 0 3 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 4))) + x 1 4 (ix 0) at h5
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5
  · change ((x 0 1 (ix 5)) + 0) - (x 0 1 (ix 5)) = x 0 3 (ix 8)
    have h0 := congrFun (hx.commute 0 1 0 3 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 0 3 (ix 5)) + (x 0 3 (ix 8))) + x 0 1 (ix 5) = ((x 0 1 (ix 5)) + 0) + x 0 3 (ix 5) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 2 (ix 5)) + 0) - (x 0 2 (ix 5)) = x 0 3 (ix 9)
    have h0 := congrFun (hx.commute 0 1 0 3 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 0 3 (ix 4)) + (x 0 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + (x 0 1 (ix 9))) + x 0 3 (ix 4) at h0
    have h1 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h1
    change ((((x 0 1 (ix 7)) + (x 0 1 (ix 9))) + x 1 3 (ix 7)) + 0) + x 0 1 (ix 7) = ((x 0 3 (ix 7)) + (x 0 3 (ix 9))) + x 1 3 (ix 7) at h1
    linear_combination (norm := (ring_nf; simp)) h0 + h1

private theorem exact_0_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 3)
    (hx : ElementaryRelations 3 x) (s : Fin 10) :
    act 0 4 (witness x) s - witness x s = x 0 4 (ix s) := by
  fin_cases s
  · change ((x 3 0 (ix 6)) + (x 0 1 (ix 4))) - (x 3 0 (ix 6)) = x 0 4 (ix 0)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.steinberg 0 1 4 (by decide) (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h1
    change ((((x 0 1 (ix 0)) + (x 0 1 (ix 4))) + x 1 4 (ix 0)) + 0) + x 0 1 (ix 0) = ((x 0 4 (ix 0)) + (x 0 4 (ix 4))) + x 1 4 (ix 0) at h1
    have h2 := congrFun (hx.steinberg 0 1 4 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h2
    change ((((x 0 1 (ix 4)) + 0) + x 1 4 (ix 4)) + (((x 0 1 (ix 7)) + 0) + x 1 4 (ix 7))) + x 0 1 (ix 4) = ((x 0 4 (ix 4)) + 0) + x 1 4 (ix 4) at h2
    have h3 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 1 4 (ix 2)) + (x 1 4 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + 0) + x 1 4 (ix 2) at h3
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3
  · change ((x 2 0 (ix 6)) + (x 0 1 (ix 5))) - (x 2 0 (ix 6)) = x 0 4 (ix 1)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.commute 0 1 0 2 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 0 2 (ix 3)) + (x 0 2 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + 0) + x 0 2 (ix 3) at h1
    have h2 := congrFun (hx.commute 0 1 0 2 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 0 2 (ix 5)) + (x 0 2 (ix 8))) + x 0 1 (ix 5) = ((x 0 1 (ix 5)) + (x 0 1 (ix 9))) + x 0 2 (ix 5) at h2
    have h3 := congrFun (hx.commute 0 1 2 4 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 2 4 (ix 3)) + (x 2 4 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + (x 0 1 (ix 5))) + x 2 4 (ix 3) at h3
    have h4 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h4
    change ((((x 0 1 (ix 4)) + 0) + x 1 3 (ix 4)) + (((x 0 1 (ix 7)) + (x 0 1 (ix 9))) + x 1 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 3 (ix 4)) + 0) + x 1 3 (ix 4) at h4
    have h5 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h5
    change ((x 1 3 (ix 2)) + (x 1 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 5))) + x 1 3 (ix 2) at h5
    have h6 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h6
    change ((x 1 4 (ix 1)) + (x 1 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 5))) + x 1 4 (ix 1) at h6
    have h7 := congrFun (hx.steinberg 0 2 4 (by decide) (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h7
    change ((((x 0 2 (ix 1)) + 0) + x 2 4 (ix 1)) + (((x 0 2 (ix 6)) + (x 0 2 (ix 8))) + x 2 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 4 (ix 1)) + 0) + x 2 4 (ix 1) at h7
    have h8 := congrFun (hx.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h8
    change ((x 1 4 (ix 0)) + (x 1 4 (ix 6))) + x 0 3 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 4))) + x 1 4 (ix 0) at h8
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8
  · change ((x 2 0 (ix 7)) + 0) - (x 2 0 (ix 7)) = x 0 4 (ix 2)
    have h0 := congrFun (hx.steinberg 0 1 4 (by decide) (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h0
    change ((((x 0 1 (ix 2)) + 0) + x 1 4 (ix 2)) + 0) + x 0 1 (ix 2) = ((x 0 4 (ix 2)) + 0) + x 1 4 (ix 2) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 6)) + (x 0 2 (ix 5))) - (x 1 0 (ix 6)) = x 0 4 (ix 3)
    have h0 := congrFun (hx.square 0 1) (ix 3)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 3)) + (x 0 1 (ix 6))) + x 0 1 (ix 3) = 0 at h0
    have h1 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h1
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h1
    have h2 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h2
    change ((((x 0 1 (ix 4)) + 0) + x 1 3 (ix 4)) + (((x 0 1 (ix 7)) + (x 0 1 (ix 9))) + x 1 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 3 (ix 4)) + 0) + x 1 3 (ix 4) at h2
    have h3 := congrFun (hx.steinberg 0 1 4 (by decide) (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h3
    change ((((x 0 1 (ix 3)) + 0) + x 1 4 (ix 3)) + (((x 0 1 (ix 6)) + (x 0 1 (ix 9))) + x 1 4 (ix 6))) + x 0 1 (ix 3) = ((x 0 4 (ix 3)) + 0) + x 1 4 (ix 3) at h3
    have h4 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 1 3 (ix 2)) + (x 1 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 5))) + x 1 3 (ix 2) at h4
    have h5 := congrFun (hx.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h5
    change ((x 1 4 (ix 0)) + (x 1 4 (ix 6))) + x 0 3 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 4))) + x 1 4 (ix 0) at h5
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5
  · change ((x 1 0 (ix 7)) + 0) - (x 1 0 (ix 7)) = x 0 4 (ix 4)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.steinberg 0 1 4 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h1
    change ((((x 0 1 (ix 4)) + 0) + x 1 4 (ix 4)) + (((x 0 1 (ix 7)) + 0) + x 1 4 (ix 7))) + x 0 1 (ix 4) = ((x 0 4 (ix 4)) + 0) + x 1 4 (ix 4) at h1
    have h2 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 1 4 (ix 2)) + (x 1 4 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + 0) + x 1 4 (ix 2) at h2
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2
  · change ((x 1 0 (ix 8)) + 0) - (x 1 0 (ix 8)) = x 0 4 (ix 5)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.commute 0 1 0 2 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 0 2 (ix 3)) + (x 0 2 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + 0) + x 0 2 (ix 3) at h1
    have h2 := congrFun (hx.commute 0 1 0 2 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 0 2 (ix 5)) + (x 0 2 (ix 8))) + x 0 1 (ix 5) = ((x 0 1 (ix 5)) + (x 0 1 (ix 9))) + x 0 2 (ix 5) at h2
    have h3 := congrFun (hx.commute 0 1 2 4 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 2 4 (ix 3)) + (x 2 4 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + (x 0 1 (ix 5))) + x 2 4 (ix 3) at h3
    have h4 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h4
    change ((((x 0 1 (ix 4)) + 0) + x 1 3 (ix 4)) + (((x 0 1 (ix 7)) + (x 0 1 (ix 9))) + x 1 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 3 (ix 4)) + 0) + x 1 3 (ix 4) at h4
    have h5 := congrFun (hx.steinberg 0 1 4 (by decide) (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h5
    change ((((x 0 1 (ix 1)) + (x 0 1 (ix 5))) + x 1 4 (ix 1)) + 0) + x 0 1 (ix 1) = ((x 0 4 (ix 1)) + (x 0 4 (ix 5))) + x 1 4 (ix 1) at h5
    have h6 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h6
    change ((x 1 3 (ix 2)) + (x 1 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 5))) + x 1 3 (ix 2) at h6
    have h7 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h7
    change ((x 1 4 (ix 1)) + (x 1 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 5))) + x 1 4 (ix 1) at h7
    have h8 := congrFun (hx.steinberg 0 2 4 (by decide) (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h8
    change ((((x 0 2 (ix 1)) + 0) + x 2 4 (ix 1)) + (((x 0 2 (ix 6)) + (x 0 2 (ix 8))) + x 2 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 4 (ix 1)) + 0) + x 2 4 (ix 1) at h8
    have h9 := congrFun (hx.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h9
    change ((x 1 4 (ix 0)) + (x 1 4 (ix 6))) + x 0 3 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 4))) + x 1 4 (ix 0) at h9
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8 + h9
  · change ((x 0 1 (ix 3)) + 0) - (x 0 1 (ix 3)) = x 0 4 (ix 6)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.commute 0 1 0 4 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 0 4 (ix 3)) + (x 0 4 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + (x 0 1 (ix 9))) + x 0 4 (ix 3) at h1
    have h2 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h2
    change ((((x 0 1 (ix 4)) + 0) + x 1 3 (ix 4)) + (((x 0 1 (ix 7)) + (x 0 1 (ix 9))) + x 1 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 3 (ix 4)) + 0) + x 1 3 (ix 4) at h2
    have h3 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 1 3 (ix 2)) + (x 1 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 5))) + x 1 3 (ix 2) at h3
    have h4 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 1 4 (ix 1)) + (x 1 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 5))) + x 1 4 (ix 1) at h4
    have h5 := congrFun (hx.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h5
    change ((x 1 4 (ix 0)) + (x 1 4 (ix 6))) + x 0 3 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 4))) + x 1 4 (ix 0) at h5
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5
  · change ((x 0 1 (ix 4)) + 0) - (x 0 1 (ix 4)) = x 0 4 (ix 7)
    have h0 := congrFun (hx.commute 0 1 0 4 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 0 4 (ix 4)) + (x 0 4 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + 0) + x 0 4 (ix 4) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 5)) + 0) - (x 0 1 (ix 5)) = x 0 4 (ix 8)
    have h0 := congrFun (hx.commute 0 1 0 4 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 0 4 (ix 5)) + (x 0 4 (ix 8))) + x 0 1 (ix 5) = ((x 0 1 (ix 5)) + 0) + x 0 4 (ix 5) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 2 (ix 5)) + 0) - (x 0 2 (ix 5)) = x 0 4 (ix 9)
    have h0 := congrFun (hx.commute 0 1 0 4 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 0 4 (ix 3)) + (x 0 4 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + (x 0 1 (ix 9))) + x 0 4 (ix 3) at h0
    have h1 := congrFun (hx.steinberg 0 1 4 (by decide) (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h1
    change ((((x 0 1 (ix 6)) + (x 0 1 (ix 9))) + x 1 4 (ix 6)) + 0) + x 0 1 (ix 6) = ((x 0 4 (ix 6)) + (x 0 4 (ix 9))) + x 1 4 (ix 6) at h1
    linear_combination (norm := (ring_nf; simp)) h0 + h1

private theorem exact_1_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 3)
    (hx : ElementaryRelations 3 x) (s : Fin 10) :
    act 1 0 (witness x) s - witness x s = x 1 0 (ix s) := by
  fin_cases s
  · change ((x 3 0 (ix 6)) + 0) - (x 3 0 (ix 6)) = x 1 0 (ix 0)
    have h0 := congrFun (hx.commute 1 0 3 2 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 2 (ix 1)) + 0) + x 1 0 (ix 1) = ((x 1 0 (ix 1)) + (x 1 0 (ix 0))) + x 3 2 (ix 1) at h0
    linear_combination (norm := (ring)) h0
  · change ((x 2 0 (ix 6)) + 0) - (x 2 0 (ix 6)) = x 1 0 (ix 1)
    have h0 := congrFun (hx.commute 1 0 2 3 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 3 (ix 0)) + 0) + x 1 0 (ix 0) = ((x 1 0 (ix 0)) + (x 1 0 (ix 1))) + x 2 3 (ix 0) at h0
    linear_combination (norm := (ring)) h0
  · change ((x 2 0 (ix 7)) + 0) - (x 2 0 (ix 7)) = x 1 0 (ix 2)
    have h0 := congrFun (hx.commute 1 0 2 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 4 (ix 0)) + 0) + x 1 0 (ix 0) = ((x 1 0 (ix 0)) + (x 1 0 (ix 2))) + x 2 4 (ix 0) at h0
    linear_combination (norm := (ring)) h0
  · change ((x 1 0 (ix 6)) + 0) - (x 1 0 (ix 6)) = x 1 0 (ix 3)
    have h0 := congrFun (hx.square 1 0) (ix 6)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 1 0 (ix 6)) + (x 1 0 (ix 3))) + x 1 0 (ix 6) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 7)) + 0) - (x 1 0 (ix 7)) = x 1 0 (ix 4)
    have h0 := congrFun (hx.square 1 0) (ix 7)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 1 0 (ix 7)) + (x 1 0 (ix 4))) + x 1 0 (ix 7) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 8)) + 0) - (x 1 0 (ix 8)) = x 1 0 (ix 5)
    have h0 := congrFun (hx.square 1 0) (ix 8)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 1 0 (ix 8)) + (x 1 0 (ix 5))) + x 1 0 (ix 8) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 3)) + (x 1 0 (ix 6))) - (x 0 1 (ix 3)) = x 1 0 (ix 6)
    ring
  · change ((x 0 1 (ix 4)) + (x 1 0 (ix 7))) - (x 0 1 (ix 4)) = x 1 0 (ix 7)
    ring
  · change ((x 0 1 (ix 5)) + (x 1 0 (ix 8))) - (x 0 1 (ix 5)) = x 1 0 (ix 8)
    ring
  · change ((x 0 2 (ix 5)) + 0) - (x 0 2 (ix 5)) = x 1 0 (ix 9)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.square 0 1) (ix 5)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h1
    change ((x 0 1 (ix 5)) + (x 0 1 (ix 8))) + x 0 1 (ix 5) = 0 at h1
    have h2 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h2
    change ((((x 0 1 (ix 5)) + 0) + x 1 2 (ix 5)) + (((x 0 1 (ix 8)) + (x 0 1 (ix 9))) + x 1 2 (ix 8))) + x 0 1 (ix 5) = ((x 0 2 (ix 5)) + 0) + x 1 2 (ix 5) at h2
    have h3 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h3
    change ((((x 0 1 (ix 4)) + 0) + x 1 3 (ix 4)) + (((x 0 1 (ix 7)) + (x 0 1 (ix 9))) + x 1 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 3 (ix 4)) + 0) + x 1 3 (ix 4) at h3
    have h4 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 1 3 (ix 2)) + (x 1 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 5))) + x 1 3 (ix 2) at h4
    have h5 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h5
    change ((x 1 4 (ix 1)) + (x 1 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 5))) + x 1 4 (ix 1) at h5
    have h6 := congrFun (hx.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h6
    change ((x 1 4 (ix 0)) + (x 1 4 (ix 6))) + x 0 3 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 4))) + x 1 4 (ix 0) at h6
    have h7 := congrFun (hx.square 1 0) (ix 8)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h7
    change ((x 1 0 (ix 8)) + (x 1 0 (ix 5))) + x 1 0 (ix 8) = 0 at h7
    have h8 := congrFun (hx.steinberg 1 0 2 (by decide) (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h8
    change ((((x 1 0 (ix 8)) + 0) + x 0 2 (ix 8)) + (((x 1 0 (ix 5)) + (x 1 0 (ix 9))) + x 0 2 (ix 5))) + x 1 0 (ix 8) = ((x 1 2 (ix 8)) + 0) + x 0 2 (ix 8) at h8
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8

private theorem exact_1_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 3)
    (hx : ElementaryRelations 3 x) (s : Fin 10) :
    act 1 1 (witness x) s - witness x s = x 1 1 (ix s) := by
  fin_cases s
  · change ((x 3 0 (ix 6)) + 0) - (x 3 0 (ix 6)) = x 1 1 (ix 0)
    have h0 := congrFun (hx.diagonal 1) (ix 0)
    change x 1 1 (ix 0) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 6)) + 0) - (x 2 0 (ix 6)) = x 1 1 (ix 1)
    have h0 := congrFun (hx.diagonal 1) (ix 1)
    change x 1 1 (ix 1) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 7)) + 0) - (x 2 0 (ix 7)) = x 1 1 (ix 2)
    have h0 := congrFun (hx.diagonal 1) (ix 2)
    change x 1 1 (ix 2) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 6)) + 0) - (x 1 0 (ix 6)) = x 1 1 (ix 3)
    have h0 := congrFun (hx.diagonal 1) (ix 3)
    change x 1 1 (ix 3) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 7)) + 0) - (x 1 0 (ix 7)) = x 1 1 (ix 4)
    have h0 := congrFun (hx.diagonal 1) (ix 4)
    change x 1 1 (ix 4) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 8)) + 0) - (x 1 0 (ix 8)) = x 1 1 (ix 5)
    have h0 := congrFun (hx.diagonal 1) (ix 5)
    change x 1 1 (ix 5) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 3)) + 0) - (x 0 1 (ix 3)) = x 1 1 (ix 6)
    have h0 := congrFun (hx.commute 0 2 1 1 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 1 1 (ix 1)) + (x 1 1 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + 0) + x 1 1 (ix 1) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 4)) + 0) - (x 0 1 (ix 4)) = x 1 1 (ix 7)
    have h0 := congrFun (hx.commute 0 2 1 1 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 1 1 (ix 2)) + (x 1 1 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + 0) + x 1 1 (ix 2) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 5)) + 0) - (x 0 1 (ix 5)) = x 1 1 (ix 8)
    have h0 := congrFun (hx.commute 0 3 1 1 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 1 1 (ix 2)) + (x 1 1 (ix 8))) + x 0 3 (ix 2) = ((x 0 3 (ix 2)) + 0) + x 1 1 (ix 2) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 2 (ix 5)) + 0) - (x 0 2 (ix 5)) = x 1 1 (ix 9)
    have h0 := congrFun (hx.commute 0 2 1 1 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 1 1 (ix 5)) + (x 1 1 (ix 9))) + x 0 2 (ix 5) = ((x 0 2 (ix 5)) + 0) + x 1 1 (ix 5) at h0
    linear_combination (norm := (ring_nf; simp)) h0

private theorem exact_1_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 3)
    (hx : ElementaryRelations 3 x) (s : Fin 10) :
    act 1 2 (witness x) s - witness x s = x 1 2 (ix s) := by
  fin_cases s
  · change ((x 3 0 (ix 6)) + 0) - (x 3 0 (ix 6)) = x 1 2 (ix 0)
    have h0 := congrFun (hx.steinberg 1 0 2 (by decide) (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h0
    change ((((x 1 0 (ix 0)) + 0) + x 0 2 (ix 0)) + 0) + x 1 0 (ix 0) = ((x 1 2 (ix 0)) + 0) + x 0 2 (ix 0) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 6)) + (x 1 0 (ix 6))) - (x 2 0 (ix 6)) = x 1 2 (ix 1)
    have h0 := congrFun (hx.square 0 1) (ix 3)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 3)) + (x 0 1 (ix 6))) + x 0 1 (ix 3) = 0 at h0
    have h1 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h1
    change ((((x 0 1 (ix 3)) + 0) + x 1 2 (ix 3)) + (((x 0 1 (ix 6)) + 0) + x 1 2 (ix 6))) + x 0 1 (ix 3) = ((x 0 2 (ix 3)) + 0) + x 1 2 (ix 3) at h1
    have h2 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 1 3 (ix 0)) + 0) + x 0 2 (ix 0) = ((x 0 2 (ix 0)) + (x 0 2 (ix 3))) + x 1 3 (ix 0) at h2
    have h3 := congrFun (hx.steinberg 1 0 2 (by decide) (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h3
    change ((((x 1 0 (ix 1)) + (x 1 0 (ix 6))) + x 0 2 (ix 1)) + 0) + x 1 0 (ix 1) = ((x 1 2 (ix 1)) + (x 1 2 (ix 6))) + x 0 2 (ix 1) at h3
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3
  · change ((x 2 0 (ix 7)) + (x 1 0 (ix 7))) - (x 2 0 (ix 7)) = x 1 2 (ix 2)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h1
    change ((((x 0 1 (ix 4)) + 0) + x 1 2 (ix 4)) + (((x 0 1 (ix 7)) + 0) + x 1 2 (ix 7))) + x 0 1 (ix 4) = ((x 0 2 (ix 4)) + 0) + x 1 2 (ix 4) at h1
    have h2 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 1 4 (ix 0)) + 0) + x 0 2 (ix 0) = ((x 0 2 (ix 0)) + (x 0 2 (ix 4))) + x 1 4 (ix 0) at h2
    have h3 := congrFun (hx.steinberg 1 0 2 (by decide) (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h3
    change ((((x 1 0 (ix 2)) + (x 1 0 (ix 7))) + x 0 2 (ix 2)) + 0) + x 1 0 (ix 2) = ((x 1 2 (ix 2)) + (x 1 2 (ix 7))) + x 0 2 (ix 2) at h3
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3
  · change ((x 1 0 (ix 6)) + 0) - (x 1 0 (ix 6)) = x 1 2 (ix 3)
    have h0 := congrFun (hx.commute 1 0 1 2 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 1 2 (ix 6)) + (x 1 2 (ix 3))) + x 1 0 (ix 6) = ((x 1 0 (ix 6)) + 0) + x 1 2 (ix 6) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 7)) + 0) - (x 1 0 (ix 7)) = x 1 2 (ix 4)
    have h0 := congrFun (hx.commute 1 0 1 2 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 1 2 (ix 7)) + (x 1 2 (ix 4))) + x 1 0 (ix 7) = ((x 1 0 (ix 7)) + 0) + x 1 2 (ix 7) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 8)) + 0) - (x 1 0 (ix 8)) = x 1 2 (ix 5)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.square 0 1) (ix 5)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h1
    change ((x 0 1 (ix 5)) + (x 0 1 (ix 8))) + x 0 1 (ix 5) = 0 at h1
    have h2 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h2
    change ((((x 0 1 (ix 5)) + 0) + x 1 2 (ix 5)) + (((x 0 1 (ix 8)) + (x 0 1 (ix 9))) + x 1 2 (ix 8))) + x 0 1 (ix 5) = ((x 0 2 (ix 5)) + 0) + x 1 2 (ix 5) at h2
    have h3 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h3
    change ((((x 0 1 (ix 4)) + 0) + x 1 3 (ix 4)) + (((x 0 1 (ix 7)) + (x 0 1 (ix 9))) + x 1 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 3 (ix 4)) + 0) + x 1 3 (ix 4) at h3
    have h4 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 1 3 (ix 2)) + (x 1 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 5))) + x 1 3 (ix 2) at h4
    have h5 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h5
    change ((x 1 4 (ix 1)) + (x 1 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 5))) + x 1 4 (ix 1) at h5
    have h6 := congrFun (hx.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h6
    change ((x 1 4 (ix 0)) + (x 1 4 (ix 6))) + x 0 3 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 4))) + x 1 4 (ix 0) at h6
    have h7 := congrFun (hx.square 1 0) (ix 8)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h7
    change ((x 1 0 (ix 8)) + (x 1 0 (ix 5))) + x 1 0 (ix 8) = 0 at h7
    have h8 := congrFun (hx.commute 1 0 1 2 (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h8
    change ((x 1 2 (ix 8)) + (x 1 2 (ix 5))) + x 1 0 (ix 8) = ((x 1 0 (ix 8)) + (x 1 0 (ix 9))) + x 1 2 (ix 8) at h8
    have h9 := congrFun (hx.steinberg 1 0 2 (by decide) (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h9
    change ((((x 1 0 (ix 8)) + 0) + x 0 2 (ix 8)) + (((x 1 0 (ix 5)) + (x 1 0 (ix 9))) + x 0 2 (ix 5))) + x 1 0 (ix 8) = ((x 1 2 (ix 8)) + 0) + x 0 2 (ix 8) at h9
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8 + h9
  · change ((x 0 1 (ix 3)) + 0) - (x 0 1 (ix 3)) = x 1 2 (ix 6)
    have h0 := congrFun (hx.square 0 1) (ix 3)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 3)) + (x 0 1 (ix 6))) + x 0 1 (ix 3) = 0 at h0
    have h1 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h1
    change ((((x 0 1 (ix 3)) + 0) + x 1 2 (ix 3)) + (((x 0 1 (ix 6)) + 0) + x 1 2 (ix 6))) + x 0 1 (ix 3) = ((x 0 2 (ix 3)) + 0) + x 1 2 (ix 3) at h1
    have h2 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 1 3 (ix 0)) + 0) + x 0 2 (ix 0) = ((x 0 2 (ix 0)) + (x 0 2 (ix 3))) + x 1 3 (ix 0) at h2
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2
  · change ((x 0 1 (ix 4)) + 0) - (x 0 1 (ix 4)) = x 1 2 (ix 7)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h1
    change ((((x 0 1 (ix 4)) + 0) + x 1 2 (ix 4)) + (((x 0 1 (ix 7)) + 0) + x 1 2 (ix 7))) + x 0 1 (ix 4) = ((x 0 2 (ix 4)) + 0) + x 1 2 (ix 4) at h1
    have h2 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 1 4 (ix 0)) + 0) + x 0 2 (ix 0) = ((x 0 2 (ix 0)) + (x 0 2 (ix 4))) + x 1 4 (ix 0) at h2
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2
  · change ((x 0 1 (ix 5)) + (x 0 2 (ix 5))) - (x 0 1 (ix 5)) = x 1 2 (ix 8)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.square 0 1) (ix 5)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h1
    change ((x 0 1 (ix 5)) + (x 0 1 (ix 8))) + x 0 1 (ix 5) = 0 at h1
    have h2 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h2
    change ((((x 0 1 (ix 5)) + 0) + x 1 2 (ix 5)) + (((x 0 1 (ix 8)) + (x 0 1 (ix 9))) + x 1 2 (ix 8))) + x 0 1 (ix 5) = ((x 0 2 (ix 5)) + 0) + x 1 2 (ix 5) at h2
    have h3 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h3
    change ((((x 0 1 (ix 4)) + 0) + x 1 3 (ix 4)) + (((x 0 1 (ix 7)) + (x 0 1 (ix 9))) + x 1 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 3 (ix 4)) + 0) + x 1 3 (ix 4) at h3
    have h4 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 1 3 (ix 2)) + (x 1 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 5))) + x 1 3 (ix 2) at h4
    have h5 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h5
    change ((x 1 4 (ix 1)) + (x 1 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 5))) + x 1 4 (ix 1) at h5
    have h6 := congrFun (hx.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h6
    change ((x 1 4 (ix 0)) + (x 1 4 (ix 6))) + x 0 3 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 4))) + x 1 4 (ix 0) at h6
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5 + h6
  · change ((x 0 2 (ix 5)) + 0) - (x 0 2 (ix 5)) = x 1 2 (ix 9)
    have h0 := congrFun (hx.commute 0 2 1 2 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 1 2 (ix 5)) + (x 1 2 (ix 9))) + x 0 2 (ix 5) = ((x 0 2 (ix 5)) + 0) + x 1 2 (ix 5) at h0
    linear_combination (norm := (ring_nf; simp)) h0

private theorem exact_1_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 3)
    (hx : ElementaryRelations 3 x) (s : Fin 10) :
    act 1 3 (witness x) s - witness x s = x 1 3 (ix s) := by
  fin_cases s
  · change ((x 3 0 (ix 6)) + (x 1 0 (ix 6))) - (x 3 0 (ix 6)) = x 1 3 (ix 0)
    have h0 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 1 3 (ix 1)) + (x 1 3 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + 0) + x 1 3 (ix 1) at h0
    have h1 := congrFun (hx.steinberg 1 0 3 (by decide) (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h1
    change ((((x 1 0 (ix 0)) + (x 1 0 (ix 6))) + x 0 3 (ix 0)) + 0) + x 1 0 (ix 0) = ((x 1 3 (ix 0)) + (x 1 3 (ix 6))) + x 0 3 (ix 0) at h1
    linear_combination (norm := (ring_nf; simp)) h0 + h1
  · change ((x 2 0 (ix 6)) + 0) - (x 2 0 (ix 6)) = x 1 3 (ix 1)
    have h0 := congrFun (hx.steinberg 1 0 3 (by decide) (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h0
    change ((((x 1 0 (ix 1)) + 0) + x 0 3 (ix 1)) + 0) + x 1 0 (ix 1) = ((x 1 3 (ix 1)) + 0) + x 0 3 (ix 1) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 7)) + (x 1 0 (ix 8))) - (x 2 0 (ix 7)) = x 1 3 (ix 2)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.square 0 1) (ix 5)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h1
    change ((x 0 1 (ix 5)) + (x 0 1 (ix 8))) + x 0 1 (ix 5) = 0 at h1
    have h2 := congrFun (hx.commute 0 1 0 2 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 0 2 (ix 4)) + (x 0 2 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + 0) + x 0 2 (ix 4) at h2
    have h3 := congrFun (hx.commute 0 1 0 2 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 0 2 (ix 5)) + (x 0 2 (ix 8))) + x 0 1 (ix 5) = ((x 0 1 (ix 5)) + (x 0 1 (ix 9))) + x 0 2 (ix 5) at h3
    have h4 := congrFun (hx.commute 0 1 2 3 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 2 3 (ix 4)) + (x 2 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + (x 0 1 (ix 5))) + x 2 3 (ix 4) at h4
    have h5 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h5
    change ((((x 0 1 (ix 2)) + (x 0 1 (ix 5))) + x 1 3 (ix 2)) + 0) + x 0 1 (ix 2) = ((x 0 3 (ix 2)) + (x 0 3 (ix 5))) + x 1 3 (ix 2) at h5
    have h6 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h6
    change ((((x 0 1 (ix 4)) + 0) + x 1 3 (ix 4)) + (((x 0 1 (ix 7)) + (x 0 1 (ix 9))) + x 1 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 3 (ix 4)) + 0) + x 1 3 (ix 4) at h6
    have h7 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h7
    change ((((x 0 1 (ix 5)) + 0) + x 1 3 (ix 5)) + (((x 0 1 (ix 8)) + 0) + x 1 3 (ix 8))) + x 0 1 (ix 5) = ((x 0 3 (ix 5)) + 0) + x 1 3 (ix 5) at h7
    have h8 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h8
    change ((x 1 3 (ix 2)) + (x 1 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 5))) + x 1 3 (ix 2) at h8
    have h9 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h9
    change ((x 1 4 (ix 1)) + (x 1 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 5))) + x 1 4 (ix 1) at h9
    have h10 := congrFun (hx.steinberg 0 2 3 (by decide) (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h10
    change ((((x 0 2 (ix 2)) + 0) + x 2 3 (ix 2)) + (((x 0 2 (ix 7)) + (x 0 2 (ix 8))) + x 2 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 3 (ix 2)) + 0) + x 2 3 (ix 2) at h10
    have h11 := congrFun (hx.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h11
    change ((x 1 4 (ix 0)) + (x 1 4 (ix 6))) + x 0 3 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 4))) + x 1 4 (ix 0) at h11
    have h12 := congrFun (hx.steinberg 1 0 3 (by decide) (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h12
    change ((((x 1 0 (ix 2)) + (x 1 0 (ix 8))) + x 0 3 (ix 2)) + 0) + x 1 0 (ix 2) = ((x 1 3 (ix 2)) + (x 1 3 (ix 8))) + x 0 3 (ix 2) at h12
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8 + h9 + h10 + h11 + h12
  · change ((x 1 0 (ix 6)) + 0) - (x 1 0 (ix 6)) = x 1 3 (ix 3)
    have h0 := congrFun (hx.commute 1 0 1 3 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 1 3 (ix 6)) + (x 1 3 (ix 3))) + x 1 0 (ix 6) = ((x 1 0 (ix 6)) + 0) + x 1 3 (ix 6) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 7)) + 0) - (x 1 0 (ix 7)) = x 1 3 (ix 4)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.square 0 1) (ix 5)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h1
    change ((x 0 1 (ix 5)) + (x 0 1 (ix 8))) + x 0 1 (ix 5) = 0 at h1
    have h2 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h2
    change ((((x 0 1 (ix 5)) + 0) + x 1 2 (ix 5)) + (((x 0 1 (ix 8)) + (x 0 1 (ix 9))) + x 1 2 (ix 8))) + x 0 1 (ix 5) = ((x 0 2 (ix 5)) + 0) + x 1 2 (ix 5) at h2
    have h3 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h3
    change ((((x 0 1 (ix 4)) + 0) + x 1 3 (ix 4)) + (((x 0 1 (ix 7)) + (x 0 1 (ix 9))) + x 1 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 3 (ix 4)) + 0) + x 1 3 (ix 4) at h3
    have h4 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 1 3 (ix 2)) + (x 1 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 5))) + x 1 3 (ix 2) at h4
    have h5 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h5
    change ((x 1 4 (ix 1)) + (x 1 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 5))) + x 1 4 (ix 1) at h5
    have h6 := congrFun (hx.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h6
    change ((x 1 4 (ix 0)) + (x 1 4 (ix 6))) + x 0 3 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 4))) + x 1 4 (ix 0) at h6
    have h7 := congrFun (hx.square 1 0) (ix 8)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h7
    change ((x 1 0 (ix 8)) + (x 1 0 (ix 5))) + x 1 0 (ix 8) = 0 at h7
    have h8 := congrFun (hx.commute 1 0 1 3 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h8
    change ((x 1 3 (ix 7)) + (x 1 3 (ix 4))) + x 1 0 (ix 7) = ((x 1 0 (ix 7)) + (x 1 0 (ix 9))) + x 1 3 (ix 7) at h8
    have h9 := congrFun (hx.steinberg 1 0 2 (by decide) (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h9
    change ((((x 1 0 (ix 8)) + 0) + x 0 2 (ix 8)) + (((x 1 0 (ix 5)) + (x 1 0 (ix 9))) + x 0 2 (ix 5))) + x 1 0 (ix 8) = ((x 1 2 (ix 8)) + 0) + x 0 2 (ix 8) at h9
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8 + h9
  · change ((x 1 0 (ix 8)) + 0) - (x 1 0 (ix 8)) = x 1 3 (ix 5)
    have h0 := congrFun (hx.commute 1 0 1 3 (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 1 3 (ix 8)) + (x 1 3 (ix 5))) + x 1 0 (ix 8) = ((x 1 0 (ix 8)) + 0) + x 1 3 (ix 8) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 3)) + 0) - (x 0 1 (ix 3)) = x 1 3 (ix 6)
    have h0 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 1 3 (ix 1)) + (x 1 3 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + 0) + x 1 3 (ix 1) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 4)) + (x 0 2 (ix 5))) - (x 0 1 (ix 4)) = x 1 3 (ix 7)
    have h0 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 1 3 (ix 2)) + (x 1 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 5))) + x 1 3 (ix 2) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 5)) + 0) - (x 0 1 (ix 5)) = x 1 3 (ix 8)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.square 0 1) (ix 5)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h1
    change ((x 0 1 (ix 5)) + (x 0 1 (ix 8))) + x 0 1 (ix 5) = 0 at h1
    have h2 := congrFun (hx.commute 0 1 0 2 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 0 2 (ix 4)) + (x 0 2 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + 0) + x 0 2 (ix 4) at h2
    have h3 := congrFun (hx.commute 0 1 0 2 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 0 2 (ix 5)) + (x 0 2 (ix 8))) + x 0 1 (ix 5) = ((x 0 1 (ix 5)) + (x 0 1 (ix 9))) + x 0 2 (ix 5) at h3
    have h4 := congrFun (hx.commute 0 1 2 3 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 2 3 (ix 4)) + (x 2 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + (x 0 1 (ix 5))) + x 2 3 (ix 4) at h4
    have h5 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h5
    change ((((x 0 1 (ix 2)) + (x 0 1 (ix 5))) + x 1 3 (ix 2)) + 0) + x 0 1 (ix 2) = ((x 0 3 (ix 2)) + (x 0 3 (ix 5))) + x 1 3 (ix 2) at h5
    have h6 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h6
    change ((((x 0 1 (ix 4)) + 0) + x 1 3 (ix 4)) + (((x 0 1 (ix 7)) + (x 0 1 (ix 9))) + x 1 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 3 (ix 4)) + 0) + x 1 3 (ix 4) at h6
    have h7 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h7
    change ((((x 0 1 (ix 5)) + 0) + x 1 3 (ix 5)) + (((x 0 1 (ix 8)) + 0) + x 1 3 (ix 8))) + x 0 1 (ix 5) = ((x 0 3 (ix 5)) + 0) + x 1 3 (ix 5) at h7
    have h8 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h8
    change ((x 1 3 (ix 2)) + (x 1 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 5))) + x 1 3 (ix 2) at h8
    have h9 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h9
    change ((x 1 4 (ix 1)) + (x 1 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 5))) + x 1 4 (ix 1) at h9
    have h10 := congrFun (hx.steinberg 0 2 3 (by decide) (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h10
    change ((((x 0 2 (ix 2)) + 0) + x 2 3 (ix 2)) + (((x 0 2 (ix 7)) + (x 0 2 (ix 8))) + x 2 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 3 (ix 2)) + 0) + x 2 3 (ix 2) at h10
    have h11 := congrFun (hx.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h11
    change ((x 1 4 (ix 0)) + (x 1 4 (ix 6))) + x 0 3 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 4))) + x 1 4 (ix 0) at h11
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8 + h9 + h10 + h11
  · change ((x 0 2 (ix 5)) + 0) - (x 0 2 (ix 5)) = x 1 3 (ix 9)
    have h0 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 1 3 (ix 5)) + (x 1 3 (ix 9))) + x 0 2 (ix 5) = ((x 0 2 (ix 5)) + 0) + x 1 3 (ix 5) at h0
    linear_combination (norm := (ring_nf; simp)) h0

private theorem exact_1_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 3)
    (hx : ElementaryRelations 3 x) (s : Fin 10) :
    act 1 4 (witness x) s - witness x s = x 1 4 (ix s) := by
  fin_cases s
  · change ((x 3 0 (ix 6)) + (x 1 0 (ix 7))) - (x 3 0 (ix 6)) = x 1 4 (ix 0)
    have h0 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 1 4 (ix 2)) + (x 1 4 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + 0) + x 1 4 (ix 2) at h0
    have h1 := congrFun (hx.steinberg 1 0 4 (by decide) (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h1
    change ((((x 1 0 (ix 0)) + (x 1 0 (ix 7))) + x 0 4 (ix 0)) + 0) + x 1 0 (ix 0) = ((x 1 4 (ix 0)) + (x 1 4 (ix 7))) + x 0 4 (ix 0) at h1
    linear_combination (norm := (ring_nf; simp)) h0 + h1
  · change ((x 2 0 (ix 6)) + (x 1 0 (ix 8))) - (x 2 0 (ix 6)) = x 1 4 (ix 1)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.square 0 1) (ix 5)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h1
    change ((x 0 1 (ix 5)) + (x 0 1 (ix 8))) + x 0 1 (ix 5) = 0 at h1
    have h2 := congrFun (hx.commute 0 1 0 2 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 0 2 (ix 3)) + (x 0 2 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + 0) + x 0 2 (ix 3) at h2
    have h3 := congrFun (hx.commute 0 1 0 2 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 0 2 (ix 5)) + (x 0 2 (ix 8))) + x 0 1 (ix 5) = ((x 0 1 (ix 5)) + (x 0 1 (ix 9))) + x 0 2 (ix 5) at h3
    have h4 := congrFun (hx.commute 0 1 2 4 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 2 4 (ix 3)) + (x 2 4 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + (x 0 1 (ix 5))) + x 2 4 (ix 3) at h4
    have h5 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h5
    change ((((x 0 1 (ix 4)) + 0) + x 1 3 (ix 4)) + (((x 0 1 (ix 7)) + (x 0 1 (ix 9))) + x 1 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 3 (ix 4)) + 0) + x 1 3 (ix 4) at h5
    have h6 := congrFun (hx.steinberg 0 1 4 (by decide) (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h6
    change ((((x 0 1 (ix 1)) + (x 0 1 (ix 5))) + x 1 4 (ix 1)) + 0) + x 0 1 (ix 1) = ((x 0 4 (ix 1)) + (x 0 4 (ix 5))) + x 1 4 (ix 1) at h6
    have h7 := congrFun (hx.steinberg 0 1 4 (by decide) (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h7
    change ((((x 0 1 (ix 5)) + 0) + x 1 4 (ix 5)) + (((x 0 1 (ix 8)) + 0) + x 1 4 (ix 8))) + x 0 1 (ix 5) = ((x 0 4 (ix 5)) + 0) + x 1 4 (ix 5) at h7
    have h8 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h8
    change ((x 1 3 (ix 2)) + (x 1 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 5))) + x 1 3 (ix 2) at h8
    have h9 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h9
    change ((x 1 4 (ix 1)) + (x 1 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 5))) + x 1 4 (ix 1) at h9
    have h10 := congrFun (hx.steinberg 0 2 4 (by decide) (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h10
    change ((((x 0 2 (ix 1)) + 0) + x 2 4 (ix 1)) + (((x 0 2 (ix 6)) + (x 0 2 (ix 8))) + x 2 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 4 (ix 1)) + 0) + x 2 4 (ix 1) at h10
    have h11 := congrFun (hx.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h11
    change ((x 1 4 (ix 0)) + (x 1 4 (ix 6))) + x 0 3 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 4))) + x 1 4 (ix 0) at h11
    have h12 := congrFun (hx.steinberg 1 0 4 (by decide) (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h12
    change ((((x 1 0 (ix 1)) + (x 1 0 (ix 8))) + x 0 4 (ix 1)) + 0) + x 1 0 (ix 1) = ((x 1 4 (ix 1)) + (x 1 4 (ix 8))) + x 0 4 (ix 1) at h12
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8 + h9 + h10 + h11 + h12
  · change ((x 2 0 (ix 7)) + 0) - (x 2 0 (ix 7)) = x 1 4 (ix 2)
    have h0 := congrFun (hx.steinberg 1 0 4 (by decide) (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h0
    change ((((x 1 0 (ix 2)) + 0) + x 0 4 (ix 2)) + 0) + x 1 0 (ix 2) = ((x 1 4 (ix 2)) + 0) + x 0 4 (ix 2) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 6)) + 0) - (x 1 0 (ix 6)) = x 1 4 (ix 3)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.square 0 1) (ix 5)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h1
    change ((x 0 1 (ix 5)) + (x 0 1 (ix 8))) + x 0 1 (ix 5) = 0 at h1
    have h2 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h2
    change ((((x 0 1 (ix 5)) + 0) + x 1 2 (ix 5)) + (((x 0 1 (ix 8)) + (x 0 1 (ix 9))) + x 1 2 (ix 8))) + x 0 1 (ix 5) = ((x 0 2 (ix 5)) + 0) + x 1 2 (ix 5) at h2
    have h3 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h3
    change ((((x 0 1 (ix 4)) + 0) + x 1 3 (ix 4)) + (((x 0 1 (ix 7)) + (x 0 1 (ix 9))) + x 1 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 3 (ix 4)) + 0) + x 1 3 (ix 4) at h3
    have h4 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 1 3 (ix 2)) + (x 1 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 5))) + x 1 3 (ix 2) at h4
    have h5 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h5
    change ((x 1 4 (ix 1)) + (x 1 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 5))) + x 1 4 (ix 1) at h5
    have h6 := congrFun (hx.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h6
    change ((x 1 4 (ix 0)) + (x 1 4 (ix 6))) + x 0 3 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 4))) + x 1 4 (ix 0) at h6
    have h7 := congrFun (hx.square 1 0) (ix 8)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h7
    change ((x 1 0 (ix 8)) + (x 1 0 (ix 5))) + x 1 0 (ix 8) = 0 at h7
    have h8 := congrFun (hx.commute 1 0 1 4 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h8
    change ((x 1 4 (ix 6)) + (x 1 4 (ix 3))) + x 1 0 (ix 6) = ((x 1 0 (ix 6)) + (x 1 0 (ix 9))) + x 1 4 (ix 6) at h8
    have h9 := congrFun (hx.steinberg 1 0 2 (by decide) (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h9
    change ((((x 1 0 (ix 8)) + 0) + x 0 2 (ix 8)) + (((x 1 0 (ix 5)) + (x 1 0 (ix 9))) + x 0 2 (ix 5))) + x 1 0 (ix 8) = ((x 1 2 (ix 8)) + 0) + x 0 2 (ix 8) at h9
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8 + h9
  · change ((x 1 0 (ix 7)) + 0) - (x 1 0 (ix 7)) = x 1 4 (ix 4)
    have h0 := congrFun (hx.commute 1 0 1 4 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 1 4 (ix 7)) + (x 1 4 (ix 4))) + x 1 0 (ix 7) = ((x 1 0 (ix 7)) + 0) + x 1 4 (ix 7) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 8)) + 0) - (x 1 0 (ix 8)) = x 1 4 (ix 5)
    have h0 := congrFun (hx.commute 1 0 1 4 (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 1 4 (ix 8)) + (x 1 4 (ix 5))) + x 1 0 (ix 8) = ((x 1 0 (ix 8)) + 0) + x 1 4 (ix 8) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 3)) + (x 0 2 (ix 5))) - (x 0 1 (ix 3)) = x 1 4 (ix 6)
    have h0 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 1 4 (ix 1)) + (x 1 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 5))) + x 1 4 (ix 1) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 4)) + 0) - (x 0 1 (ix 4)) = x 1 4 (ix 7)
    have h0 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 1 4 (ix 2)) + (x 1 4 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + 0) + x 1 4 (ix 2) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 5)) + 0) - (x 0 1 (ix 5)) = x 1 4 (ix 8)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.square 0 1) (ix 5)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h1
    change ((x 0 1 (ix 5)) + (x 0 1 (ix 8))) + x 0 1 (ix 5) = 0 at h1
    have h2 := congrFun (hx.commute 0 1 0 2 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 0 2 (ix 3)) + (x 0 2 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + 0) + x 0 2 (ix 3) at h2
    have h3 := congrFun (hx.commute 0 1 0 2 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 0 2 (ix 5)) + (x 0 2 (ix 8))) + x 0 1 (ix 5) = ((x 0 1 (ix 5)) + (x 0 1 (ix 9))) + x 0 2 (ix 5) at h3
    have h4 := congrFun (hx.commute 0 1 2 4 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 2 4 (ix 3)) + (x 2 4 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + (x 0 1 (ix 5))) + x 2 4 (ix 3) at h4
    have h5 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h5
    change ((((x 0 1 (ix 4)) + 0) + x 1 3 (ix 4)) + (((x 0 1 (ix 7)) + (x 0 1 (ix 9))) + x 1 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 3 (ix 4)) + 0) + x 1 3 (ix 4) at h5
    have h6 := congrFun (hx.steinberg 0 1 4 (by decide) (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h6
    change ((((x 0 1 (ix 1)) + (x 0 1 (ix 5))) + x 1 4 (ix 1)) + 0) + x 0 1 (ix 1) = ((x 0 4 (ix 1)) + (x 0 4 (ix 5))) + x 1 4 (ix 1) at h6
    have h7 := congrFun (hx.steinberg 0 1 4 (by decide) (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h7
    change ((((x 0 1 (ix 5)) + 0) + x 1 4 (ix 5)) + (((x 0 1 (ix 8)) + 0) + x 1 4 (ix 8))) + x 0 1 (ix 5) = ((x 0 4 (ix 5)) + 0) + x 1 4 (ix 5) at h7
    have h8 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h8
    change ((x 1 3 (ix 2)) + (x 1 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 5))) + x 1 3 (ix 2) at h8
    have h9 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h9
    change ((x 1 4 (ix 1)) + (x 1 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 5))) + x 1 4 (ix 1) at h9
    have h10 := congrFun (hx.steinberg 0 2 4 (by decide) (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h10
    change ((((x 0 2 (ix 1)) + 0) + x 2 4 (ix 1)) + (((x 0 2 (ix 6)) + (x 0 2 (ix 8))) + x 2 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 4 (ix 1)) + 0) + x 2 4 (ix 1) at h10
    have h11 := congrFun (hx.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h11
    change ((x 1 4 (ix 0)) + (x 1 4 (ix 6))) + x 0 3 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 4))) + x 1 4 (ix 0) at h11
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8 + h9 + h10 + h11
  · change ((x 0 2 (ix 5)) + 0) - (x 0 2 (ix 5)) = x 1 4 (ix 9)
    have h0 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 1 4 (ix 5)) + (x 1 4 (ix 9))) + x 0 2 (ix 5) = ((x 0 2 (ix 5)) + 0) + x 1 4 (ix 5) at h0
    linear_combination (norm := (ring_nf; simp)) h0

private theorem exact_2_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 3)
    (hx : ElementaryRelations 3 x) (s : Fin 10) :
    act 2 0 (witness x) s - witness x s = x 2 0 (ix s) := by
  fin_cases s
  · change ((x 3 0 (ix 6)) + 0) - (x 3 0 (ix 6)) = x 2 0 (ix 0)
    have h0 := congrFun (hx.commute 2 0 3 1 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 1 (ix 3)) + 0) + x 2 0 (ix 3) = ((x 2 0 (ix 3)) + (x 2 0 (ix 0))) + x 3 1 (ix 3) at h0
    linear_combination (norm := (ring)) h0
  · change ((x 2 0 (ix 6)) + 0) - (x 2 0 (ix 6)) = x 2 0 (ix 1)
    have h0 := congrFun (hx.square 2 0) (ix 6)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 2 0 (ix 6)) + (x 2 0 (ix 1))) + x 2 0 (ix 6) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 7)) + 0) - (x 2 0 (ix 7)) = x 2 0 (ix 2)
    have h0 := congrFun (hx.square 2 0) (ix 7)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 2 0 (ix 7)) + (x 2 0 (ix 2))) + x 2 0 (ix 7) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 6)) + 0) - (x 1 0 (ix 6)) = x 2 0 (ix 3)
    have h0 := congrFun (hx.commute 1 0 2 0 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 0 (ix 6)) + (x 2 0 (ix 3))) + x 1 0 (ix 6) = ((x 1 0 (ix 6)) + (x 1 0 (ix 1))) + x 2 0 (ix 6) at h0
    have h1 := congrFun (hx.commute 1 0 2 3 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 2 3 (ix 0)) + 0) + x 1 0 (ix 0) = ((x 1 0 (ix 0)) + (x 1 0 (ix 1))) + x 2 3 (ix 0) at h1
    linear_combination (norm := (ring_nf; simp)) h0 + h1
  · change ((x 1 0 (ix 7)) + 0) - (x 1 0 (ix 7)) = x 2 0 (ix 4)
    have h0 := congrFun (hx.commute 1 0 2 0 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 0 (ix 7)) + (x 2 0 (ix 4))) + x 1 0 (ix 7) = ((x 1 0 (ix 7)) + (x 1 0 (ix 2))) + x 2 0 (ix 7) at h0
    have h1 := congrFun (hx.commute 1 0 2 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 2 4 (ix 0)) + 0) + x 1 0 (ix 0) = ((x 1 0 (ix 0)) + (x 1 0 (ix 2))) + x 2 4 (ix 0) at h1
    linear_combination (norm := (ring_nf; simp)) h0 + h1
  · change ((x 1 0 (ix 8)) + 0) - (x 1 0 (ix 8)) = x 2 0 (ix 5)
    have h0 := congrFun (hx.commute 1 0 2 0 (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 0 (ix 8)) + (x 2 0 (ix 5))) + x 1 0 (ix 8) = ((x 1 0 (ix 8)) + 0) + x 2 0 (ix 8) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 3)) + (x 2 0 (ix 6))) - (x 0 1 (ix 3)) = x 2 0 (ix 6)
    ring
  · change ((x 0 1 (ix 4)) + (x 2 0 (ix 7))) - (x 0 1 (ix 4)) = x 2 0 (ix 7)
    ring
  · change ((x 0 1 (ix 5)) + 0) - (x 0 1 (ix 5)) = x 2 0 (ix 8)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h1
    change ((((x 0 1 (ix 8)) + (x 0 1 (ix 9))) + x 1 2 (ix 8)) + 0) + x 0 1 (ix 8) = ((x 0 2 (ix 8)) + (x 0 2 (ix 9))) + x 1 2 (ix 8) at h1
    have h2 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h2
    change ((((x 0 1 (ix 4)) + 0) + x 1 3 (ix 4)) + (((x 0 1 (ix 7)) + (x 0 1 (ix 9))) + x 1 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 3 (ix 4)) + 0) + x 1 3 (ix 4) at h2
    have h3 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 1 3 (ix 2)) + (x 1 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 5))) + x 1 3 (ix 2) at h3
    have h4 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 1 4 (ix 1)) + (x 1 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 5))) + x 1 4 (ix 1) at h4
    have h5 := congrFun (hx.steinberg 0 2 1 (by decide) (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h5
    change ((((x 0 2 (ix 5)) + 0) + x 2 1 (ix 5)) + (((x 0 2 (ix 9)) + (x 0 2 (ix 8))) + x 2 1 (ix 9))) + x 0 2 (ix 5) = ((x 0 1 (ix 5)) + 0) + x 2 1 (ix 5) at h5
    have h6 := congrFun (hx.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h6
    change ((x 1 4 (ix 0)) + (x 1 4 (ix 6))) + x 0 3 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 4))) + x 1 4 (ix 0) at h6
    have h7 := congrFun (hx.commute 1 0 2 0 (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h7
    change ((x 2 0 (ix 8)) + (x 2 0 (ix 5))) + x 1 0 (ix 8) = ((x 1 0 (ix 8)) + 0) + x 2 0 (ix 8) at h7
    have h8 := congrFun (hx.steinberg 2 0 1 (by decide) (by decide) (by decide)) (ix 9)
    simp only [Pi.add_apply, action_coords] at h8
    change ((((x 2 0 (ix 9)) + 0) + x 0 1 (ix 9)) + (((x 2 0 (ix 5)) + (x 2 0 (ix 8))) + x 0 1 (ix 5))) + x 2 0 (ix 9) = ((x 2 1 (ix 9)) + 0) + x 0 1 (ix 9) at h8
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8
  · change ((x 0 2 (ix 5)) + (x 1 0 (ix 8))) - (x 0 2 (ix 5)) = x 2 0 (ix 9)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.square 0 1) (ix 5)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h1
    change ((x 0 1 (ix 5)) + (x 0 1 (ix 8))) + x 0 1 (ix 5) = 0 at h1
    have h2 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h2
    change ((((x 0 1 (ix 5)) + 0) + x 1 2 (ix 5)) + (((x 0 1 (ix 8)) + (x 0 1 (ix 9))) + x 1 2 (ix 8))) + x 0 1 (ix 5) = ((x 0 2 (ix 5)) + 0) + x 1 2 (ix 5) at h2
    have h3 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h3
    change ((((x 0 1 (ix 4)) + 0) + x 1 3 (ix 4)) + (((x 0 1 (ix 7)) + (x 0 1 (ix 9))) + x 1 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 3 (ix 4)) + 0) + x 1 3 (ix 4) at h3
    have h4 := congrFun (hx.commute 0 2 1 2 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 1 2 (ix 5)) + (x 1 2 (ix 9))) + x 0 2 (ix 5) = ((x 0 2 (ix 5)) + 0) + x 1 2 (ix 5) at h4
    have h5 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h5
    change ((x 1 3 (ix 2)) + (x 1 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 5))) + x 1 3 (ix 2) at h5
    have h6 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h6
    change ((x 1 4 (ix 1)) + (x 1 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 5))) + x 1 4 (ix 1) at h6
    have h7 := congrFun (hx.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h7
    change ((x 1 4 (ix 0)) + (x 1 4 (ix 6))) + x 0 3 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 4))) + x 1 4 (ix 0) at h7
    have h8 := congrFun (hx.square 1 0) (ix 8)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h8
    change ((x 1 0 (ix 8)) + (x 1 0 (ix 5))) + x 1 0 (ix 8) = 0 at h8
    have h9 := congrFun (hx.commute 1 0 1 2 (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h9
    change ((x 1 2 (ix 8)) + (x 1 2 (ix 5))) + x 1 0 (ix 8) = ((x 1 0 (ix 8)) + (x 1 0 (ix 9))) + x 1 2 (ix 8) at h9
    have h10 := congrFun (hx.steinberg 1 0 2 (by decide) (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h10
    change ((((x 1 0 (ix 8)) + 0) + x 0 2 (ix 8)) + (((x 1 0 (ix 5)) + (x 1 0 (ix 9))) + x 0 2 (ix 5))) + x 1 0 (ix 8) = ((x 1 2 (ix 8)) + 0) + x 0 2 (ix 8) at h10
    have h11 := congrFun (hx.steinberg 1 2 0 (by decide) (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h11
    change ((((x 1 2 (ix 8)) + 0) + x 2 0 (ix 8)) + (((x 1 2 (ix 9)) + (x 1 2 (ix 5))) + x 2 0 (ix 9))) + x 1 2 (ix 8) = ((x 1 0 (ix 8)) + 0) + x 2 0 (ix 8) at h11
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8 + h9 + h10 + h11

private theorem exact_2_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 3)
    (hx : ElementaryRelations 3 x) (s : Fin 10) :
    act 2 1 (witness x) s - witness x s = x 2 1 (ix s) := by
  fin_cases s
  · change ((x 3 0 (ix 6)) + 0) - (x 3 0 (ix 6)) = x 2 1 (ix 0)
    have h0 := congrFun (hx.steinberg 2 0 1 (by decide) (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h0
    change ((((x 2 0 (ix 0)) + 0) + x 0 1 (ix 0)) + 0) + x 2 0 (ix 0) = ((x 2 1 (ix 0)) + 0) + x 0 1 (ix 0) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 6)) + 0) - (x 2 0 (ix 6)) = x 2 1 (ix 1)
    have h0 := congrFun (hx.commute 2 0 2 1 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 1 (ix 6)) + (x 2 1 (ix 1))) + x 2 0 (ix 6) = ((x 2 0 (ix 6)) + 0) + x 2 1 (ix 6) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 7)) + 0) - (x 2 0 (ix 7)) = x 2 1 (ix 2)
    have h0 := congrFun (hx.commute 2 0 2 1 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 1 (ix 7)) + (x 2 1 (ix 2))) + x 2 0 (ix 7) = ((x 2 0 (ix 7)) + 0) + x 2 1 (ix 7) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 6)) + (x 2 0 (ix 6))) - (x 1 0 (ix 6)) = x 2 1 (ix 3)
    have h0 := congrFun (hx.commute 0 1 2 1 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 1 (ix 3)) + (x 2 1 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + (x 0 1 (ix 1))) + x 2 1 (ix 3) at h0
    have h1 := congrFun (hx.commute 0 1 2 3 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 2 3 (ix 0)) + 0) + x 0 1 (ix 0) = ((x 0 1 (ix 0)) + (x 0 1 (ix 1))) + x 2 3 (ix 0) at h1
    have h2 := congrFun (hx.steinberg 2 0 1 (by decide) (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h2
    change ((((x 2 0 (ix 3)) + (x 2 0 (ix 6))) + x 0 1 (ix 3)) + 0) + x 2 0 (ix 3) = ((x 2 1 (ix 3)) + (x 2 1 (ix 6))) + x 0 1 (ix 3) at h2
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2
  · change ((x 1 0 (ix 7)) + (x 2 0 (ix 7))) - (x 1 0 (ix 7)) = x 2 1 (ix 4)
    have h0 := congrFun (hx.commute 0 1 2 1 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 1 (ix 4)) + (x 2 1 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + (x 0 1 (ix 2))) + x 2 1 (ix 4) at h0
    have h1 := congrFun (hx.commute 0 1 2 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 2 4 (ix 0)) + 0) + x 0 1 (ix 0) = ((x 0 1 (ix 0)) + (x 0 1 (ix 2))) + x 2 4 (ix 0) at h1
    have h2 := congrFun (hx.steinberg 2 0 1 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h2
    change ((((x 2 0 (ix 4)) + (x 2 0 (ix 7))) + x 0 1 (ix 4)) + 0) + x 2 0 (ix 4) = ((x 2 1 (ix 4)) + (x 2 1 (ix 7))) + x 0 1 (ix 4) at h2
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2
  · change ((x 1 0 (ix 8)) + 0) - (x 1 0 (ix 8)) = x 2 1 (ix 5)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h1
    change ((((x 0 1 (ix 8)) + (x 0 1 (ix 9))) + x 1 2 (ix 8)) + 0) + x 0 1 (ix 8) = ((x 0 2 (ix 8)) + (x 0 2 (ix 9))) + x 1 2 (ix 8) at h1
    have h2 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h2
    change ((((x 0 1 (ix 4)) + 0) + x 1 3 (ix 4)) + (((x 0 1 (ix 7)) + (x 0 1 (ix 9))) + x 1 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 3 (ix 4)) + 0) + x 1 3 (ix 4) at h2
    have h3 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 1 3 (ix 2)) + (x 1 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 5))) + x 1 3 (ix 2) at h3
    have h4 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 1 4 (ix 1)) + (x 1 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 5))) + x 1 4 (ix 1) at h4
    have h5 := congrFun (hx.steinberg 0 2 1 (by decide) (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h5
    change ((((x 0 2 (ix 5)) + 0) + x 2 1 (ix 5)) + (((x 0 2 (ix 9)) + (x 0 2 (ix 8))) + x 2 1 (ix 9))) + x 0 2 (ix 5) = ((x 0 1 (ix 5)) + 0) + x 2 1 (ix 5) at h5
    have h6 := congrFun (hx.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h6
    change ((x 1 4 (ix 0)) + (x 1 4 (ix 6))) + x 0 3 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 4))) + x 1 4 (ix 0) at h6
    have h7 := congrFun (hx.commute 1 0 2 0 (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h7
    change ((x 2 0 (ix 8)) + (x 2 0 (ix 5))) + x 1 0 (ix 8) = ((x 1 0 (ix 8)) + 0) + x 2 0 (ix 8) at h7
    have h8 := congrFun (hx.commute 2 0 2 1 (by decide) (by decide)) (ix 9)
    simp only [Pi.add_apply, action_coords] at h8
    change ((x 2 1 (ix 9)) + (x 2 1 (ix 5))) + x 2 0 (ix 9) = ((x 2 0 (ix 9)) + (x 2 0 (ix 8))) + x 2 1 (ix 9) at h8
    have h9 := congrFun (hx.steinberg 2 0 1 (by decide) (by decide) (by decide)) (ix 9)
    simp only [Pi.add_apply, action_coords] at h9
    change ((((x 2 0 (ix 9)) + 0) + x 0 1 (ix 9)) + (((x 2 0 (ix 5)) + (x 2 0 (ix 8))) + x 0 1 (ix 5))) + x 2 0 (ix 9) = ((x 2 1 (ix 9)) + 0) + x 0 1 (ix 9) at h9
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8 + h9
  · change ((x 0 1 (ix 3)) + 0) - (x 0 1 (ix 3)) = x 2 1 (ix 6)
    have h0 := congrFun (hx.commute 0 1 2 1 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 1 (ix 3)) + (x 2 1 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + (x 0 1 (ix 1))) + x 2 1 (ix 3) at h0
    have h1 := congrFun (hx.commute 0 1 2 3 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 2 3 (ix 0)) + 0) + x 0 1 (ix 0) = ((x 0 1 (ix 0)) + (x 0 1 (ix 1))) + x 2 3 (ix 0) at h1
    linear_combination (norm := (ring_nf; simp)) h0 + h1
  · change ((x 0 1 (ix 4)) + 0) - (x 0 1 (ix 4)) = x 2 1 (ix 7)
    have h0 := congrFun (hx.commute 0 1 2 1 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 1 (ix 4)) + (x 2 1 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + (x 0 1 (ix 2))) + x 2 1 (ix 4) at h0
    have h1 := congrFun (hx.commute 0 1 2 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 2 4 (ix 0)) + 0) + x 0 1 (ix 0) = ((x 0 1 (ix 0)) + (x 0 1 (ix 2))) + x 2 4 (ix 0) at h1
    linear_combination (norm := (ring_nf; simp)) h0 + h1
  · change ((x 0 1 (ix 5)) + 0) - (x 0 1 (ix 5)) = x 2 1 (ix 8)
    have h0 := congrFun (hx.commute 0 1 2 1 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 1 (ix 5)) + (x 2 1 (ix 8))) + x 0 1 (ix 5) = ((x 0 1 (ix 5)) + 0) + x 2 1 (ix 5) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 2 (ix 5)) + (x 0 1 (ix 5))) - (x 0 2 (ix 5)) = x 2 1 (ix 9)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h1
    change ((((x 0 1 (ix 8)) + (x 0 1 (ix 9))) + x 1 2 (ix 8)) + 0) + x 0 1 (ix 8) = ((x 0 2 (ix 8)) + (x 0 2 (ix 9))) + x 1 2 (ix 8) at h1
    have h2 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h2
    change ((((x 0 1 (ix 4)) + 0) + x 1 3 (ix 4)) + (((x 0 1 (ix 7)) + (x 0 1 (ix 9))) + x 1 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 3 (ix 4)) + 0) + x 1 3 (ix 4) at h2
    have h3 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 1 3 (ix 2)) + (x 1 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 5))) + x 1 3 (ix 2) at h3
    have h4 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 1 4 (ix 1)) + (x 1 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 5))) + x 1 4 (ix 1) at h4
    have h5 := congrFun (hx.steinberg 0 2 1 (by decide) (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h5
    change ((((x 0 2 (ix 5)) + 0) + x 2 1 (ix 5)) + (((x 0 2 (ix 9)) + (x 0 2 (ix 8))) + x 2 1 (ix 9))) + x 0 2 (ix 5) = ((x 0 1 (ix 5)) + 0) + x 2 1 (ix 5) at h5
    have h6 := congrFun (hx.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h6
    change ((x 1 4 (ix 0)) + (x 1 4 (ix 6))) + x 0 3 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 4))) + x 1 4 (ix 0) at h6
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5 + h6

private theorem exact_2_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 3)
    (hx : ElementaryRelations 3 x) (s : Fin 10) :
    act 2 2 (witness x) s - witness x s = x 2 2 (ix s) := by
  fin_cases s
  · change ((x 3 0 (ix 6)) + 0) - (x 3 0 (ix 6)) = x 2 2 (ix 0)
    have h0 := congrFun (hx.diagonal 2) (ix 0)
    change x 2 2 (ix 0) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 6)) + 0) - (x 2 0 (ix 6)) = x 2 2 (ix 1)
    have h0 := congrFun (hx.diagonal 2) (ix 1)
    change x 2 2 (ix 1) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 7)) + 0) - (x 2 0 (ix 7)) = x 2 2 (ix 2)
    have h0 := congrFun (hx.diagonal 2) (ix 2)
    change x 2 2 (ix 2) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 6)) + 0) - (x 1 0 (ix 6)) = x 2 2 (ix 3)
    have h0 := congrFun (hx.commute 1 0 2 2 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 2 (ix 6)) + (x 2 2 (ix 3))) + x 1 0 (ix 6) = ((x 1 0 (ix 6)) + 0) + x 2 2 (ix 6) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 7)) + 0) - (x 1 0 (ix 7)) = x 2 2 (ix 4)
    have h0 := congrFun (hx.commute 1 0 2 2 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 2 (ix 7)) + (x 2 2 (ix 4))) + x 1 0 (ix 7) = ((x 1 0 (ix 7)) + 0) + x 2 2 (ix 7) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 8)) + 0) - (x 1 0 (ix 8)) = x 2 2 (ix 5)
    have h0 := congrFun (hx.commute 1 0 2 2 (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 2 (ix 8)) + (x 2 2 (ix 5))) + x 1 0 (ix 8) = ((x 1 0 (ix 8)) + 0) + x 2 2 (ix 8) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 3)) + 0) - (x 0 1 (ix 3)) = x 2 2 (ix 6)
    have h0 := congrFun (hx.commute 0 1 2 2 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 2 (ix 3)) + (x 2 2 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + 0) + x 2 2 (ix 3) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 4)) + 0) - (x 0 1 (ix 4)) = x 2 2 (ix 7)
    have h0 := congrFun (hx.commute 0 1 2 2 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 2 (ix 4)) + (x 2 2 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + 0) + x 2 2 (ix 4) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 5)) + 0) - (x 0 1 (ix 5)) = x 2 2 (ix 8)
    have h0 := congrFun (hx.commute 0 1 2 2 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 2 (ix 5)) + (x 2 2 (ix 8))) + x 0 1 (ix 5) = ((x 0 1 (ix 5)) + 0) + x 2 2 (ix 5) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 2 (ix 5)) + 0) - (x 0 2 (ix 5)) = x 2 2 (ix 9)
    have h0 := congrFun (hx.commute 0 3 2 2 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 2 (ix 4)) + (x 2 2 (ix 9))) + x 0 3 (ix 4) = ((x 0 3 (ix 4)) + 0) + x 2 2 (ix 4) at h0
    linear_combination (norm := (ring_nf; simp)) h0

private theorem exact_2_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 3)
    (hx : ElementaryRelations 3 x) (s : Fin 10) :
    act 2 3 (witness x) s - witness x s = x 2 3 (ix s) := by
  fin_cases s
  · change ((x 3 0 (ix 6)) + (x 2 0 (ix 6))) - (x 3 0 (ix 6)) = x 2 3 (ix 0)
    have h0 := congrFun (hx.commute 0 1 2 3 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 3 (ix 3)) + (x 2 3 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + 0) + x 2 3 (ix 3) at h0
    have h1 := congrFun (hx.steinberg 2 0 3 (by decide) (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h1
    change ((((x 2 0 (ix 0)) + (x 2 0 (ix 6))) + x 0 3 (ix 0)) + 0) + x 2 0 (ix 0) = ((x 2 3 (ix 0)) + (x 2 3 (ix 6))) + x 0 3 (ix 0) at h1
    linear_combination (norm := (ring_nf; simp)) h0 + h1
  · change ((x 2 0 (ix 6)) + 0) - (x 2 0 (ix 6)) = x 2 3 (ix 1)
    have h0 := congrFun (hx.commute 2 0 2 3 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 3 (ix 6)) + (x 2 3 (ix 1))) + x 2 0 (ix 6) = ((x 2 0 (ix 6)) + 0) + x 2 3 (ix 6) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 7)) + 0) - (x 2 0 (ix 7)) = x 2 3 (ix 2)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h1
    change ((((x 0 1 (ix 8)) + (x 0 1 (ix 9))) + x 1 2 (ix 8)) + 0) + x 0 1 (ix 8) = ((x 0 2 (ix 8)) + (x 0 2 (ix 9))) + x 1 2 (ix 8) at h1
    have h2 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h2
    change ((((x 0 1 (ix 4)) + 0) + x 1 3 (ix 4)) + (((x 0 1 (ix 7)) + (x 0 1 (ix 9))) + x 1 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 3 (ix 4)) + 0) + x 1 3 (ix 4) at h2
    have h3 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 1 3 (ix 2)) + (x 1 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 5))) + x 1 3 (ix 2) at h3
    have h4 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 1 4 (ix 1)) + (x 1 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 5))) + x 1 4 (ix 1) at h4
    have h5 := congrFun (hx.steinberg 0 2 1 (by decide) (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h5
    change ((((x 0 2 (ix 5)) + 0) + x 2 1 (ix 5)) + (((x 0 2 (ix 9)) + (x 0 2 (ix 8))) + x 2 1 (ix 9))) + x 0 2 (ix 5) = ((x 0 1 (ix 5)) + 0) + x 2 1 (ix 5) at h5
    have h6 := congrFun (hx.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h6
    change ((x 1 4 (ix 0)) + (x 1 4 (ix 6))) + x 0 3 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 4))) + x 1 4 (ix 0) at h6
    have h7 := congrFun (hx.commute 1 0 2 0 (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h7
    change ((x 2 0 (ix 8)) + (x 2 0 (ix 5))) + x 1 0 (ix 8) = ((x 1 0 (ix 8)) + 0) + x 2 0 (ix 8) at h7
    have h8 := congrFun (hx.commute 2 0 2 3 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h8
    change ((x 2 3 (ix 7)) + (x 2 3 (ix 2))) + x 2 0 (ix 7) = ((x 2 0 (ix 7)) + (x 2 0 (ix 8))) + x 2 3 (ix 7) at h8
    have h9 := congrFun (hx.steinberg 2 0 1 (by decide) (by decide) (by decide)) (ix 9)
    simp only [Pi.add_apply, action_coords] at h9
    change ((((x 2 0 (ix 9)) + 0) + x 0 1 (ix 9)) + (((x 2 0 (ix 5)) + (x 2 0 (ix 8))) + x 0 1 (ix 5))) + x 2 0 (ix 9) = ((x 2 1 (ix 9)) + 0) + x 0 1 (ix 9) at h9
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8 + h9
  · change ((x 1 0 (ix 6)) + 0) - (x 1 0 (ix 6)) = x 2 3 (ix 3)
    have h0 := congrFun (hx.commute 1 0 2 3 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 3 (ix 6)) + (x 2 3 (ix 3))) + x 1 0 (ix 6) = ((x 1 0 (ix 6)) + 0) + x 2 3 (ix 6) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 7)) + (x 1 0 (ix 8))) - (x 1 0 (ix 7)) = x 2 3 (ix 4)
    have h0 := congrFun (hx.commute 1 0 2 3 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 3 (ix 7)) + (x 2 3 (ix 4))) + x 1 0 (ix 7) = ((x 1 0 (ix 7)) + (x 1 0 (ix 8))) + x 2 3 (ix 7) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 8)) + 0) - (x 1 0 (ix 8)) = x 2 3 (ix 5)
    have h0 := congrFun (hx.commute 1 0 2 3 (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 3 (ix 8)) + (x 2 3 (ix 5))) + x 1 0 (ix 8) = ((x 1 0 (ix 8)) + 0) + x 2 3 (ix 8) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 3)) + 0) - (x 0 1 (ix 3)) = x 2 3 (ix 6)
    have h0 := congrFun (hx.commute 0 1 2 3 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 3 (ix 3)) + (x 2 3 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + 0) + x 2 3 (ix 3) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 4)) + (x 0 1 (ix 5))) - (x 0 1 (ix 4)) = x 2 3 (ix 7)
    have h0 := congrFun (hx.commute 0 1 2 3 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 3 (ix 4)) + (x 2 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + (x 0 1 (ix 5))) + x 2 3 (ix 4) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 5)) + 0) - (x 0 1 (ix 5)) = x 2 3 (ix 8)
    have h0 := congrFun (hx.commute 0 1 2 3 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 3 (ix 5)) + (x 2 3 (ix 8))) + x 0 1 (ix 5) = ((x 0 1 (ix 5)) + 0) + x 2 3 (ix 5) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 2 (ix 5)) + 0) - (x 0 2 (ix 5)) = x 2 3 (ix 9)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.commute 0 1 0 2 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 0 2 (ix 4)) + (x 0 2 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + 0) + x 0 2 (ix 4) at h1
    have h2 := congrFun (hx.commute 0 1 2 3 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 2 3 (ix 4)) + (x 2 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + (x 0 1 (ix 5))) + x 2 3 (ix 4) at h2
    have h3 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h3
    change ((((x 0 1 (ix 8)) + (x 0 1 (ix 9))) + x 1 2 (ix 8)) + 0) + x 0 1 (ix 8) = ((x 0 2 (ix 8)) + (x 0 2 (ix 9))) + x 1 2 (ix 8) at h3
    have h4 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h4
    change ((((x 0 1 (ix 2)) + (x 0 1 (ix 5))) + x 1 3 (ix 2)) + 0) + x 0 1 (ix 2) = ((x 0 3 (ix 2)) + (x 0 3 (ix 5))) + x 1 3 (ix 2) at h4
    have h5 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h5
    change ((((x 0 1 (ix 4)) + 0) + x 1 3 (ix 4)) + (((x 0 1 (ix 7)) + (x 0 1 (ix 9))) + x 1 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 3 (ix 4)) + 0) + x 1 3 (ix 4) at h5
    have h6 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h6
    change ((x 1 3 (ix 2)) + (x 1 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 5))) + x 1 3 (ix 2) at h6
    have h7 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h7
    change ((x 1 4 (ix 1)) + (x 1 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 5))) + x 1 4 (ix 1) at h7
    have h8 := congrFun (hx.steinberg 0 2 3 (by decide) (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h8
    change ((((x 0 2 (ix 2)) + 0) + x 2 3 (ix 2)) + (((x 0 2 (ix 7)) + (x 0 2 (ix 8))) + x 2 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 3 (ix 2)) + 0) + x 2 3 (ix 2) at h8
    have h9 := congrFun (hx.steinberg 0 2 3 (by decide) (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h9
    change ((((x 0 2 (ix 5)) + 0) + x 2 3 (ix 5)) + (((x 0 2 (ix 9)) + 0) + x 2 3 (ix 9))) + x 0 2 (ix 5) = ((x 0 3 (ix 5)) + 0) + x 2 3 (ix 5) at h9
    have h10 := congrFun (hx.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h10
    change ((x 1 4 (ix 0)) + (x 1 4 (ix 6))) + x 0 3 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 4))) + x 1 4 (ix 0) at h10
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8 + h9 + h10

private theorem exact_2_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 3)
    (hx : ElementaryRelations 3 x) (s : Fin 10) :
    act 2 4 (witness x) s - witness x s = x 2 4 (ix s) := by
  fin_cases s
  · change ((x 3 0 (ix 6)) + (x 2 0 (ix 7))) - (x 3 0 (ix 6)) = x 2 4 (ix 0)
    have h0 := congrFun (hx.commute 0 1 2 4 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 4 (ix 4)) + (x 2 4 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + 0) + x 2 4 (ix 4) at h0
    have h1 := congrFun (hx.steinberg 2 0 4 (by decide) (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h1
    change ((((x 2 0 (ix 0)) + (x 2 0 (ix 7))) + x 0 4 (ix 0)) + 0) + x 2 0 (ix 0) = ((x 2 4 (ix 0)) + (x 2 4 (ix 7))) + x 0 4 (ix 0) at h1
    linear_combination (norm := (ring_nf; simp)) h0 + h1
  · change ((x 2 0 (ix 6)) + 0) - (x 2 0 (ix 6)) = x 2 4 (ix 1)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h1
    change ((((x 0 1 (ix 8)) + (x 0 1 (ix 9))) + x 1 2 (ix 8)) + 0) + x 0 1 (ix 8) = ((x 0 2 (ix 8)) + (x 0 2 (ix 9))) + x 1 2 (ix 8) at h1
    have h2 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h2
    change ((((x 0 1 (ix 4)) + 0) + x 1 3 (ix 4)) + (((x 0 1 (ix 7)) + (x 0 1 (ix 9))) + x 1 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 3 (ix 4)) + 0) + x 1 3 (ix 4) at h2
    have h3 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 1 3 (ix 2)) + (x 1 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 5))) + x 1 3 (ix 2) at h3
    have h4 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 1 4 (ix 1)) + (x 1 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 5))) + x 1 4 (ix 1) at h4
    have h5 := congrFun (hx.steinberg 0 2 1 (by decide) (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h5
    change ((((x 0 2 (ix 5)) + 0) + x 2 1 (ix 5)) + (((x 0 2 (ix 9)) + (x 0 2 (ix 8))) + x 2 1 (ix 9))) + x 0 2 (ix 5) = ((x 0 1 (ix 5)) + 0) + x 2 1 (ix 5) at h5
    have h6 := congrFun (hx.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h6
    change ((x 1 4 (ix 0)) + (x 1 4 (ix 6))) + x 0 3 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 4))) + x 1 4 (ix 0) at h6
    have h7 := congrFun (hx.commute 1 0 2 0 (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h7
    change ((x 2 0 (ix 8)) + (x 2 0 (ix 5))) + x 1 0 (ix 8) = ((x 1 0 (ix 8)) + 0) + x 2 0 (ix 8) at h7
    have h8 := congrFun (hx.commute 2 0 2 4 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h8
    change ((x 2 4 (ix 6)) + (x 2 4 (ix 1))) + x 2 0 (ix 6) = ((x 2 0 (ix 6)) + (x 2 0 (ix 8))) + x 2 4 (ix 6) at h8
    have h9 := congrFun (hx.steinberg 2 0 1 (by decide) (by decide) (by decide)) (ix 9)
    simp only [Pi.add_apply, action_coords] at h9
    change ((((x 2 0 (ix 9)) + 0) + x 0 1 (ix 9)) + (((x 2 0 (ix 5)) + (x 2 0 (ix 8))) + x 0 1 (ix 5))) + x 2 0 (ix 9) = ((x 2 1 (ix 9)) + 0) + x 0 1 (ix 9) at h9
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8 + h9
  · change ((x 2 0 (ix 7)) + 0) - (x 2 0 (ix 7)) = x 2 4 (ix 2)
    have h0 := congrFun (hx.commute 2 0 2 4 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 4 (ix 7)) + (x 2 4 (ix 2))) + x 2 0 (ix 7) = ((x 2 0 (ix 7)) + 0) + x 2 4 (ix 7) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 6)) + (x 1 0 (ix 8))) - (x 1 0 (ix 6)) = x 2 4 (ix 3)
    have h0 := congrFun (hx.commute 1 0 2 4 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 4 (ix 6)) + (x 2 4 (ix 3))) + x 1 0 (ix 6) = ((x 1 0 (ix 6)) + (x 1 0 (ix 8))) + x 2 4 (ix 6) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 7)) + 0) - (x 1 0 (ix 7)) = x 2 4 (ix 4)
    have h0 := congrFun (hx.commute 1 0 2 4 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 4 (ix 7)) + (x 2 4 (ix 4))) + x 1 0 (ix 7) = ((x 1 0 (ix 7)) + 0) + x 2 4 (ix 7) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 8)) + 0) - (x 1 0 (ix 8)) = x 2 4 (ix 5)
    have h0 := congrFun (hx.commute 1 0 2 4 (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 4 (ix 8)) + (x 2 4 (ix 5))) + x 1 0 (ix 8) = ((x 1 0 (ix 8)) + 0) + x 2 4 (ix 8) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 3)) + (x 0 1 (ix 5))) - (x 0 1 (ix 3)) = x 2 4 (ix 6)
    have h0 := congrFun (hx.commute 0 1 2 4 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 4 (ix 3)) + (x 2 4 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + (x 0 1 (ix 5))) + x 2 4 (ix 3) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 4)) + 0) - (x 0 1 (ix 4)) = x 2 4 (ix 7)
    have h0 := congrFun (hx.commute 0 1 2 4 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 4 (ix 4)) + (x 2 4 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + 0) + x 2 4 (ix 4) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 5)) + 0) - (x 0 1 (ix 5)) = x 2 4 (ix 8)
    have h0 := congrFun (hx.commute 0 1 2 4 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 4 (ix 5)) + (x 2 4 (ix 8))) + x 0 1 (ix 5) = ((x 0 1 (ix 5)) + 0) + x 2 4 (ix 5) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 2 (ix 5)) + 0) - (x 0 2 (ix 5)) = x 2 4 (ix 9)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.commute 0 1 0 2 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 0 2 (ix 3)) + (x 0 2 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + 0) + x 0 2 (ix 3) at h1
    have h2 := congrFun (hx.commute 0 1 2 4 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 2 4 (ix 3)) + (x 2 4 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + (x 0 1 (ix 5))) + x 2 4 (ix 3) at h2
    have h3 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h3
    change ((((x 0 1 (ix 8)) + (x 0 1 (ix 9))) + x 1 2 (ix 8)) + 0) + x 0 1 (ix 8) = ((x 0 2 (ix 8)) + (x 0 2 (ix 9))) + x 1 2 (ix 8) at h3
    have h4 := congrFun (hx.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h4
    change ((((x 0 1 (ix 4)) + 0) + x 1 3 (ix 4)) + (((x 0 1 (ix 7)) + (x 0 1 (ix 9))) + x 1 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 3 (ix 4)) + 0) + x 1 3 (ix 4) at h4
    have h5 := congrFun (hx.steinberg 0 1 4 (by decide) (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h5
    change ((((x 0 1 (ix 1)) + (x 0 1 (ix 5))) + x 1 4 (ix 1)) + 0) + x 0 1 (ix 1) = ((x 0 4 (ix 1)) + (x 0 4 (ix 5))) + x 1 4 (ix 1) at h5
    have h6 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h6
    change ((x 1 3 (ix 2)) + (x 1 3 (ix 7))) + x 0 2 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 5))) + x 1 3 (ix 2) at h6
    have h7 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h7
    change ((x 1 4 (ix 1)) + (x 1 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 5))) + x 1 4 (ix 1) at h7
    have h8 := congrFun (hx.steinberg 0 2 4 (by decide) (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h8
    change ((((x 0 2 (ix 1)) + 0) + x 2 4 (ix 1)) + (((x 0 2 (ix 6)) + (x 0 2 (ix 8))) + x 2 4 (ix 6))) + x 0 2 (ix 1) = ((x 0 4 (ix 1)) + 0) + x 2 4 (ix 1) at h8
    have h9 := congrFun (hx.steinberg 0 2 4 (by decide) (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h9
    change ((((x 0 2 (ix 5)) + 0) + x 2 4 (ix 5)) + (((x 0 2 (ix 9)) + 0) + x 2 4 (ix 9))) + x 0 2 (ix 5) = ((x 0 4 (ix 5)) + 0) + x 2 4 (ix 5) at h9
    have h10 := congrFun (hx.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h10
    change ((x 1 4 (ix 0)) + (x 1 4 (ix 6))) + x 0 3 (ix 0) = ((x 0 3 (ix 0)) + (x 0 3 (ix 4))) + x 1 4 (ix 0) at h10
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8 + h9 + h10

private theorem exact_3_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 3)
    (hx : ElementaryRelations 3 x) (s : Fin 10) :
    act 3 0 (witness x) s - witness x s = x 3 0 (ix s) := by
  fin_cases s
  · change ((x 3 0 (ix 6)) + 0) - (x 3 0 (ix 6)) = x 3 0 (ix 0)
    have h0 := congrFun (hx.square 3 0) (ix 6)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 3 0 (ix 6)) + (x 3 0 (ix 0))) + x 3 0 (ix 6) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 6)) + 0) - (x 2 0 (ix 6)) = x 3 0 (ix 1)
    have h0 := congrFun (hx.commute 2 0 3 0 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 0 (ix 6)) + (x 3 0 (ix 1))) + x 2 0 (ix 6) = ((x 2 0 (ix 6)) + (x 2 0 (ix 0))) + x 3 0 (ix 6) at h0
    have h1 := congrFun (hx.commute 2 0 3 1 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 3 1 (ix 3)) + 0) + x 2 0 (ix 3) = ((x 2 0 (ix 3)) + (x 2 0 (ix 0))) + x 3 1 (ix 3) at h1
    linear_combination (norm := (ring_nf; simp)) h0 + h1
  · change ((x 2 0 (ix 7)) + 0) - (x 2 0 (ix 7)) = x 3 0 (ix 2)
    have h0 := congrFun (hx.commute 2 0 3 0 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 0 (ix 7)) + (x 3 0 (ix 2))) + x 2 0 (ix 7) = ((x 2 0 (ix 7)) + 0) + x 3 0 (ix 7) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 6)) + 0) - (x 1 0 (ix 6)) = x 3 0 (ix 3)
    have h0 := congrFun (hx.commute 1 0 3 0 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 0 (ix 6)) + (x 3 0 (ix 3))) + x 1 0 (ix 6) = ((x 1 0 (ix 6)) + (x 1 0 (ix 0))) + x 3 0 (ix 6) at h0
    have h1 := congrFun (hx.commute 1 0 3 2 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 3 2 (ix 1)) + 0) + x 1 0 (ix 1) = ((x 1 0 (ix 1)) + (x 1 0 (ix 0))) + x 3 2 (ix 1) at h1
    linear_combination (norm := (ring_nf; simp)) h0 + h1
  · change ((x 1 0 (ix 7)) + 0) - (x 1 0 (ix 7)) = x 3 0 (ix 4)
    have h0 := congrFun (hx.commute 1 0 3 0 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 0 (ix 7)) + (x 3 0 (ix 4))) + x 1 0 (ix 7) = ((x 1 0 (ix 7)) + 0) + x 3 0 (ix 7) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 8)) + 0) - (x 1 0 (ix 8)) = x 3 0 (ix 5)
    have h0 := congrFun (hx.commute 1 0 2 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 4 (ix 0)) + 0) + x 1 0 (ix 0) = ((x 1 0 (ix 0)) + (x 1 0 (ix 2))) + x 2 4 (ix 0) at h0
    have h1 := congrFun (hx.commute 1 0 3 0 (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 3 0 (ix 8)) + (x 3 0 (ix 5))) + x 1 0 (ix 8) = ((x 1 0 (ix 8)) + (x 1 0 (ix 2))) + x 3 0 (ix 8) at h1
    linear_combination (norm := (ring_nf; simp)) h0 + h1
  · change ((x 0 1 (ix 3)) + (x 3 0 (ix 6))) - (x 0 1 (ix 3)) = x 3 0 (ix 6)
    ring
  · change ((x 0 1 (ix 4)) + 0) - (x 0 1 (ix 4)) = x 3 0 (ix 7)
    have h0 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h0
    change ((((x 0 1 (ix 2)) + (x 0 1 (ix 4))) + x 1 2 (ix 2)) + 0) + x 0 1 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 4))) + x 1 2 (ix 2) at h0
    have h1 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 1 4 (ix 0)) + 0) + x 0 2 (ix 0) = ((x 0 2 (ix 0)) + (x 0 2 (ix 4))) + x 1 4 (ix 0) at h1
    have h2 := congrFun (hx.commute 0 2 3 1 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 3 1 (ix 5)) + (x 3 1 (ix 9))) + x 0 2 (ix 5) = ((x 0 2 (ix 5)) + (x 0 2 (ix 2))) + x 3 1 (ix 5) at h2
    have h3 := congrFun (hx.commute 1 0 3 0 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 3 0 (ix 7)) + (x 3 0 (ix 4))) + x 1 0 (ix 7) = ((x 1 0 (ix 7)) + 0) + x 3 0 (ix 7) at h3
    have h4 := congrFun (hx.steinberg 3 0 1 (by decide) (by decide) (by decide)) (ix 9)
    simp only [Pi.add_apply, action_coords] at h4
    change ((((x 3 0 (ix 9)) + 0) + x 0 1 (ix 9)) + (((x 3 0 (ix 4)) + (x 3 0 (ix 7))) + x 0 1 (ix 4))) + x 3 0 (ix 9) = ((x 3 1 (ix 9)) + 0) + x 0 1 (ix 9) at h4
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4
  · change ((x 0 1 (ix 5)) + (x 2 0 (ix 7))) - (x 0 1 (ix 5)) = x 3 0 (ix 8)
    have h0 := congrFun (hx.commute 0 1 2 1 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 1 (ix 4)) + (x 2 1 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + (x 0 1 (ix 2))) + x 2 1 (ix 4) at h0
    have h1 := congrFun (hx.commute 0 1 2 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 2 4 (ix 0)) + 0) + x 0 1 (ix 0) = ((x 0 1 (ix 0)) + (x 0 1 (ix 2))) + x 2 4 (ix 0) at h1
    have h2 := congrFun (hx.steinberg 2 0 1 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h2
    change ((((x 2 0 (ix 4)) + (x 2 0 (ix 7))) + x 0 1 (ix 4)) + 0) + x 2 0 (ix 4) = ((x 2 1 (ix 4)) + (x 2 1 (ix 7))) + x 0 1 (ix 4) at h2
    have h3 := congrFun (hx.commute 2 1 3 0 (by decide) (by decide)) (ix 9)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 3 0 (ix 9)) + (x 3 0 (ix 8))) + x 2 1 (ix 9) = ((x 2 1 (ix 9)) + (x 2 1 (ix 4))) + x 3 0 (ix 9) at h3
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3
  · change ((x 0 2 (ix 5)) + (x 1 0 (ix 7))) - (x 0 2 (ix 5)) = x 3 0 (ix 9)
    have h0 := congrFun (hx.square 0 1) (ix 4)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 4)) + (x 0 1 (ix 7))) + x 0 1 (ix 4) = 0 at h0
    have h1 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h1
    change ((((x 0 1 (ix 4)) + 0) + x 1 2 (ix 4)) + (((x 0 1 (ix 7)) + 0) + x 1 2 (ix 7))) + x 0 1 (ix 4) = ((x 0 2 (ix 4)) + 0) + x 1 2 (ix 4) at h1
    have h2 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 1 4 (ix 0)) + 0) + x 0 2 (ix 0) = ((x 0 2 (ix 0)) + (x 0 2 (ix 4))) + x 1 4 (ix 0) at h2
    have h3 := congrFun (hx.steinberg 1 0 2 (by decide) (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h3
    change ((((x 1 0 (ix 2)) + (x 1 0 (ix 7))) + x 0 2 (ix 2)) + 0) + x 1 0 (ix 2) = ((x 1 2 (ix 2)) + (x 1 2 (ix 7))) + x 0 2 (ix 2) at h3
    have h4 := congrFun (hx.commute 1 2 3 0 (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 3 0 (ix 8)) + (x 3 0 (ix 9))) + x 1 2 (ix 8) = ((x 1 2 (ix 8)) + (x 1 2 (ix 2))) + x 3 0 (ix 8) at h4
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4

private theorem exact_3_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 3)
    (hx : ElementaryRelations 3 x) (s : Fin 10) :
    act 3 1 (witness x) s - witness x s = x 3 1 (ix s) := by
  fin_cases s
  · change ((x 3 0 (ix 6)) + 0) - (x 3 0 (ix 6)) = x 3 1 (ix 0)
    have h0 := congrFun (hx.commute 3 0 3 1 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 1 (ix 6)) + (x 3 1 (ix 0))) + x 3 0 (ix 6) = ((x 3 0 (ix 6)) + 0) + x 3 1 (ix 6) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 6)) + 0) - (x 2 0 (ix 6)) = x 3 1 (ix 1)
    have h0 := congrFun (hx.commute 2 0 3 1 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 1 (ix 6)) + (x 3 1 (ix 1))) + x 2 0 (ix 6) = ((x 2 0 (ix 6)) + 0) + x 3 1 (ix 6) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 7)) + 0) - (x 2 0 (ix 7)) = x 3 1 (ix 2)
    have h0 := congrFun (hx.commute 2 0 3 1 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 1 (ix 7)) + (x 3 1 (ix 2))) + x 2 0 (ix 7) = ((x 2 0 (ix 7)) + 0) + x 3 1 (ix 7) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 6)) + (x 3 0 (ix 6))) - (x 1 0 (ix 6)) = x 3 1 (ix 3)
    have h0 := congrFun (hx.commute 0 1 3 1 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 1 (ix 3)) + (x 3 1 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + (x 0 1 (ix 0))) + x 3 1 (ix 3) at h0
    have h1 := congrFun (hx.commute 0 1 3 2 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 3 2 (ix 1)) + 0) + x 0 1 (ix 1) = ((x 0 1 (ix 1)) + (x 0 1 (ix 0))) + x 3 2 (ix 1) at h1
    have h2 := congrFun (hx.steinberg 3 0 1 (by decide) (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h2
    change ((((x 3 0 (ix 3)) + (x 3 0 (ix 6))) + x 0 1 (ix 3)) + 0) + x 3 0 (ix 3) = ((x 3 1 (ix 3)) + (x 3 1 (ix 6))) + x 0 1 (ix 3) at h2
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2
  · change ((x 1 0 (ix 7)) + 0) - (x 1 0 (ix 7)) = x 3 1 (ix 4)
    have h0 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h0
    change ((((x 0 1 (ix 2)) + (x 0 1 (ix 4))) + x 1 2 (ix 2)) + 0) + x 0 1 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 4))) + x 1 2 (ix 2) at h0
    have h1 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 1 4 (ix 0)) + 0) + x 0 2 (ix 0) = ((x 0 2 (ix 0)) + (x 0 2 (ix 4))) + x 1 4 (ix 0) at h1
    have h2 := congrFun (hx.commute 0 2 3 1 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 3 1 (ix 5)) + (x 3 1 (ix 9))) + x 0 2 (ix 5) = ((x 0 2 (ix 5)) + (x 0 2 (ix 2))) + x 3 1 (ix 5) at h2
    have h3 := congrFun (hx.commute 1 0 3 0 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 3 0 (ix 7)) + (x 3 0 (ix 4))) + x 1 0 (ix 7) = ((x 1 0 (ix 7)) + 0) + x 3 0 (ix 7) at h3
    have h4 := congrFun (hx.commute 3 0 3 1 (by decide) (by decide)) (ix 9)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 3 1 (ix 9)) + (x 3 1 (ix 4))) + x 3 0 (ix 9) = ((x 3 0 (ix 9)) + (x 3 0 (ix 7))) + x 3 1 (ix 9) at h4
    have h5 := congrFun (hx.steinberg 3 0 1 (by decide) (by decide) (by decide)) (ix 9)
    simp only [Pi.add_apply, action_coords] at h5
    change ((((x 3 0 (ix 9)) + 0) + x 0 1 (ix 9)) + (((x 3 0 (ix 4)) + (x 3 0 (ix 7))) + x 0 1 (ix 4))) + x 3 0 (ix 9) = ((x 3 1 (ix 9)) + 0) + x 0 1 (ix 9) at h5
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5
  · change ((x 1 0 (ix 8)) + (x 2 0 (ix 7))) - (x 1 0 (ix 8)) = x 3 1 (ix 5)
    have h0 := congrFun (hx.commute 2 0 3 1 (by decide) (by decide)) (ix 9)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 1 (ix 9)) + (x 3 1 (ix 5))) + x 2 0 (ix 9) = ((x 2 0 (ix 9)) + (x 2 0 (ix 7))) + x 3 1 (ix 9) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 3)) + 0) - (x 0 1 (ix 3)) = x 3 1 (ix 6)
    have h0 := congrFun (hx.commute 0 1 3 1 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 1 (ix 3)) + (x 3 1 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + (x 0 1 (ix 0))) + x 3 1 (ix 3) at h0
    have h1 := congrFun (hx.commute 0 1 3 2 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 3 2 (ix 1)) + 0) + x 0 1 (ix 1) = ((x 0 1 (ix 1)) + (x 0 1 (ix 0))) + x 3 2 (ix 1) at h1
    linear_combination (norm := (ring_nf; simp)) h0 + h1
  · change ((x 0 1 (ix 4)) + 0) - (x 0 1 (ix 4)) = x 3 1 (ix 7)
    have h0 := congrFun (hx.commute 0 1 3 1 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 1 (ix 4)) + (x 3 1 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + 0) + x 3 1 (ix 4) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 5)) + 0) - (x 0 1 (ix 5)) = x 3 1 (ix 8)
    have h0 := congrFun (hx.commute 0 1 2 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 4 (ix 0)) + 0) + x 0 1 (ix 0) = ((x 0 1 (ix 0)) + (x 0 1 (ix 2))) + x 2 4 (ix 0) at h0
    have h1 := congrFun (hx.commute 0 1 3 1 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 3 1 (ix 5)) + (x 3 1 (ix 8))) + x 0 1 (ix 5) = ((x 0 1 (ix 5)) + (x 0 1 (ix 2))) + x 3 1 (ix 5) at h1
    linear_combination (norm := (ring_nf; simp)) h0 + h1
  · change ((x 0 2 (ix 5)) + (x 0 1 (ix 4))) - (x 0 2 (ix 5)) = x 3 1 (ix 9)
    have h0 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h0
    change ((((x 0 1 (ix 2)) + (x 0 1 (ix 4))) + x 1 2 (ix 2)) + 0) + x 0 1 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 4))) + x 1 2 (ix 2) at h0
    have h1 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 1 4 (ix 0)) + 0) + x 0 2 (ix 0) = ((x 0 2 (ix 0)) + (x 0 2 (ix 4))) + x 1 4 (ix 0) at h1
    have h2 := congrFun (hx.commute 0 2 3 1 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 3 1 (ix 5)) + (x 3 1 (ix 9))) + x 0 2 (ix 5) = ((x 0 2 (ix 5)) + (x 0 2 (ix 2))) + x 3 1 (ix 5) at h2
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2

private theorem exact_3_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 3)
    (hx : ElementaryRelations 3 x) (s : Fin 10) :
    act 3 2 (witness x) s - witness x s = x 3 2 (ix s) := by
  fin_cases s
  · change ((x 3 0 (ix 6)) + 0) - (x 3 0 (ix 6)) = x 3 2 (ix 0)
    have h0 := congrFun (hx.commute 3 0 3 2 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 2 (ix 6)) + (x 3 2 (ix 0))) + x 3 0 (ix 6) = ((x 3 0 (ix 6)) + 0) + x 3 2 (ix 6) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 6)) + (x 3 0 (ix 6))) - (x 2 0 (ix 6)) = x 3 2 (ix 1)
    have h0 := congrFun (hx.commute 0 1 3 2 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 2 (ix 3)) + (x 3 2 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + 0) + x 3 2 (ix 3) at h0
    have h1 := congrFun (hx.steinberg 3 0 2 (by decide) (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h1
    change ((((x 3 0 (ix 1)) + (x 3 0 (ix 6))) + x 0 2 (ix 1)) + 0) + x 3 0 (ix 1) = ((x 3 2 (ix 1)) + (x 3 2 (ix 6))) + x 0 2 (ix 1) at h1
    linear_combination (norm := (ring_nf; simp)) h0 + h1
  · change ((x 2 0 (ix 7)) + 0) - (x 2 0 (ix 7)) = x 3 2 (ix 2)
    have h0 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h0
    change ((((x 0 1 (ix 2)) + (x 0 1 (ix 4))) + x 1 2 (ix 2)) + 0) + x 0 1 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 4))) + x 1 2 (ix 2) at h0
    have h1 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 1 4 (ix 0)) + 0) + x 0 2 (ix 0) = ((x 0 2 (ix 0)) + (x 0 2 (ix 4))) + x 1 4 (ix 0) at h1
    have h2 := congrFun (hx.commute 0 2 3 1 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 3 1 (ix 5)) + (x 3 1 (ix 9))) + x 0 2 (ix 5) = ((x 0 2 (ix 5)) + (x 0 2 (ix 2))) + x 3 1 (ix 5) at h2
    have h3 := congrFun (hx.commute 1 0 3 0 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 3 0 (ix 7)) + (x 3 0 (ix 4))) + x 1 0 (ix 7) = ((x 1 0 (ix 7)) + 0) + x 3 0 (ix 7) at h3
    have h4 := congrFun (hx.commute 3 0 3 2 (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 3 2 (ix 8)) + (x 3 2 (ix 2))) + x 3 0 (ix 8) = ((x 3 0 (ix 8)) + (x 3 0 (ix 7))) + x 3 2 (ix 8) at h4
    have h5 := congrFun (hx.steinberg 3 0 1 (by decide) (by decide) (by decide)) (ix 9)
    simp only [Pi.add_apply, action_coords] at h5
    change ((((x 3 0 (ix 9)) + 0) + x 0 1 (ix 9)) + (((x 3 0 (ix 4)) + (x 3 0 (ix 7))) + x 0 1 (ix 4))) + x 3 0 (ix 9) = ((x 3 1 (ix 9)) + 0) + x 0 1 (ix 9) at h5
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5
  · change ((x 1 0 (ix 6)) + 0) - (x 1 0 (ix 6)) = x 3 2 (ix 3)
    have h0 := congrFun (hx.commute 1 0 3 2 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 2 (ix 6)) + (x 3 2 (ix 3))) + x 1 0 (ix 6) = ((x 1 0 (ix 6)) + 0) + x 3 2 (ix 6) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 7)) + 0) - (x 1 0 (ix 7)) = x 3 2 (ix 4)
    have h0 := congrFun (hx.commute 1 0 3 2 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 2 (ix 7)) + (x 3 2 (ix 4))) + x 1 0 (ix 7) = ((x 1 0 (ix 7)) + 0) + x 3 2 (ix 7) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 8)) + (x 1 0 (ix 7))) - (x 1 0 (ix 8)) = x 3 2 (ix 5)
    have h0 := congrFun (hx.commute 1 0 3 2 (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 2 (ix 8)) + (x 3 2 (ix 5))) + x 1 0 (ix 8) = ((x 1 0 (ix 8)) + (x 1 0 (ix 7))) + x 3 2 (ix 8) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 3)) + 0) - (x 0 1 (ix 3)) = x 3 2 (ix 6)
    have h0 := congrFun (hx.commute 0 1 3 2 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 2 (ix 3)) + (x 3 2 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + 0) + x 3 2 (ix 3) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 4)) + 0) - (x 0 1 (ix 4)) = x 3 2 (ix 7)
    have h0 := congrFun (hx.commute 0 1 3 2 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 2 (ix 4)) + (x 3 2 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + 0) + x 3 2 (ix 4) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 5)) + (x 0 1 (ix 4))) - (x 0 1 (ix 5)) = x 3 2 (ix 8)
    have h0 := congrFun (hx.commute 0 1 3 2 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 2 (ix 5)) + (x 3 2 (ix 8))) + x 0 1 (ix 5) = ((x 0 1 (ix 5)) + (x 0 1 (ix 4))) + x 3 2 (ix 5) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 2 (ix 5)) + 0) - (x 0 2 (ix 5)) = x 3 2 (ix 9)
    have h0 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 1 4 (ix 0)) + 0) + x 0 2 (ix 0) = ((x 0 2 (ix 0)) + (x 0 2 (ix 4))) + x 1 4 (ix 0) at h0
    have h1 := congrFun (hx.commute 0 2 3 2 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 3 2 (ix 5)) + (x 3 2 (ix 9))) + x 0 2 (ix 5) = ((x 0 2 (ix 5)) + (x 0 2 (ix 4))) + x 3 2 (ix 5) at h1
    linear_combination (norm := (ring_nf; simp)) h0 + h1

private theorem exact_3_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 3)
    (hx : ElementaryRelations 3 x) (s : Fin 10) :
    act 3 3 (witness x) s - witness x s = x 3 3 (ix s) := by
  fin_cases s
  · change ((x 3 0 (ix 6)) + 0) - (x 3 0 (ix 6)) = x 3 3 (ix 0)
    have h0 := congrFun (hx.diagonal 3) (ix 0)
    change x 3 3 (ix 0) = 0 at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 6)) + 0) - (x 2 0 (ix 6)) = x 3 3 (ix 1)
    have h0 := congrFun (hx.commute 2 0 3 3 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 3 (ix 6)) + (x 3 3 (ix 1))) + x 2 0 (ix 6) = ((x 2 0 (ix 6)) + 0) + x 3 3 (ix 6) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 7)) + 0) - (x 2 0 (ix 7)) = x 3 3 (ix 2)
    have h0 := congrFun (hx.commute 2 0 3 3 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 3 (ix 7)) + (x 3 3 (ix 2))) + x 2 0 (ix 7) = ((x 2 0 (ix 7)) + 0) + x 3 3 (ix 7) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 6)) + 0) - (x 1 0 (ix 6)) = x 3 3 (ix 3)
    have h0 := congrFun (hx.commute 1 0 3 3 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 3 (ix 6)) + (x 3 3 (ix 3))) + x 1 0 (ix 6) = ((x 1 0 (ix 6)) + 0) + x 3 3 (ix 6) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 7)) + 0) - (x 1 0 (ix 7)) = x 3 3 (ix 4)
    have h0 := congrFun (hx.commute 1 0 3 3 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 3 (ix 7)) + (x 3 3 (ix 4))) + x 1 0 (ix 7) = ((x 1 0 (ix 7)) + 0) + x 3 3 (ix 7) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 8)) + 0) - (x 1 0 (ix 8)) = x 3 3 (ix 5)
    have h0 := congrFun (hx.commute 1 0 3 3 (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 3 (ix 8)) + (x 3 3 (ix 5))) + x 1 0 (ix 8) = ((x 1 0 (ix 8)) + 0) + x 3 3 (ix 8) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 3)) + 0) - (x 0 1 (ix 3)) = x 3 3 (ix 6)
    have h0 := congrFun (hx.commute 0 1 3 3 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 3 (ix 3)) + (x 3 3 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + 0) + x 3 3 (ix 3) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 4)) + 0) - (x 0 1 (ix 4)) = x 3 3 (ix 7)
    have h0 := congrFun (hx.commute 0 1 3 3 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 3 (ix 4)) + (x 3 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + 0) + x 3 3 (ix 4) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 5)) + 0) - (x 0 1 (ix 5)) = x 3 3 (ix 8)
    have h0 := congrFun (hx.commute 0 1 3 3 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 3 (ix 5)) + (x 3 3 (ix 8))) + x 0 1 (ix 5) = ((x 0 1 (ix 5)) + 0) + x 3 3 (ix 5) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 2 (ix 5)) + 0) - (x 0 2 (ix 5)) = x 3 3 (ix 9)
    have h0 := congrFun (hx.commute 0 2 3 3 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 3 (ix 5)) + (x 3 3 (ix 9))) + x 0 2 (ix 5) = ((x 0 2 (ix 5)) + 0) + x 3 3 (ix 5) at h0
    linear_combination (norm := (ring_nf; simp)) h0

private theorem exact_3_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 3)
    (hx : ElementaryRelations 3 x) (s : Fin 10) :
    act 3 4 (witness x) s - witness x s = x 3 4 (ix s) := by
  fin_cases s
  · change ((x 3 0 (ix 6)) + 0) - (x 3 0 (ix 6)) = x 3 4 (ix 0)
    have h0 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 2)
    simp only [Pi.add_apply, action_coords] at h0
    change ((((x 0 1 (ix 2)) + (x 0 1 (ix 4))) + x 1 2 (ix 2)) + 0) + x 0 1 (ix 2) = ((x 0 2 (ix 2)) + (x 0 2 (ix 4))) + x 1 2 (ix 2) at h0
    have h1 := congrFun (hx.commute 0 2 1 4 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 1 4 (ix 0)) + 0) + x 0 2 (ix 0) = ((x 0 2 (ix 0)) + (x 0 2 (ix 4))) + x 1 4 (ix 0) at h1
    have h2 := congrFun (hx.commute 0 2 3 1 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 3 1 (ix 5)) + (x 3 1 (ix 9))) + x 0 2 (ix 5) = ((x 0 2 (ix 5)) + (x 0 2 (ix 2))) + x 3 1 (ix 5) at h2
    have h3 := congrFun (hx.commute 1 0 3 0 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 3 0 (ix 7)) + (x 3 0 (ix 4))) + x 1 0 (ix 7) = ((x 1 0 (ix 7)) + 0) + x 3 0 (ix 7) at h3
    have h4 := congrFun (hx.commute 3 0 3 4 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 3 4 (ix 6)) + (x 3 4 (ix 0))) + x 3 0 (ix 6) = ((x 3 0 (ix 6)) + (x 3 0 (ix 7))) + x 3 4 (ix 6) at h4
    have h5 := congrFun (hx.steinberg 3 0 1 (by decide) (by decide) (by decide)) (ix 9)
    simp only [Pi.add_apply, action_coords] at h5
    change ((((x 3 0 (ix 9)) + 0) + x 0 1 (ix 9)) + (((x 3 0 (ix 4)) + (x 3 0 (ix 7))) + x 0 1 (ix 4))) + x 3 0 (ix 9) = ((x 3 1 (ix 9)) + 0) + x 0 1 (ix 9) at h5
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5
  · change ((x 2 0 (ix 6)) + (x 2 0 (ix 7))) - (x 2 0 (ix 6)) = x 3 4 (ix 1)
    have h0 := congrFun (hx.commute 2 0 3 4 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 4 (ix 6)) + (x 3 4 (ix 1))) + x 2 0 (ix 6) = ((x 2 0 (ix 6)) + (x 2 0 (ix 7))) + x 3 4 (ix 6) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 7)) + 0) - (x 2 0 (ix 7)) = x 3 4 (ix 2)
    have h0 := congrFun (hx.commute 2 0 3 4 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 4 (ix 7)) + (x 3 4 (ix 2))) + x 2 0 (ix 7) = ((x 2 0 (ix 7)) + 0) + x 3 4 (ix 7) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 6)) + (x 1 0 (ix 7))) - (x 1 0 (ix 6)) = x 3 4 (ix 3)
    have h0 := congrFun (hx.commute 1 0 3 4 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 4 (ix 6)) + (x 3 4 (ix 3))) + x 1 0 (ix 6) = ((x 1 0 (ix 6)) + (x 1 0 (ix 7))) + x 3 4 (ix 6) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 7)) + 0) - (x 1 0 (ix 7)) = x 3 4 (ix 4)
    have h0 := congrFun (hx.commute 1 0 3 4 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 4 (ix 7)) + (x 3 4 (ix 4))) + x 1 0 (ix 7) = ((x 1 0 (ix 7)) + 0) + x 3 4 (ix 7) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 8)) + 0) - (x 1 0 (ix 8)) = x 3 4 (ix 5)
    have h0 := congrFun (hx.commute 1 0 3 4 (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 4 (ix 8)) + (x 3 4 (ix 5))) + x 1 0 (ix 8) = ((x 1 0 (ix 8)) + 0) + x 3 4 (ix 8) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 3)) + (x 0 1 (ix 4))) - (x 0 1 (ix 3)) = x 3 4 (ix 6)
    have h0 := congrFun (hx.commute 0 1 3 4 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 4 (ix 3)) + (x 3 4 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + (x 0 1 (ix 4))) + x 3 4 (ix 3) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 4)) + 0) - (x 0 1 (ix 4)) = x 3 4 (ix 7)
    have h0 := congrFun (hx.commute 0 1 3 4 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 4 (ix 4)) + (x 3 4 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + 0) + x 3 4 (ix 4) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 5)) + 0) - (x 0 1 (ix 5)) = x 3 4 (ix 8)
    have h0 := congrFun (hx.commute 0 1 3 4 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 4 (ix 5)) + (x 3 4 (ix 8))) + x 0 1 (ix 5) = ((x 0 1 (ix 5)) + 0) + x 3 4 (ix 5) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 2 (ix 5)) + 0) - (x 0 2 (ix 5)) = x 3 4 (ix 9)
    have h0 := congrFun (hx.commute 0 2 3 4 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 4 (ix 5)) + (x 3 4 (ix 9))) + x 0 2 (ix 5) = ((x 0 2 (ix 5)) + 0) + x 3 4 (ix 5) at h0
    linear_combination (norm := (ring_nf; simp)) h0

private theorem exact_4_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 3)
    (hx : ElementaryRelations 3 x) (s : Fin 10) :
    act 4 0 (witness x) s - witness x s = x 4 0 (ix s) := by
  fin_cases s
  · change ((x 3 0 (ix 6)) + 0) - (x 3 0 (ix 6)) = x 4 0 (ix 0)
    have h0 := congrFun (hx.commute 3 0 4 0 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 0 (ix 6)) + (x 4 0 (ix 0))) + x 3 0 (ix 6) = ((x 3 0 (ix 6)) + 0) + x 4 0 (ix 6) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 6)) + 0) - (x 2 0 (ix 6)) = x 4 0 (ix 1)
    have h0 := congrFun (hx.commute 2 0 4 0 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 0 (ix 6)) + (x 4 0 (ix 1))) + x 2 0 (ix 6) = ((x 2 0 (ix 6)) + 0) + x 4 0 (ix 6) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 7)) + 0) - (x 2 0 (ix 7)) = x 4 0 (ix 2)
    have h0 := congrFun (hx.commute 2 0 3 1 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 1 (ix 3)) + 0) + x 2 0 (ix 3) = ((x 2 0 (ix 3)) + (x 2 0 (ix 0))) + x 3 1 (ix 3) at h0
    have h1 := congrFun (hx.commute 2 0 4 0 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 4 0 (ix 7)) + (x 4 0 (ix 2))) + x 2 0 (ix 7) = ((x 2 0 (ix 7)) + (x 2 0 (ix 0))) + x 4 0 (ix 7) at h1
    linear_combination (norm := (ring_nf; simp)) h0 + h1
  · change ((x 1 0 (ix 6)) + 0) - (x 1 0 (ix 6)) = x 4 0 (ix 3)
    have h0 := congrFun (hx.commute 1 0 4 0 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 0 (ix 6)) + (x 4 0 (ix 3))) + x 1 0 (ix 6) = ((x 1 0 (ix 6)) + 0) + x 4 0 (ix 6) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 7)) + 0) - (x 1 0 (ix 7)) = x 4 0 (ix 4)
    have h0 := congrFun (hx.commute 1 0 3 2 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 2 (ix 1)) + 0) + x 1 0 (ix 1) = ((x 1 0 (ix 1)) + (x 1 0 (ix 0))) + x 3 2 (ix 1) at h0
    have h1 := congrFun (hx.commute 1 0 4 0 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 4 0 (ix 7)) + (x 4 0 (ix 4))) + x 1 0 (ix 7) = ((x 1 0 (ix 7)) + (x 1 0 (ix 0))) + x 4 0 (ix 7) at h1
    linear_combination (norm := (ring_nf; simp)) h0 + h1
  · change ((x 1 0 (ix 8)) + 0) - (x 1 0 (ix 8)) = x 4 0 (ix 5)
    have h0 := congrFun (hx.commute 1 0 2 3 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 3 (ix 0)) + 0) + x 1 0 (ix 0) = ((x 1 0 (ix 0)) + (x 1 0 (ix 1))) + x 2 3 (ix 0) at h0
    have h1 := congrFun (hx.commute 1 0 4 0 (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 4 0 (ix 8)) + (x 4 0 (ix 5))) + x 1 0 (ix 8) = ((x 1 0 (ix 8)) + (x 1 0 (ix 1))) + x 4 0 (ix 8) at h1
    linear_combination (norm := (ring_nf; simp)) h0 + h1
  · change ((x 0 1 (ix 3)) + 0) - (x 0 1 (ix 3)) = x 4 0 (ix 6)
    have h0 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h0
    change ((((x 0 1 (ix 1)) + (x 0 1 (ix 3))) + x 1 2 (ix 1)) + 0) + x 0 1 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 3))) + x 1 2 (ix 1) at h0
    have h1 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 1 3 (ix 0)) + 0) + x 0 2 (ix 0) = ((x 0 2 (ix 0)) + (x 0 2 (ix 3))) + x 1 3 (ix 0) at h1
    have h2 := congrFun (hx.commute 0 2 4 1 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 4 1 (ix 5)) + (x 4 1 (ix 9))) + x 0 2 (ix 5) = ((x 0 2 (ix 5)) + (x 0 2 (ix 1))) + x 4 1 (ix 5) at h2
    have h3 := congrFun (hx.commute 1 0 4 0 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 4 0 (ix 6)) + (x 4 0 (ix 3))) + x 1 0 (ix 6) = ((x 1 0 (ix 6)) + 0) + x 4 0 (ix 6) at h3
    have h4 := congrFun (hx.steinberg 4 0 1 (by decide) (by decide) (by decide)) (ix 9)
    simp only [Pi.add_apply, action_coords] at h4
    change ((((x 4 0 (ix 9)) + 0) + x 0 1 (ix 9)) + (((x 4 0 (ix 3)) + (x 4 0 (ix 6))) + x 0 1 (ix 3))) + x 4 0 (ix 9) = ((x 4 1 (ix 9)) + 0) + x 0 1 (ix 9) at h4
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4
  · change ((x 0 1 (ix 4)) + (x 3 0 (ix 6))) - (x 0 1 (ix 4)) = x 4 0 (ix 7)
    have h0 := congrFun (hx.commute 0 1 3 1 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 1 (ix 3)) + (x 3 1 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + (x 0 1 (ix 0))) + x 3 1 (ix 3) at h0
    have h1 := congrFun (hx.commute 0 1 3 2 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 3 2 (ix 1)) + 0) + x 0 1 (ix 1) = ((x 0 1 (ix 1)) + (x 0 1 (ix 0))) + x 3 2 (ix 1) at h1
    have h2 := congrFun (hx.steinberg 3 0 1 (by decide) (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h2
    change ((((x 3 0 (ix 3)) + (x 3 0 (ix 6))) + x 0 1 (ix 3)) + 0) + x 3 0 (ix 3) = ((x 3 1 (ix 3)) + (x 3 1 (ix 6))) + x 0 1 (ix 3) at h2
    have h3 := congrFun (hx.commute 3 1 4 0 (by decide) (by decide)) (ix 9)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 4 0 (ix 9)) + (x 4 0 (ix 7))) + x 3 1 (ix 9) = ((x 3 1 (ix 9)) + (x 3 1 (ix 3))) + x 4 0 (ix 9) at h3
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3
  · change ((x 0 1 (ix 5)) + (x 2 0 (ix 6))) - (x 0 1 (ix 5)) = x 4 0 (ix 8)
    have h0 := congrFun (hx.commute 0 1 2 1 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 1 (ix 3)) + (x 2 1 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + (x 0 1 (ix 1))) + x 2 1 (ix 3) at h0
    have h1 := congrFun (hx.commute 0 1 2 3 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 2 3 (ix 0)) + 0) + x 0 1 (ix 0) = ((x 0 1 (ix 0)) + (x 0 1 (ix 1))) + x 2 3 (ix 0) at h1
    have h2 := congrFun (hx.steinberg 2 0 1 (by decide) (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h2
    change ((((x 2 0 (ix 3)) + (x 2 0 (ix 6))) + x 0 1 (ix 3)) + 0) + x 2 0 (ix 3) = ((x 2 1 (ix 3)) + (x 2 1 (ix 6))) + x 0 1 (ix 3) at h2
    have h3 := congrFun (hx.commute 2 1 4 0 (by decide) (by decide)) (ix 9)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 4 0 (ix 9)) + (x 4 0 (ix 8))) + x 2 1 (ix 9) = ((x 2 1 (ix 9)) + (x 2 1 (ix 3))) + x 4 0 (ix 9) at h3
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3
  · change ((x 0 2 (ix 5)) + (x 1 0 (ix 6))) - (x 0 2 (ix 5)) = x 4 0 (ix 9)
    have h0 := congrFun (hx.square 0 1) (ix 3)
    simp only [Pi.add_apply, Pi.zero_apply, action_coords] at h0
    change ((x 0 1 (ix 3)) + (x 0 1 (ix 6))) + x 0 1 (ix 3) = 0 at h0
    have h1 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h1
    change ((((x 0 1 (ix 3)) + 0) + x 1 2 (ix 3)) + (((x 0 1 (ix 6)) + 0) + x 1 2 (ix 6))) + x 0 1 (ix 3) = ((x 0 2 (ix 3)) + 0) + x 1 2 (ix 3) at h1
    have h2 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 1 3 (ix 0)) + 0) + x 0 2 (ix 0) = ((x 0 2 (ix 0)) + (x 0 2 (ix 3))) + x 1 3 (ix 0) at h2
    have h3 := congrFun (hx.steinberg 1 0 2 (by decide) (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h3
    change ((((x 1 0 (ix 1)) + (x 1 0 (ix 6))) + x 0 2 (ix 1)) + 0) + x 1 0 (ix 1) = ((x 1 2 (ix 1)) + (x 1 2 (ix 6))) + x 0 2 (ix 1) at h3
    have h4 := congrFun (hx.commute 1 2 4 0 (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 4 0 (ix 8)) + (x 4 0 (ix 9))) + x 1 2 (ix 8) = ((x 1 2 (ix 8)) + (x 1 2 (ix 1))) + x 4 0 (ix 8) at h4
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4

private theorem exact_4_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 3)
    (hx : ElementaryRelations 3 x) (s : Fin 10) :
    act 4 1 (witness x) s - witness x s = x 4 1 (ix s) := by
  fin_cases s
  · change ((x 3 0 (ix 6)) + 0) - (x 3 0 (ix 6)) = x 4 1 (ix 0)
    have h0 := congrFun (hx.commute 3 0 4 1 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 1 (ix 6)) + (x 4 1 (ix 0))) + x 3 0 (ix 6) = ((x 3 0 (ix 6)) + 0) + x 4 1 (ix 6) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 6)) + 0) - (x 2 0 (ix 6)) = x 4 1 (ix 1)
    have h0 := congrFun (hx.commute 2 0 4 1 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 1 (ix 6)) + (x 4 1 (ix 1))) + x 2 0 (ix 6) = ((x 2 0 (ix 6)) + 0) + x 4 1 (ix 6) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 7)) + 0) - (x 2 0 (ix 7)) = x 4 1 (ix 2)
    have h0 := congrFun (hx.commute 2 0 4 1 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 1 (ix 7)) + (x 4 1 (ix 2))) + x 2 0 (ix 7) = ((x 2 0 (ix 7)) + 0) + x 4 1 (ix 7) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 6)) + 0) - (x 1 0 (ix 6)) = x 4 1 (ix 3)
    have h0 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h0
    change ((((x 0 1 (ix 1)) + (x 0 1 (ix 3))) + x 1 2 (ix 1)) + 0) + x 0 1 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 3))) + x 1 2 (ix 1) at h0
    have h1 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 1 3 (ix 0)) + 0) + x 0 2 (ix 0) = ((x 0 2 (ix 0)) + (x 0 2 (ix 3))) + x 1 3 (ix 0) at h1
    have h2 := congrFun (hx.commute 0 2 4 1 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 4 1 (ix 5)) + (x 4 1 (ix 9))) + x 0 2 (ix 5) = ((x 0 2 (ix 5)) + (x 0 2 (ix 1))) + x 4 1 (ix 5) at h2
    have h3 := congrFun (hx.commute 1 0 4 0 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 4 0 (ix 6)) + (x 4 0 (ix 3))) + x 1 0 (ix 6) = ((x 1 0 (ix 6)) + 0) + x 4 0 (ix 6) at h3
    have h4 := congrFun (hx.commute 4 0 4 1 (by decide) (by decide)) (ix 9)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 4 1 (ix 9)) + (x 4 1 (ix 3))) + x 4 0 (ix 9) = ((x 4 0 (ix 9)) + (x 4 0 (ix 6))) + x 4 1 (ix 9) at h4
    have h5 := congrFun (hx.steinberg 4 0 1 (by decide) (by decide) (by decide)) (ix 9)
    simp only [Pi.add_apply, action_coords] at h5
    change ((((x 4 0 (ix 9)) + 0) + x 0 1 (ix 9)) + (((x 4 0 (ix 3)) + (x 4 0 (ix 6))) + x 0 1 (ix 3))) + x 4 0 (ix 9) = ((x 4 1 (ix 9)) + 0) + x 0 1 (ix 9) at h5
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5
  · change ((x 1 0 (ix 7)) + (x 3 0 (ix 6))) - (x 1 0 (ix 7)) = x 4 1 (ix 4)
    have h0 := congrFun (hx.commute 3 0 4 1 (by decide) (by decide)) (ix 9)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 1 (ix 9)) + (x 4 1 (ix 4))) + x 3 0 (ix 9) = ((x 3 0 (ix 9)) + (x 3 0 (ix 6))) + x 4 1 (ix 9) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 8)) + (x 2 0 (ix 6))) - (x 1 0 (ix 8)) = x 4 1 (ix 5)
    have h0 := congrFun (hx.commute 2 0 4 1 (by decide) (by decide)) (ix 9)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 1 (ix 9)) + (x 4 1 (ix 5))) + x 2 0 (ix 9) = ((x 2 0 (ix 9)) + (x 2 0 (ix 6))) + x 4 1 (ix 9) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 3)) + 0) - (x 0 1 (ix 3)) = x 4 1 (ix 6)
    have h0 := congrFun (hx.commute 0 1 4 1 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 1 (ix 3)) + (x 4 1 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + 0) + x 4 1 (ix 3) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 4)) + 0) - (x 0 1 (ix 4)) = x 4 1 (ix 7)
    have h0 := congrFun (hx.commute 0 1 3 2 (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 3 2 (ix 1)) + 0) + x 0 1 (ix 1) = ((x 0 1 (ix 1)) + (x 0 1 (ix 0))) + x 3 2 (ix 1) at h0
    have h1 := congrFun (hx.commute 0 1 4 1 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 4 1 (ix 4)) + (x 4 1 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + (x 0 1 (ix 0))) + x 4 1 (ix 4) at h1
    linear_combination (norm := (ring_nf; simp)) h0 + h1
  · change ((x 0 1 (ix 5)) + 0) - (x 0 1 (ix 5)) = x 4 1 (ix 8)
    have h0 := congrFun (hx.commute 0 1 2 3 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 2 3 (ix 0)) + 0) + x 0 1 (ix 0) = ((x 0 1 (ix 0)) + (x 0 1 (ix 1))) + x 2 3 (ix 0) at h0
    have h1 := congrFun (hx.commute 0 1 4 1 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 4 1 (ix 5)) + (x 4 1 (ix 8))) + x 0 1 (ix 5) = ((x 0 1 (ix 5)) + (x 0 1 (ix 1))) + x 4 1 (ix 5) at h1
    linear_combination (norm := (ring_nf; simp)) h0 + h1
  · change ((x 0 2 (ix 5)) + (x 0 1 (ix 3))) - (x 0 2 (ix 5)) = x 4 1 (ix 9)
    have h0 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h0
    change ((((x 0 1 (ix 1)) + (x 0 1 (ix 3))) + x 1 2 (ix 1)) + 0) + x 0 1 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 3))) + x 1 2 (ix 1) at h0
    have h1 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 1 3 (ix 0)) + 0) + x 0 2 (ix 0) = ((x 0 2 (ix 0)) + (x 0 2 (ix 3))) + x 1 3 (ix 0) at h1
    have h2 := congrFun (hx.commute 0 2 4 1 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 4 1 (ix 5)) + (x 4 1 (ix 9))) + x 0 2 (ix 5) = ((x 0 2 (ix 5)) + (x 0 2 (ix 1))) + x 4 1 (ix 5) at h2
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2

private theorem exact_4_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 3)
    (hx : ElementaryRelations 3 x) (s : Fin 10) :
    act 4 2 (witness x) s - witness x s = x 4 2 (ix s) := by
  fin_cases s
  · change ((x 3 0 (ix 6)) + 0) - (x 3 0 (ix 6)) = x 4 2 (ix 0)
    have h0 := congrFun (hx.commute 3 0 4 2 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 2 (ix 6)) + (x 4 2 (ix 0))) + x 3 0 (ix 6) = ((x 3 0 (ix 6)) + 0) + x 4 2 (ix 6) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 6)) + 0) - (x 2 0 (ix 6)) = x 4 2 (ix 1)
    have h0 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h0
    change ((((x 0 1 (ix 1)) + (x 0 1 (ix 3))) + x 1 2 (ix 1)) + 0) + x 0 1 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 3))) + x 1 2 (ix 1) at h0
    have h1 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 1 3 (ix 0)) + 0) + x 0 2 (ix 0) = ((x 0 2 (ix 0)) + (x 0 2 (ix 3))) + x 1 3 (ix 0) at h1
    have h2 := congrFun (hx.commute 0 2 4 1 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 4 1 (ix 5)) + (x 4 1 (ix 9))) + x 0 2 (ix 5) = ((x 0 2 (ix 5)) + (x 0 2 (ix 1))) + x 4 1 (ix 5) at h2
    have h3 := congrFun (hx.commute 1 0 4 0 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 4 0 (ix 6)) + (x 4 0 (ix 3))) + x 1 0 (ix 6) = ((x 1 0 (ix 6)) + 0) + x 4 0 (ix 6) at h3
    have h4 := congrFun (hx.commute 4 0 4 2 (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 4 2 (ix 8)) + (x 4 2 (ix 1))) + x 4 0 (ix 8) = ((x 4 0 (ix 8)) + (x 4 0 (ix 6))) + x 4 2 (ix 8) at h4
    have h5 := congrFun (hx.steinberg 4 0 1 (by decide) (by decide) (by decide)) (ix 9)
    simp only [Pi.add_apply, action_coords] at h5
    change ((((x 4 0 (ix 9)) + 0) + x 0 1 (ix 9)) + (((x 4 0 (ix 3)) + (x 4 0 (ix 6))) + x 0 1 (ix 3))) + x 4 0 (ix 9) = ((x 4 1 (ix 9)) + 0) + x 0 1 (ix 9) at h5
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5
  · change ((x 2 0 (ix 7)) + (x 3 0 (ix 6))) - (x 2 0 (ix 7)) = x 4 2 (ix 2)
    have h0 := congrFun (hx.commute 3 0 4 2 (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 2 (ix 8)) + (x 4 2 (ix 2))) + x 3 0 (ix 8) = ((x 3 0 (ix 8)) + (x 3 0 (ix 6))) + x 4 2 (ix 8) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 6)) + 0) - (x 1 0 (ix 6)) = x 4 2 (ix 3)
    have h0 := congrFun (hx.commute 1 0 4 2 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 2 (ix 6)) + (x 4 2 (ix 3))) + x 1 0 (ix 6) = ((x 1 0 (ix 6)) + 0) + x 4 2 (ix 6) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 7)) + 0) - (x 1 0 (ix 7)) = x 4 2 (ix 4)
    have h0 := congrFun (hx.commute 1 0 4 2 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 2 (ix 7)) + (x 4 2 (ix 4))) + x 1 0 (ix 7) = ((x 1 0 (ix 7)) + 0) + x 4 2 (ix 7) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 8)) + (x 1 0 (ix 6))) - (x 1 0 (ix 8)) = x 4 2 (ix 5)
    have h0 := congrFun (hx.commute 1 0 4 2 (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 2 (ix 8)) + (x 4 2 (ix 5))) + x 1 0 (ix 8) = ((x 1 0 (ix 8)) + (x 1 0 (ix 6))) + x 4 2 (ix 8) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 3)) + 0) - (x 0 1 (ix 3)) = x 4 2 (ix 6)
    have h0 := congrFun (hx.commute 0 1 4 2 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 2 (ix 3)) + (x 4 2 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + 0) + x 4 2 (ix 3) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 4)) + 0) - (x 0 1 (ix 4)) = x 4 2 (ix 7)
    have h0 := congrFun (hx.commute 0 1 4 2 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 2 (ix 4)) + (x 4 2 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + 0) + x 4 2 (ix 4) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 5)) + (x 0 1 (ix 3))) - (x 0 1 (ix 5)) = x 4 2 (ix 8)
    have h0 := congrFun (hx.commute 0 1 4 2 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 2 (ix 5)) + (x 4 2 (ix 8))) + x 0 1 (ix 5) = ((x 0 1 (ix 5)) + (x 0 1 (ix 3))) + x 4 2 (ix 5) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 2 (ix 5)) + 0) - (x 0 2 (ix 5)) = x 4 2 (ix 9)
    have h0 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 1 3 (ix 0)) + 0) + x 0 2 (ix 0) = ((x 0 2 (ix 0)) + (x 0 2 (ix 3))) + x 1 3 (ix 0) at h0
    have h1 := congrFun (hx.commute 0 2 4 2 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 4 2 (ix 5)) + (x 4 2 (ix 9))) + x 0 2 (ix 5) = ((x 0 2 (ix 5)) + (x 0 2 (ix 3))) + x 4 2 (ix 5) at h1
    linear_combination (norm := (ring_nf; simp)) h0 + h1

private theorem exact_4_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 3)
    (hx : ElementaryRelations 3 x) (s : Fin 10) :
    act 4 3 (witness x) s - witness x s = x 4 3 (ix s) := by
  fin_cases s
  · change ((x 3 0 (ix 6)) + 0) - (x 3 0 (ix 6)) = x 4 3 (ix 0)
    have h0 := congrFun (hx.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 1)
    simp only [Pi.add_apply, action_coords] at h0
    change ((((x 0 1 (ix 1)) + (x 0 1 (ix 3))) + x 1 2 (ix 1)) + 0) + x 0 1 (ix 1) = ((x 0 2 (ix 1)) + (x 0 2 (ix 3))) + x 1 2 (ix 1) at h0
    have h1 := congrFun (hx.commute 0 2 1 3 (by decide) (by decide)) (ix 0)
    simp only [Pi.add_apply, action_coords] at h1
    change ((x 1 3 (ix 0)) + 0) + x 0 2 (ix 0) = ((x 0 2 (ix 0)) + (x 0 2 (ix 3))) + x 1 3 (ix 0) at h1
    have h2 := congrFun (hx.commute 0 2 4 1 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h2
    change ((x 4 1 (ix 5)) + (x 4 1 (ix 9))) + x 0 2 (ix 5) = ((x 0 2 (ix 5)) + (x 0 2 (ix 1))) + x 4 1 (ix 5) at h2
    have h3 := congrFun (hx.commute 1 0 4 0 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h3
    change ((x 4 0 (ix 6)) + (x 4 0 (ix 3))) + x 1 0 (ix 6) = ((x 1 0 (ix 6)) + 0) + x 4 0 (ix 6) at h3
    have h4 := congrFun (hx.commute 4 0 4 3 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h4
    change ((x 4 3 (ix 7)) + (x 4 3 (ix 0))) + x 4 0 (ix 7) = ((x 4 0 (ix 7)) + (x 4 0 (ix 6))) + x 4 3 (ix 7) at h4
    have h5 := congrFun (hx.steinberg 4 0 1 (by decide) (by decide) (by decide)) (ix 9)
    simp only [Pi.add_apply, action_coords] at h5
    change ((((x 4 0 (ix 9)) + 0) + x 0 1 (ix 9)) + (((x 4 0 (ix 3)) + (x 4 0 (ix 6))) + x 0 1 (ix 3))) + x 4 0 (ix 9) = ((x 4 1 (ix 9)) + 0) + x 0 1 (ix 9) at h5
    linear_combination (norm := (ring_nf; simp)) h0 + h1 + h2 + h3 + h4 + h5
  · change ((x 2 0 (ix 6)) + 0) - (x 2 0 (ix 6)) = x 4 3 (ix 1)
    have h0 := congrFun (hx.commute 2 0 4 3 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 3 (ix 6)) + (x 4 3 (ix 1))) + x 2 0 (ix 6) = ((x 2 0 (ix 6)) + 0) + x 4 3 (ix 6) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 7)) + (x 2 0 (ix 6))) - (x 2 0 (ix 7)) = x 4 3 (ix 2)
    have h0 := congrFun (hx.commute 2 0 4 3 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 3 (ix 7)) + (x 4 3 (ix 2))) + x 2 0 (ix 7) = ((x 2 0 (ix 7)) + (x 2 0 (ix 6))) + x 4 3 (ix 7) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 6)) + 0) - (x 1 0 (ix 6)) = x 4 3 (ix 3)
    have h0 := congrFun (hx.commute 1 0 4 3 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 3 (ix 6)) + (x 4 3 (ix 3))) + x 1 0 (ix 6) = ((x 1 0 (ix 6)) + 0) + x 4 3 (ix 6) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 7)) + (x 1 0 (ix 6))) - (x 1 0 (ix 7)) = x 4 3 (ix 4)
    have h0 := congrFun (hx.commute 1 0 4 3 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 3 (ix 7)) + (x 4 3 (ix 4))) + x 1 0 (ix 7) = ((x 1 0 (ix 7)) + (x 1 0 (ix 6))) + x 4 3 (ix 7) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 8)) + 0) - (x 1 0 (ix 8)) = x 4 3 (ix 5)
    have h0 := congrFun (hx.commute 1 0 4 3 (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 3 (ix 8)) + (x 4 3 (ix 5))) + x 1 0 (ix 8) = ((x 1 0 (ix 8)) + 0) + x 4 3 (ix 8) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 3)) + 0) - (x 0 1 (ix 3)) = x 4 3 (ix 6)
    have h0 := congrFun (hx.commute 0 1 4 3 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 3 (ix 3)) + (x 4 3 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + 0) + x 4 3 (ix 3) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 4)) + (x 0 1 (ix 3))) - (x 0 1 (ix 4)) = x 4 3 (ix 7)
    have h0 := congrFun (hx.commute 0 1 4 3 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 3 (ix 4)) + (x 4 3 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + (x 0 1 (ix 3))) + x 4 3 (ix 4) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 5)) + 0) - (x 0 1 (ix 5)) = x 4 3 (ix 8)
    have h0 := congrFun (hx.commute 0 1 4 3 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 3 (ix 5)) + (x 4 3 (ix 8))) + x 0 1 (ix 5) = ((x 0 1 (ix 5)) + 0) + x 4 3 (ix 5) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 2 (ix 5)) + 0) - (x 0 2 (ix 5)) = x 4 3 (ix 9)
    have h0 := congrFun (hx.commute 0 2 4 3 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 3 (ix 5)) + (x 4 3 (ix 9))) + x 0 2 (ix 5) = ((x 0 2 (ix 5)) + 0) + x 4 3 (ix 5) at h0
    linear_combination (norm := (ring_nf; simp)) h0

private theorem exact_4_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 3)
    (hx : ElementaryRelations 3 x) (s : Fin 10) :
    act 4 4 (witness x) s - witness x s = x 4 4 (ix s) := by
  fin_cases s
  · change ((x 3 0 (ix 6)) + 0) - (x 3 0 (ix 6)) = x 4 4 (ix 0)
    have h0 := congrFun (hx.commute 3 0 4 4 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 4 (ix 6)) + (x 4 4 (ix 0))) + x 3 0 (ix 6) = ((x 3 0 (ix 6)) + 0) + x 4 4 (ix 6) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 6)) + 0) - (x 2 0 (ix 6)) = x 4 4 (ix 1)
    have h0 := congrFun (hx.commute 2 0 4 4 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 4 (ix 6)) + (x 4 4 (ix 1))) + x 2 0 (ix 6) = ((x 2 0 (ix 6)) + 0) + x 4 4 (ix 6) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 2 0 (ix 7)) + 0) - (x 2 0 (ix 7)) = x 4 4 (ix 2)
    have h0 := congrFun (hx.commute 2 0 4 4 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 4 (ix 7)) + (x 4 4 (ix 2))) + x 2 0 (ix 7) = ((x 2 0 (ix 7)) + 0) + x 4 4 (ix 7) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 6)) + 0) - (x 1 0 (ix 6)) = x 4 4 (ix 3)
    have h0 := congrFun (hx.commute 1 0 4 4 (by decide) (by decide)) (ix 6)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 4 (ix 6)) + (x 4 4 (ix 3))) + x 1 0 (ix 6) = ((x 1 0 (ix 6)) + 0) + x 4 4 (ix 6) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 7)) + 0) - (x 1 0 (ix 7)) = x 4 4 (ix 4)
    have h0 := congrFun (hx.commute 1 0 4 4 (by decide) (by decide)) (ix 7)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 4 (ix 7)) + (x 4 4 (ix 4))) + x 1 0 (ix 7) = ((x 1 0 (ix 7)) + 0) + x 4 4 (ix 7) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 1 0 (ix 8)) + 0) - (x 1 0 (ix 8)) = x 4 4 (ix 5)
    have h0 := congrFun (hx.commute 1 0 4 4 (by decide) (by decide)) (ix 8)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 4 (ix 8)) + (x 4 4 (ix 5))) + x 1 0 (ix 8) = ((x 1 0 (ix 8)) + 0) + x 4 4 (ix 8) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 3)) + 0) - (x 0 1 (ix 3)) = x 4 4 (ix 6)
    have h0 := congrFun (hx.commute 0 1 4 4 (by decide) (by decide)) (ix 3)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 4 (ix 3)) + (x 4 4 (ix 6))) + x 0 1 (ix 3) = ((x 0 1 (ix 3)) + 0) + x 4 4 (ix 3) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 4)) + 0) - (x 0 1 (ix 4)) = x 4 4 (ix 7)
    have h0 := congrFun (hx.commute 0 1 4 4 (by decide) (by decide)) (ix 4)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 4 (ix 4)) + (x 4 4 (ix 7))) + x 0 1 (ix 4) = ((x 0 1 (ix 4)) + 0) + x 4 4 (ix 4) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 1 (ix 5)) + 0) - (x 0 1 (ix 5)) = x 4 4 (ix 8)
    have h0 := congrFun (hx.commute 0 1 4 4 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 4 (ix 5)) + (x 4 4 (ix 8))) + x 0 1 (ix 5) = ((x 0 1 (ix 5)) + 0) + x 4 4 (ix 5) at h0
    linear_combination (norm := (ring_nf; simp)) h0
  · change ((x 0 2 (ix 5)) + 0) - (x 0 2 (ix 5)) = x 4 4 (ix 9)
    have h0 := congrFun (hx.commute 0 2 4 4 (by decide) (by decide)) (ix 5)
    simp only [Pi.add_apply, action_coords] at h0
    change ((x 4 4 (ix 5)) + (x 4 4 (ix 9))) + x 0 2 (ix 5) = ((x 0 2 (ix 5)) + 0) + x 4 4 (ix 5) at h0
    linear_combination (norm := (ring_nf; simp)) h0

private theorem witness_exact (x : Fin 5 → Fin 5 → ExteriorCoordinates 3)
    (hx : ElementaryRelations 3 x) (i j : Fin 5) (s : Fin 10) :
    act i j (witness x) s - witness x s = x i j (ix s) := by
  fin_cases i <;> fin_cases j
  · exact exact_0_0 x hx s
  · exact exact_0_1 x hx s
  · exact exact_0_2 x hx s
  · exact exact_0_3 x hx s
  · exact exact_0_4 x hx s
  · exact exact_1_0 x hx s
  · exact exact_1_1 x hx s
  · exact exact_1_2 x hx s
  · exact exact_1_3 x hx s
  · exact exact_1_4 x hx s
  · exact exact_2_0 x hx s
  · exact exact_2_1 x hx s
  · exact exact_2_2 x hx s
  · exact exact_2_3 x hx s
  · exact exact_2_4 x hx s
  · exact exact_3_0 x hx s
  · exact exact_3_1 x hx s
  · exact exact_3_2 x hx s
  · exact exact_3_3 x hx s
  · exact exact_3_4 x hx s
  · exact exact_4_0 x hx s
  · exact exact_4_1 x hx s
  · exact exact_4_2 x hx s
  · exact exact_4_3 x hx s
  · exact exact_4_4 x hx s

end CubeRelations

open CubeRelations in
/-- Every exterior-cube elementary relation family is a principal family. -/
public theorem elementaryRelations_exact_three :
    ∀ x : Fin 5 → Fin 5 → ExteriorCoordinates 3,
      ElementaryRelations 3 x → ∃ v : ExteriorCoordinates 3,
        ∀ i j, elementaryAction 3 i j v - v = x i j := by
  intro x hx
  let e : Fin 10 ≃ ExteriorIndex 3 := Equiv.ofBijective ix bij
  let v : ExteriorCoordinates 3 := fun S => witness x (e.symm S)
  have hv (s : Fin 10) : v (ix s) = witness x s := by
    change witness x (e.symm (e s)) = witness x s
    rw [e.symm_apply_apply]
  refine ⟨v, ?_⟩
  intro i j
  funext S
  obtain ⟨s, rfl⟩ := bij.surjective S
  change elementaryAction 3 i j v (ix s) - v (ix s) = x i j (ix s)
  simp only [action_coords, hv]
  exact witness_exact x hx i j s

end Representation.SL5TenDimensional
