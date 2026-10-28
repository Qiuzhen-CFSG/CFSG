module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.ExteriorVanishing.Reduction
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
/-!
# Exactness of the exterior-square elementary relations for SL₅(2)

The ten increasing pairs identify the exterior-square coordinates with `Fin 10`.
We check the elementary action table against the actual determinant minors, then
use sparse linear combinations of the square, commuting, and Steinberg relations
to recover every generator value from one vector. For a pair `S`, this vector has
coordinate `x i j ((S \ {j}) ∪ {i})`, where `j = min S` and `i = min Sᶜ`.

The certificates below are ordinary algebraic proofs over arbitrary coordinates
in `ZMod 2`. Only basis indices and determinant entries are checked by finite
computation; no enumeration of assignments to the 250 variables is used. The
finite tables and sparse combinations are independently verified by the kernel.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma I.1.6(7), printed p.408/PDF p.419, citing Jones--Parshall [JP76].
-/

open scoped BigOperators

namespace Representation.SL5TenDimensional

/-- Lexicographic enumeration of the two-element subsets. -/

private def ix : Fin 10 → ExteriorIndex 2 := ![
  ⟨{0, 1}, by change Finset.card _ = 2; decide⟩,
  ⟨{0, 2}, by change Finset.card _ = 2; decide⟩,
  ⟨{0, 3}, by change Finset.card _ = 2; decide⟩,
  ⟨{0, 4}, by change Finset.card _ = 2; decide⟩,
  ⟨{1, 2}, by change Finset.card _ = 2; decide⟩,
  ⟨{1, 3}, by change Finset.card _ = 2; decide⟩,
  ⟨{1, 4}, by change Finset.card _ = 2; decide⟩,
  ⟨{2, 3}, by change Finset.card _ = 2; decide⟩,
  ⟨{2, 4}, by change Finset.card _ = 2; decide⟩,
  ⟨{3, 4}, by change Finset.card _ = 2; decide⟩]

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

private theorem ix_inj : Function.Injective ix := by decide

private theorem ix_bij : Function.Bijective ix := by
  apply (Fintype.bijective_iff_injective_and_card ix).mpr
  refine ⟨ix_inj, ?_⟩
  rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, Set.powersetCard.card]
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

private def pair : Fin 10 → Fin 2 → Fin 5 :=
  ![![0,1], ![0,2], ![0,3], ![0,4], ![1,2], ![1,3], ![1,4], ![2,3], ![2,4], ![3,4]]

private def emb (s : Fin 10) : Fin 2 ↪o Fin 5 :=
  OrderEmbedding.ofStrictMono (pair s) ((by decide : ∀ s, StrictMono (pair s)) s)

private theorem ix_emb (s : Fin 10) : ix s = Set.powersetCard.ofFinEmbEquiv (emb s) := by
  fin_cases s <;> decide

private theorem ix_order (s : Fin 10) : Set.powersetCard.ofFinEmbEquiv.symm (ix s) = emb s := by
  rw [ix_emb, Equiv.symm_apply_apply]
/-- For output pair `S`, the extra input is `S - {i} + {j}` if `i ∈ S`, `j ∉ S`.
Each row lists these extra inputs for the ten pairs; `none` means zero. -/

private def source : Fin 5 → Fin 5 → Fin 10 → Option (Fin 10) :=
  ![![![none, none, none, none, none, none, none, none, none, none],
      ![none, some 4, some 5, some 6, none, none, none, none, none, none],
      ![some 4, none, some 7, some 8, none, none, none, none, none, none],
      ![some 5, some 7, none, some 9, none, none, none, none, none, none],
      ![some 6, some 8, some 9, none, none, none, none, none, none, none]],
    ![![none, none, none, none, some 1, some 2, some 3, none, none, none],
      ![none, none, none, none, none, none, none, none, none, none],
      ![some 1, none, none, none, none, some 7, some 8, none, none, none],
      ![some 2, none, none, none, some 7, none, some 9, none, none, none],
      ![some 3, none, none, none, some 8, some 9, none, none, none, none]],
    ![![none, none, none, none, some 0, none, none, some 2, some 3, none],
      ![none, some 0, none, none, none, none, none, some 5, some 6, none],
      ![none, none, none, none, none, none, none, none, none, none],
      ![none, some 2, none, none, some 5, none, none, none, some 9, none],
      ![none, some 3, none, none, some 6, none, none, some 9, none, none]],
    ![![none, none, none, none, none, some 0, none, some 1, none, some 3],
      ![none, none, some 0, none, none, none, none, some 4, none, some 6],
      ![none, none, some 1, none, none, some 4, none, none, none, some 8],
      ![none, none, none, none, none, none, none, none, none, none],
      ![none, none, some 3, none, none, some 6, none, some 8, none, none]],
    ![![none, none, none, none, none, none, some 0, none, some 1, some 2],
      ![none, none, none, some 0, none, none, none, none, some 4, some 5],
      ![none, none, none, some 1, none, none, some 4, none, none, some 7],
      ![none, none, none, some 2, none, none, some 5, none, some 7, none],
      ![none, none, none, none, none, none, none, none, none, none]]]

private def act (i j : Fin 5) (v : Fin 10 → ZMod 2) (s : Fin 10) : ZMod 2 :=
  v s + match source i j s with | none => 0 | some t => v t

private def coeff (i j : Fin 5) (s t : Fin 10) : ZMod 2 :=
  (if s = t then 1 else 0) +
    match source i j s with | none => 0 | some u => if u = t then 1 else 0
/-- Verification against the genuine two-by-two determinant minors. -/

private theorem matrix_entry (i j : Fin 5) (s t : Fin 10) :
    exteriorMatrix 2 (elementary i j) (ix s) (ix t) = coeff i j s t := by
  simp only [exteriorMatrix, Matrix.det_fin_two, Matrix.of_apply, ix_order]
  revert i j s t
  decide

private noncomputable def indexEquiv : Fin 10 ≃ ExteriorIndex 2 :=
  Equiv.ofBijective ix ix_bij
/-- Reindex the determinant action and use the verified sparse matrix entries. -/

private theorem action_coord (i j : Fin 5) (v : ExteriorCoordinates 2) (s : Fin 10) :
    elementaryAction 2 i j v (ix s) = act i j (fun t => v (ix t)) s := by
  change (∑ t, exteriorMatrix 2 (elementary i j) (ix s) t * v t) = _
  rw [← indexEquiv.sum_comp]
  change (∑ t, exteriorMatrix 2 (elementary i j) (ix s) (ix t) * v (ix t)) = _
  simp only [matrix_entry, coeff, add_mul, Finset.sum_add_distrib]
  unfold act
  cases h : source i j s <;> simp

/-- The vector reconstructed from the least element of a pair and its complement. -/

private def witness (x : Fin 5 → Fin 5 → Fin 10 → ZMod 2) : Fin 10 → ZMod 2 :=
  ![x 2 0 4, x 1 0 4, x 1 0 5, x 1 0 6, x 0 1 1, x 0 1 2, x 0 1 3, x 0 2 2, x 0 2 3, x 0 3 3]

private theorem two_zero : (2 : ZMod 2) = 0 := by decide

private theorem four_zero : (4 : ZMod 2) = 0 := by decide
attribute [local simp] two_zero four_zero
-- Ring normalization followed by reduction of the even coefficients occurring below.
local macro "square_ring" : tactic =>
  `(tactic| (ring_nf <;> simp))

/- Each certificate extracts the displayed scalar relation coordinates and adds them.
The suffix records the generator indices and the lexicographic output coordinate. -/

private theorem cert_0_0_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 0 (witness (fun i j s => x i j (ix s))) 0 -
      witness (fun i j s => x i j (ix s)) 0 = x 0 0 (ix 0) := by
  have h0 := congrFun (h.diagonal 0) (ix 0)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_0_0_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 0 (witness (fun i j s => x i j (ix s))) 1 -
      witness (fun i j s => x i j (ix s)) 1 = x 0 0 (ix 1) := by
  have h0 := congrFun (h.diagonal 0) (ix 1)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_0_0_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 0 (witness (fun i j s => x i j (ix s))) 2 -
      witness (fun i j s => x i j (ix s)) 2 = x 0 0 (ix 2) := by
  have h0 := congrFun (h.diagonal 0) (ix 2)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_0_0_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 0 (witness (fun i j s => x i j (ix s))) 3 -
      witness (fun i j s => x i j (ix s)) 3 = x 0 0 (ix 3) := by
  have h0 := congrFun (h.diagonal 0) (ix 3)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_0_0_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 0 (witness (fun i j s => x i j (ix s))) 4 -
      witness (fun i j s => x i j (ix s)) 4 = x 0 0 (ix 4) := by
  have h0 := congrFun (h.diagonal 0) (ix 4)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_0_0_5 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 0 (witness (fun i j s => x i j (ix s))) 5 -
      witness (fun i j s => x i j (ix s)) 5 = x 0 0 (ix 5) := by
  have h0 := congrFun (h.diagonal 0) (ix 5)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_0_0_6 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 0 (witness (fun i j s => x i j (ix s))) 6 -
      witness (fun i j s => x i j (ix s)) 6 = x 0 0 (ix 6) := by
  have h0 := congrFun (h.diagonal 0) (ix 6)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_0_0_7 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 0 (witness (fun i j s => x i j (ix s))) 7 -
      witness (fun i j s => x i j (ix s)) 7 = x 0 0 (ix 7) := by
  have h0 := congrFun (h.diagonal 0) (ix 7)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_0_0_8 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 0 (witness (fun i j s => x i j (ix s))) 8 -
      witness (fun i j s => x i j (ix s)) 8 = x 0 0 (ix 8) := by
  have h0 := congrFun (h.diagonal 0) (ix 8)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_0_0_9 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 0 (witness (fun i j s => x i j (ix s))) 9 -
      witness (fun i j s => x i j (ix s)) 9 = x 0 0 (ix 9) := by
  have h0 := congrFun (h.diagonal 0) (ix 9)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_0_1_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 1 (witness (fun i j s => x i j (ix s))) 0 -
      witness (fun i j s => x i j (ix s)) 0 = x 0 1 (ix 0) := by
  have h0 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h1 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
  have h2 := congrFun (h.commute 0 2 3 1 (by decide) (by decide)) (ix 2)
  have h3 := congrFun (h.steinberg 0 2 1 (by decide) (by decide) (by decide)) (ix 1)
  have h4 := congrFun (h.steinberg 0 3 1 (by decide) (by decide) (by decide)) (ix 1)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4

private theorem cert_0_1_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (_h : ElementaryRelations 2 x) :
    act 0 1 (witness (fun i j s => x i j (ix s))) 1 -
      witness (fun i j s => x i j (ix s)) 1 = x 0 1 (ix 1) := by
  simp [act, source, witness]

private theorem cert_0_1_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (_h : ElementaryRelations 2 x) :
    act 0 1 (witness (fun i j s => x i j (ix s))) 2 -
      witness (fun i j s => x i j (ix s)) 2 = x 0 1 (ix 2) := by
  simp [act, source, witness]

private theorem cert_0_1_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (_h : ElementaryRelations 2 x) :
    act 0 1 (witness (fun i j s => x i j (ix s))) 3 -
      witness (fun i j s => x i j (ix s)) 3 = x 0 1 (ix 3) := by
  simp [act, source, witness]

private theorem cert_0_1_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 1 (witness (fun i j s => x i j (ix s))) 4 -
      witness (fun i j s => x i j (ix s)) 4 = x 0 1 (ix 4) := by
  have h0 := congrFun (h.square 0 1) (ix 1)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_0_1_5 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 1 (witness (fun i j s => x i j (ix s))) 5 -
      witness (fun i j s => x i j (ix s)) 5 = x 0 1 (ix 5) := by
  have h0 := congrFun (h.square 0 1) (ix 2)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_0_1_6 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 1 (witness (fun i j s => x i j (ix s))) 6 -
      witness (fun i j s => x i j (ix s)) 6 = x 0 1 (ix 6) := by
  have h0 := congrFun (h.square 0 1) (ix 3)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_0_1_7 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 1 (witness (fun i j s => x i j (ix s))) 7 -
      witness (fun i j s => x i j (ix s)) 7 = x 0 1 (ix 7) := by
  have h0 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_0_1_8 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 1 (witness (fun i j s => x i j (ix s))) 8 -
      witness (fun i j s => x i j (ix s)) 8 = x 0 1 (ix 8) := by
  have h0 := congrFun (h.commute 0 1 3 2 (by decide) (by decide)) (ix 9)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_0_1_9 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 1 (witness (fun i j s => x i j (ix s))) 9 -
      witness (fun i j s => x i j (ix s)) 9 = x 0 1 (ix 9) := by
  have h0 := congrFun (h.commute 0 1 2 3 (by decide) (by decide)) (ix 8)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_0_2_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 2 (witness (fun i j s => x i j (ix s))) 0 -
      witness (fun i j s => x i j (ix s)) 0 = x 0 2 (ix 0) := by
  have h0 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h1 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
  have h2 := congrFun (h.commute 0 2 3 1 (by decide) (by decide)) (ix 2)
  have h3 := congrFun (h.steinberg 0 3 1 (by decide) (by decide) (by decide)) (ix 1)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3

private theorem cert_0_2_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 2 (witness (fun i j s => x i j (ix s))) 1 -
      witness (fun i j s => x i j (ix s)) 1 = x 0 2 (ix 1) := by
  have h0 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h1 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 0)
  have h2 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
  have h3 := congrFun (h.commute 0 2 3 1 (by decide) (by decide)) (ix 2)
  have h4 := congrFun (h.steinberg 0 3 1 (by decide) (by decide) (by decide)) (ix 1)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4

private theorem cert_0_2_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (_h : ElementaryRelations 2 x) :
    act 0 2 (witness (fun i j s => x i j (ix s))) 2 -
      witness (fun i j s => x i j (ix s)) 2 = x 0 2 (ix 2) := by
  simp [act, source, witness]

private theorem cert_0_2_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (_h : ElementaryRelations 2 x) :
    act 0 2 (witness (fun i j s => x i j (ix s))) 3 -
      witness (fun i j s => x i j (ix s)) 3 = x 0 2 (ix 3) := by
  simp [act, source, witness]

private theorem cert_0_2_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 2 (witness (fun i j s => x i j (ix s))) 4 -
      witness (fun i j s => x i j (ix s)) 4 = x 0 2 (ix 4) := by
  have h0 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 1)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_0_2_5 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 2 (witness (fun i j s => x i j (ix s))) 5 -
      witness (fun i j s => x i j (ix s)) 5 = x 0 2 (ix 5) := by
  have h0 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 2)
  have h1 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  simp [act, source, witness, action_coord] at h0 h1 ⊢
  linear_combination (norm := square_ring) h0 + h1

private theorem cert_0_2_6 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 2 (witness (fun i j s => x i j (ix s))) 6 -
      witness (fun i j s => x i j (ix s)) 6 = x 0 2 (ix 6) := by
  have h0 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 3)
  have h1 := congrFun (h.commute 0 1 3 2 (by decide) (by decide)) (ix 9)
  simp [act, source, witness, action_coord] at h0 h1 ⊢
  linear_combination (norm := square_ring) h0 + h1

private theorem cert_0_2_7 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 2 (witness (fun i j s => x i j (ix s))) 7 -
      witness (fun i j s => x i j (ix s)) 7 = x 0 2 (ix 7) := by
  have h0 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 2)
  have h1 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 5)
  simp [act, source, witness, action_coord] at h0 h1 ⊢
  linear_combination (norm := square_ring) h0 + h1

private theorem cert_0_2_8 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 2 (witness (fun i j s => x i j (ix s))) 8 -
      witness (fun i j s => x i j (ix s)) 8 = x 0 2 (ix 8) := by
  have h0 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 3)
  have h1 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 6)
  simp [act, source, witness, action_coord] at h0 h1 ⊢
  linear_combination (norm := square_ring) h0 + h1

private theorem cert_0_2_9 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 2 (witness (fun i j s => x i j (ix s))) 9 -
      witness (fun i j s => x i j (ix s)) 9 = x 0 2 (ix 9) := by
  have h0 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 9)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_0_3_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 3 (witness (fun i j s => x i j (ix s))) 0 -
      witness (fun i j s => x i j (ix s)) 0 = x 0 3 (ix 0) := by
  have h0 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 1)
  have h1 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 2)
  have h2 := congrFun (h.commute 0 1 2 3 (by decide) (by decide)) (ix 1)
  have h3 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h4 := congrFun (h.steinberg 0 2 3 (by decide) (by decide) (by decide)) (ix 0)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4

private theorem cert_0_3_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 3 (witness (fun i j s => x i j (ix s))) 1 -
      witness (fun i j s => x i j (ix s)) 1 = x 0 3 (ix 1) := by
  have h0 := congrFun (h.square 0 1) (ix 1)
  have h1 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h2 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 1)
  have h3 := congrFun (h.commute 0 2 1 3 (by decide) (by decide)) (ix 0)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3

private theorem cert_0_3_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 3 (witness (fun i j s => x i j (ix s))) 2 -
      witness (fun i j s => x i j (ix s)) 2 = x 0 3 (ix 2) := by
  have h0 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 1)
  have h1 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 2)
  have h2 := congrFun (h.commute 0 1 2 3 (by decide) (by decide)) (ix 1)
  have h3 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h4 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 0)
  have h5 := congrFun (h.steinberg 0 2 3 (by decide) (by decide) (by decide)) (ix 0)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5

private theorem cert_0_3_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (_h : ElementaryRelations 2 x) :
    act 0 3 (witness (fun i j s => x i j (ix s))) 3 -
      witness (fun i j s => x i j (ix s)) 3 = x 0 3 (ix 3) := by
  simp [act, source, witness]

private theorem cert_0_3_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 3 (witness (fun i j s => x i j (ix s))) 4 -
      witness (fun i j s => x i j (ix s)) 4 = x 0 3 (ix 4) := by
  have h0 := congrFun (h.commute 0 1 0 3 (by decide) (by decide)) (ix 1)
  have h1 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  simp [act, source, witness, action_coord] at h0 h1 ⊢
  linear_combination (norm := square_ring) h0 + h1

private theorem cert_0_3_5 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 3 (witness (fun i j s => x i j (ix s))) 5 -
      witness (fun i j s => x i j (ix s)) 5 = x 0 3 (ix 5) := by
  have h0 := congrFun (h.commute 0 1 0 3 (by decide) (by decide)) (ix 2)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_0_3_6 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 3 (witness (fun i j s => x i j (ix s))) 6 -
      witness (fun i j s => x i j (ix s)) 6 = x 0 3 (ix 6) := by
  have h0 := congrFun (h.commute 0 1 0 3 (by decide) (by decide)) (ix 3)
  have h1 := congrFun (h.commute 0 1 2 3 (by decide) (by decide)) (ix 8)
  simp [act, source, witness, action_coord] at h0 h1 ⊢
  linear_combination (norm := square_ring) h0 + h1

private theorem cert_0_3_7 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 3 (witness (fun i j s => x i j (ix s))) 7 -
      witness (fun i j s => x i j (ix s)) 7 = x 0 3 (ix 7) := by
  have h0 := congrFun (h.commute 0 1 0 3 (by decide) (by decide)) (ix 1)
  have h1 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
  simp [act, source, witness, action_coord] at h0 h1 ⊢
  linear_combination (norm := square_ring) h0 + h1

private theorem cert_0_3_8 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 3 (witness (fun i j s => x i j (ix s))) 8 -
      witness (fun i j s => x i j (ix s)) 8 = x 0 3 (ix 8) := by
  have h0 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 8)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_0_3_9 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 3 (witness (fun i j s => x i j (ix s))) 9 -
      witness (fun i j s => x i j (ix s)) 9 = x 0 3 (ix 9) := by
  have h0 := congrFun (h.commute 0 1 0 3 (by decide) (by decide)) (ix 3)
  have h1 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 6)
  simp [act, source, witness, action_coord] at h0 h1 ⊢
  linear_combination (norm := square_ring) h0 + h1

private theorem cert_0_4_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 4 (witness (fun i j s => x i j (ix s))) 0 -
      witness (fun i j s => x i j (ix s)) 0 = x 0 4 (ix 0) := by
  have h0 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 1)
  have h1 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 3)
  have h2 := congrFun (h.commute 0 1 2 4 (by decide) (by decide)) (ix 1)
  have h3 := congrFun (h.commute 0 1 3 2 (by decide) (by decide)) (ix 9)
  have h4 := congrFun (h.steinberg 0 2 4 (by decide) (by decide) (by decide)) (ix 0)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4

private theorem cert_0_4_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 4 (witness (fun i j s => x i j (ix s))) 1 -
      witness (fun i j s => x i j (ix s)) 1 = x 0 4 (ix 1) := by
  have h0 := congrFun (h.square 0 1) (ix 1)
  have h1 := congrFun (h.commute 0 1 3 2 (by decide) (by decide)) (ix 9)
  have h2 := congrFun (h.steinberg 0 1 4 (by decide) (by decide) (by decide)) (ix 1)
  have h3 := congrFun (h.commute 0 2 1 4 (by decide) (by decide)) (ix 0)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3

private theorem cert_0_4_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 4 (witness (fun i j s => x i j (ix s))) 2 -
      witness (fun i j s => x i j (ix s)) 2 = x 0 4 (ix 2) := by
  have h0 := congrFun (h.square 0 1) (ix 2)
  have h1 := congrFun (h.commute 0 1 2 3 (by decide) (by decide)) (ix 8)
  have h2 := congrFun (h.steinberg 0 1 4 (by decide) (by decide) (by decide)) (ix 2)
  have h3 := congrFun (h.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3

private theorem cert_0_4_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 4 (witness (fun i j s => x i j (ix s))) 3 -
      witness (fun i j s => x i j (ix s)) 3 = x 0 4 (ix 3) := by
  have h0 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 1)
  have h1 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 3)
  have h2 := congrFun (h.commute 0 1 2 4 (by decide) (by decide)) (ix 1)
  have h3 := congrFun (h.commute 0 1 3 2 (by decide) (by decide)) (ix 9)
  have h4 := congrFun (h.steinberg 0 1 4 (by decide) (by decide) (by decide)) (ix 0)
  have h5 := congrFun (h.steinberg 0 2 4 (by decide) (by decide) (by decide)) (ix 0)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5

private theorem cert_0_4_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 4 (witness (fun i j s => x i j (ix s))) 4 -
      witness (fun i j s => x i j (ix s)) 4 = x 0 4 (ix 4) := by
  have h0 := congrFun (h.commute 0 1 0 4 (by decide) (by decide)) (ix 1)
  have h1 := congrFun (h.commute 0 1 3 2 (by decide) (by decide)) (ix 9)
  simp [act, source, witness, action_coord] at h0 h1 ⊢
  linear_combination (norm := square_ring) h0 + h1

private theorem cert_0_4_5 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 4 (witness (fun i j s => x i j (ix s))) 5 -
      witness (fun i j s => x i j (ix s)) 5 = x 0 4 (ix 5) := by
  have h0 := congrFun (h.commute 0 1 0 4 (by decide) (by decide)) (ix 2)
  have h1 := congrFun (h.commute 0 1 2 3 (by decide) (by decide)) (ix 8)
  simp [act, source, witness, action_coord] at h0 h1 ⊢
  linear_combination (norm := square_ring) h0 + h1

private theorem cert_0_4_6 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 4 (witness (fun i j s => x i j (ix s))) 6 -
      witness (fun i j s => x i j (ix s)) 6 = x 0 4 (ix 6) := by
  have h0 := congrFun (h.commute 0 1 0 4 (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_0_4_7 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 4 (witness (fun i j s => x i j (ix s))) 7 -
      witness (fun i j s => x i j (ix s)) 7 = x 0 4 (ix 7) := by
  have h0 := congrFun (h.steinberg 0 1 4 (by decide) (by decide) (by decide)) (ix 7)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_0_4_8 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 4 (witness (fun i j s => x i j (ix s))) 8 -
      witness (fun i j s => x i j (ix s)) 8 = x 0 4 (ix 8) := by
  have h0 := congrFun (h.commute 0 1 0 4 (by decide) (by decide)) (ix 1)
  have h1 := congrFun (h.steinberg 0 1 4 (by decide) (by decide) (by decide)) (ix 4)
  simp [act, source, witness, action_coord] at h0 h1 ⊢
  linear_combination (norm := square_ring) h0 + h1

private theorem cert_0_4_9 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 0 4 (witness (fun i j s => x i j (ix s))) 9 -
      witness (fun i j s => x i j (ix s)) 9 = x 0 4 (ix 9) := by
  have h0 := congrFun (h.commute 0 1 0 4 (by decide) (by decide)) (ix 2)
  have h1 := congrFun (h.steinberg 0 1 4 (by decide) (by decide) (by decide)) (ix 5)
  simp [act, source, witness, action_coord] at h0 h1 ⊢
  linear_combination (norm := square_ring) h0 + h1

private theorem cert_1_0_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 0 (witness (fun i j s => x i j (ix s))) 0 -
      witness (fun i j s => x i j (ix s)) 0 = x 1 0 (ix 0) := by
  have h0 := congrFun (h.square 0 1) (ix 1)
  have h1 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h2 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 0)
  have h3 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 1)
  have h4 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
  have h5 := congrFun (h.commute 0 2 3 1 (by decide) (by decide)) (ix 2)
  have h6 := congrFun (h.steinberg 0 3 1 (by decide) (by decide) (by decide)) (ix 1)
  have h7 := congrFun (h.steinberg 1 0 2 (by decide) (by decide) (by decide)) (ix 0)
  have h8 := congrFun (h.steinberg 1 2 0 (by decide) (by decide) (by decide)) (ix 4)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8

private theorem cert_1_0_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 0 (witness (fun i j s => x i j (ix s))) 1 -
      witness (fun i j s => x i j (ix s)) 1 = x 1 0 (ix 1) := by
  have h0 := congrFun (h.square 1 0) (ix 4)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_0_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 0 (witness (fun i j s => x i j (ix s))) 2 -
      witness (fun i j s => x i j (ix s)) 2 = x 1 0 (ix 2) := by
  have h0 := congrFun (h.square 1 0) (ix 5)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_0_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 0 (witness (fun i j s => x i j (ix s))) 3 -
      witness (fun i j s => x i j (ix s)) 3 = x 1 0 (ix 3) := by
  have h0 := congrFun (h.square 1 0) (ix 6)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_0_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (_h : ElementaryRelations 2 x) :
    act 1 0 (witness (fun i j s => x i j (ix s))) 4 -
      witness (fun i j s => x i j (ix s)) 4 = x 1 0 (ix 4) := by
  simp [act, source, witness]

private theorem cert_1_0_5 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (_h : ElementaryRelations 2 x) :
    act 1 0 (witness (fun i j s => x i j (ix s))) 5 -
      witness (fun i j s => x i j (ix s)) 5 = x 1 0 (ix 5) := by
  simp [act, source, witness]

private theorem cert_1_0_6 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (_h : ElementaryRelations 2 x) :
    act 1 0 (witness (fun i j s => x i j (ix s))) 6 -
      witness (fun i j s => x i j (ix s)) 6 = x 1 0 (ix 6) := by
  simp [act, source, witness]

private theorem cert_1_0_7 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 0 (witness (fun i j s => x i j (ix s))) 7 -
      witness (fun i j s => x i j (ix s)) 7 = x 1 0 (ix 7) := by
  have h0 := congrFun (h.commute 1 0 4 2 (by decide) (by decide)) (ix 9)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_0_8 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 0 (witness (fun i j s => x i j (ix s))) 8 -
      witness (fun i j s => x i j (ix s)) 8 = x 1 0 (ix 8) := by
  have h0 := congrFun (h.commute 1 0 3 2 (by decide) (by decide)) (ix 9)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_0_9 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 0 (witness (fun i j s => x i j (ix s))) 9 -
      witness (fun i j s => x i j (ix s)) 9 = x 1 0 (ix 9) := by
  have h0 := congrFun (h.commute 1 0 2 3 (by decide) (by decide)) (ix 8)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_1_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 1 (witness (fun i j s => x i j (ix s))) 0 -
      witness (fun i j s => x i j (ix s)) 0 = x 1 1 (ix 0) := by
  have h0 := congrFun (h.diagonal 1) (ix 0)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_1_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 1 (witness (fun i j s => x i j (ix s))) 1 -
      witness (fun i j s => x i j (ix s)) 1 = x 1 1 (ix 1) := by
  have h0 := congrFun (h.diagonal 1) (ix 1)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_1_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 1 (witness (fun i j s => x i j (ix s))) 2 -
      witness (fun i j s => x i j (ix s)) 2 = x 1 1 (ix 2) := by
  have h0 := congrFun (h.diagonal 1) (ix 2)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_1_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 1 (witness (fun i j s => x i j (ix s))) 3 -
      witness (fun i j s => x i j (ix s)) 3 = x 1 1 (ix 3) := by
  have h0 := congrFun (h.diagonal 1) (ix 3)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_1_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 1 (witness (fun i j s => x i j (ix s))) 4 -
      witness (fun i j s => x i j (ix s)) 4 = x 1 1 (ix 4) := by
  have h0 := congrFun (h.diagonal 1) (ix 4)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_1_5 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 1 (witness (fun i j s => x i j (ix s))) 5 -
      witness (fun i j s => x i j (ix s)) 5 = x 1 1 (ix 5) := by
  have h0 := congrFun (h.diagonal 1) (ix 5)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_1_6 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 1 (witness (fun i j s => x i j (ix s))) 6 -
      witness (fun i j s => x i j (ix s)) 6 = x 1 1 (ix 6) := by
  have h0 := congrFun (h.diagonal 1) (ix 6)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_1_7 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 1 (witness (fun i j s => x i j (ix s))) 7 -
      witness (fun i j s => x i j (ix s)) 7 = x 1 1 (ix 7) := by
  have h0 := congrFun (h.diagonal 1) (ix 7)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_1_8 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 1 (witness (fun i j s => x i j (ix s))) 8 -
      witness (fun i j s => x i j (ix s)) 8 = x 1 1 (ix 8) := by
  have h0 := congrFun (h.diagonal 1) (ix 8)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_1_9 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 1 (witness (fun i j s => x i j (ix s))) 9 -
      witness (fun i j s => x i j (ix s)) 9 = x 1 1 (ix 9) := by
  have h0 := congrFun (h.diagonal 1) (ix 9)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_2_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 2 (witness (fun i j s => x i j (ix s))) 0 -
      witness (fun i j s => x i j (ix s)) 0 = x 1 2 (ix 0) := by
  have h0 := congrFun (h.square 0 1) (ix 1)
  have h1 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h2 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 0)
  have h3 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 1)
  have h4 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
  have h5 := congrFun (h.commute 0 2 3 1 (by decide) (by decide)) (ix 2)
  have h6 := congrFun (h.steinberg 0 3 1 (by decide) (by decide) (by decide)) (ix 1)
  have h7 := congrFun (h.steinberg 1 0 2 (by decide) (by decide) (by decide)) (ix 0)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7

private theorem cert_1_2_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 2 (witness (fun i j s => x i j (ix s))) 1 -
      witness (fun i j s => x i j (ix s)) 1 = x 1 2 (ix 1) := by
  have h0 := congrFun (h.commute 1 0 1 2 (by decide) (by decide)) (ix 4)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_2_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 2 (witness (fun i j s => x i j (ix s))) 2 -
      witness (fun i j s => x i j (ix s)) 2 = x 1 2 (ix 2) := by
  have h0 := congrFun (h.commute 1 0 1 2 (by decide) (by decide)) (ix 5)
  have h1 := congrFun (h.commute 1 0 4 2 (by decide) (by decide)) (ix 9)
  simp [act, source, witness, action_coord] at h0 h1 ⊢
  linear_combination (norm := square_ring) h0 + h1

private theorem cert_1_2_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 2 (witness (fun i j s => x i j (ix s))) 3 -
      witness (fun i j s => x i j (ix s)) 3 = x 1 2 (ix 3) := by
  have h0 := congrFun (h.commute 1 0 1 2 (by decide) (by decide)) (ix 6)
  have h1 := congrFun (h.commute 1 0 3 2 (by decide) (by decide)) (ix 9)
  simp [act, source, witness, action_coord] at h0 h1 ⊢
  linear_combination (norm := square_ring) h0 + h1

private theorem cert_1_2_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 2 (witness (fun i j s => x i j (ix s))) 4 -
      witness (fun i j s => x i j (ix s)) 4 = x 1 2 (ix 4) := by
  have h0 := congrFun (h.square 0 1) (ix 1)
  have h1 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h2 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 0)
  have h3 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 1)
  have h4 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
  have h5 := congrFun (h.commute 0 2 3 1 (by decide) (by decide)) (ix 2)
  have h6 := congrFun (h.steinberg 0 3 1 (by decide) (by decide) (by decide)) (ix 1)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 h6 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5 + h6

private theorem cert_1_2_5 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 2 (witness (fun i j s => x i j (ix s))) 5 -
      witness (fun i j s => x i j (ix s)) 5 = x 1 2 (ix 5) := by
  have h0 := congrFun (h.square 0 1) (ix 2)
  have h1 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h2 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 2)
  simp [act, source, witness, action_coord] at h0 h1 h2 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2

private theorem cert_1_2_6 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 2 (witness (fun i j s => x i j (ix s))) 6 -
      witness (fun i j s => x i j (ix s)) 6 = x 1 2 (ix 6) := by
  have h0 := congrFun (h.square 0 1) (ix 3)
  have h1 := congrFun (h.commute 0 1 3 2 (by decide) (by decide)) (ix 9)
  have h2 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 h1 h2 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2

private theorem cert_1_2_7 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 2 (witness (fun i j s => x i j (ix s))) 7 -
      witness (fun i j s => x i j (ix s)) 7 = x 1 2 (ix 7) := by
  have h0 := congrFun (h.commute 0 2 1 2 (by decide) (by decide)) (ix 2)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_2_8 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 2 (witness (fun i j s => x i j (ix s))) 8 -
      witness (fun i j s => x i j (ix s)) 8 = x 1 2 (ix 8) := by
  have h0 := congrFun (h.commute 0 2 1 2 (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_2_9 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 2 (witness (fun i j s => x i j (ix s))) 9 -
      witness (fun i j s => x i j (ix s)) 9 = x 1 2 (ix 9) := by
  have h0 := congrFun (h.commute 0 3 1 2 (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_3_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 3 (witness (fun i j s => x i j (ix s))) 0 -
      witness (fun i j s => x i j (ix s)) 0 = x 1 3 (ix 0) := by
  have h0 := congrFun (h.square 0 1) (ix 2)
  have h1 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 1)
  have h2 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 2)
  have h3 := congrFun (h.commute 0 1 2 3 (by decide) (by decide)) (ix 1)
  have h4 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h5 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 0)
  have h6 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 2)
  have h7 := congrFun (h.steinberg 0 2 3 (by decide) (by decide) (by decide)) (ix 0)
  have h8 := congrFun (h.steinberg 1 0 3 (by decide) (by decide) (by decide)) (ix 0)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8

private theorem cert_1_3_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 3 (witness (fun i j s => x i j (ix s))) 1 -
      witness (fun i j s => x i j (ix s)) 1 = x 1 3 (ix 1) := by
  have h0 := congrFun (h.commute 1 0 1 3 (by decide) (by decide)) (ix 4)
  have h1 := congrFun (h.commute 1 0 4 2 (by decide) (by decide)) (ix 9)
  simp [act, source, witness, action_coord] at h0 h1 ⊢
  linear_combination (norm := square_ring) h0 + h1

private theorem cert_1_3_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 3 (witness (fun i j s => x i j (ix s))) 2 -
      witness (fun i j s => x i j (ix s)) 2 = x 1 3 (ix 2) := by
  have h0 := congrFun (h.commute 1 0 1 3 (by decide) (by decide)) (ix 5)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_3_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 3 (witness (fun i j s => x i j (ix s))) 3 -
      witness (fun i j s => x i j (ix s)) 3 = x 1 3 (ix 3) := by
  have h0 := congrFun (h.commute 1 0 1 3 (by decide) (by decide)) (ix 6)
  have h1 := congrFun (h.commute 1 0 2 3 (by decide) (by decide)) (ix 8)
  simp [act, source, witness, action_coord] at h0 h1 ⊢
  linear_combination (norm := square_ring) h0 + h1

private theorem cert_1_3_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 3 (witness (fun i j s => x i j (ix s))) 4 -
      witness (fun i j s => x i j (ix s)) 4 = x 1 3 (ix 4) := by
  have h0 := congrFun (h.commute 0 2 1 3 (by decide) (by decide)) (ix 0)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_3_5 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 3 (witness (fun i j s => x i j (ix s))) 5 -
      witness (fun i j s => x i j (ix s)) 5 = x 1 3 (ix 5) := by
  have h0 := congrFun (h.square 0 1) (ix 2)
  have h1 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 1)
  have h2 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 2)
  have h3 := congrFun (h.commute 0 1 2 3 (by decide) (by decide)) (ix 1)
  have h4 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h5 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 0)
  have h6 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 2)
  have h7 := congrFun (h.steinberg 0 2 3 (by decide) (by decide) (by decide)) (ix 0)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7

private theorem cert_1_3_6 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 3 (witness (fun i j s => x i j (ix s))) 6 -
      witness (fun i j s => x i j (ix s)) 6 = x 1 3 (ix 6) := by
  have h0 := congrFun (h.square 0 1) (ix 3)
  have h1 := congrFun (h.commute 0 1 2 3 (by decide) (by decide)) (ix 8)
  have h2 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 h1 h2 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2

private theorem cert_1_3_7 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 3 (witness (fun i j s => x i j (ix s))) 7 -
      witness (fun i j s => x i j (ix s)) 7 = x 1 3 (ix 7) := by
  have h0 := congrFun (h.commute 0 2 1 3 (by decide) (by decide)) (ix 2)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_3_8 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 3 (witness (fun i j s => x i j (ix s))) 8 -
      witness (fun i j s => x i j (ix s)) 8 = x 1 3 (ix 8) := by
  have h0 := congrFun (h.commute 0 2 1 3 (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_3_9 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 3 (witness (fun i j s => x i j (ix s))) 9 -
      witness (fun i j s => x i j (ix s)) 9 = x 1 3 (ix 9) := by
  have h0 := congrFun (h.commute 0 3 1 3 (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_4_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 4 (witness (fun i j s => x i j (ix s))) 0 -
      witness (fun i j s => x i j (ix s)) 0 = x 1 4 (ix 0) := by
  have h0 := congrFun (h.square 0 1) (ix 3)
  have h1 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 1)
  have h2 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 3)
  have h3 := congrFun (h.commute 0 1 2 4 (by decide) (by decide)) (ix 1)
  have h4 := congrFun (h.commute 0 1 3 2 (by decide) (by decide)) (ix 9)
  have h5 := congrFun (h.steinberg 0 1 4 (by decide) (by decide) (by decide)) (ix 0)
  have h6 := congrFun (h.steinberg 0 1 4 (by decide) (by decide) (by decide)) (ix 3)
  have h7 := congrFun (h.steinberg 0 2 4 (by decide) (by decide) (by decide)) (ix 0)
  have h8 := congrFun (h.steinberg 1 0 4 (by decide) (by decide) (by decide)) (ix 0)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8

private theorem cert_1_4_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 4 (witness (fun i j s => x i j (ix s))) 1 -
      witness (fun i j s => x i j (ix s)) 1 = x 1 4 (ix 1) := by
  have h0 := congrFun (h.commute 1 0 1 4 (by decide) (by decide)) (ix 4)
  have h1 := congrFun (h.commute 1 0 3 2 (by decide) (by decide)) (ix 9)
  simp [act, source, witness, action_coord] at h0 h1 ⊢
  linear_combination (norm := square_ring) h0 + h1

private theorem cert_1_4_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 4 (witness (fun i j s => x i j (ix s))) 2 -
      witness (fun i j s => x i j (ix s)) 2 = x 1 4 (ix 2) := by
  have h0 := congrFun (h.commute 1 0 1 4 (by decide) (by decide)) (ix 5)
  have h1 := congrFun (h.commute 1 0 2 3 (by decide) (by decide)) (ix 8)
  simp [act, source, witness, action_coord] at h0 h1 ⊢
  linear_combination (norm := square_ring) h0 + h1

private theorem cert_1_4_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 4 (witness (fun i j s => x i j (ix s))) 3 -
      witness (fun i j s => x i j (ix s)) 3 = x 1 4 (ix 3) := by
  have h0 := congrFun (h.commute 1 0 1 4 (by decide) (by decide)) (ix 6)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_4_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 4 (witness (fun i j s => x i j (ix s))) 4 -
      witness (fun i j s => x i j (ix s)) 4 = x 1 4 (ix 4) := by
  have h0 := congrFun (h.commute 0 2 1 4 (by decide) (by decide)) (ix 0)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_4_5 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 4 (witness (fun i j s => x i j (ix s))) 5 -
      witness (fun i j s => x i j (ix s)) 5 = x 1 4 (ix 5) := by
  have h0 := congrFun (h.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_4_6 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 4 (witness (fun i j s => x i j (ix s))) 6 -
      witness (fun i j s => x i j (ix s)) 6 = x 1 4 (ix 6) := by
  have h0 := congrFun (h.square 0 1) (ix 3)
  have h1 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 1)
  have h2 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 3)
  have h3 := congrFun (h.commute 0 1 2 4 (by decide) (by decide)) (ix 1)
  have h4 := congrFun (h.commute 0 1 3 2 (by decide) (by decide)) (ix 9)
  have h5 := congrFun (h.steinberg 0 1 4 (by decide) (by decide) (by decide)) (ix 0)
  have h6 := congrFun (h.steinberg 0 1 4 (by decide) (by decide) (by decide)) (ix 3)
  have h7 := congrFun (h.steinberg 0 2 4 (by decide) (by decide) (by decide)) (ix 0)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7

private theorem cert_1_4_7 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 4 (witness (fun i j s => x i j (ix s))) 7 -
      witness (fun i j s => x i j (ix s)) 7 = x 1 4 (ix 7) := by
  have h0 := congrFun (h.commute 0 2 1 4 (by decide) (by decide)) (ix 2)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_4_8 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 4 (witness (fun i j s => x i j (ix s))) 8 -
      witness (fun i j s => x i j (ix s)) 8 = x 1 4 (ix 8) := by
  have h0 := congrFun (h.commute 0 2 1 4 (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_1_4_9 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 1 4 (witness (fun i j s => x i j (ix s))) 9 -
      witness (fun i j s => x i j (ix s)) 9 = x 1 4 (ix 9) := by
  have h0 := congrFun (h.commute 0 3 1 4 (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_0_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 0 (witness (fun i j s => x i j (ix s))) 0 -
      witness (fun i j s => x i j (ix s)) 0 = x 2 0 (ix 0) := by
  have h0 := congrFun (h.square 2 0) (ix 4)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_0_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 0 (witness (fun i j s => x i j (ix s))) 1 -
      witness (fun i j s => x i j (ix s)) 1 = x 2 0 (ix 1) := by
  have h0 := congrFun (h.square 0 1) (ix 1)
  have h1 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h2 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 0)
  have h3 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 1)
  have h4 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
  have h5 := congrFun (h.commute 0 2 3 1 (by decide) (by decide)) (ix 2)
  have h6 := congrFun (h.steinberg 0 3 1 (by decide) (by decide) (by decide)) (ix 1)
  have h7 := congrFun (h.commute 1 0 2 0 (by decide) (by decide)) (ix 4)
  have h8 := congrFun (h.steinberg 1 0 2 (by decide) (by decide) (by decide)) (ix 0)
  have h9 := congrFun (h.steinberg 1 2 0 (by decide) (by decide) (by decide)) (ix 4)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8 + h9

private theorem cert_2_0_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 0 (witness (fun i j s => x i j (ix s))) 2 -
      witness (fun i j s => x i j (ix s)) 2 = x 2 0 (ix 2) := by
  have h0 := congrFun (h.commute 1 0 2 0 (by decide) (by decide)) (ix 5)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_0_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 0 (witness (fun i j s => x i j (ix s))) 3 -
      witness (fun i j s => x i j (ix s)) 3 = x 2 0 (ix 3) := by
  have h0 := congrFun (h.commute 1 0 2 0 (by decide) (by decide)) (ix 6)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_0_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (_h : ElementaryRelations 2 x) :
    act 2 0 (witness (fun i j s => x i j (ix s))) 4 -
      witness (fun i j s => x i j (ix s)) 4 = x 2 0 (ix 4) := by
  simp [act, source, witness]

private theorem cert_2_0_5 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 0 (witness (fun i j s => x i j (ix s))) 5 -
      witness (fun i j s => x i j (ix s)) 5 = x 2 0 (ix 5) := by
  have h0 := congrFun (h.commute 2 0 4 1 (by decide) (by decide)) (ix 9)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_0_6 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 0 (witness (fun i j s => x i j (ix s))) 6 -
      witness (fun i j s => x i j (ix s)) 6 = x 2 0 (ix 6) := by
  have h0 := congrFun (h.commute 2 0 3 1 (by decide) (by decide)) (ix 9)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_0_7 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 0 (witness (fun i j s => x i j (ix s))) 7 -
      witness (fun i j s => x i j (ix s)) 7 = x 2 0 (ix 7) := by
  have h0 := congrFun (h.commute 0 2 1 2 (by decide) (by decide)) (ix 2)
  have h1 := congrFun (h.commute 1 0 1 2 (by decide) (by decide)) (ix 5)
  have h2 := congrFun (h.commute 1 0 4 2 (by decide) (by decide)) (ix 9)
  have h3 := congrFun (h.steinberg 1 2 0 (by decide) (by decide) (by decide)) (ix 5)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3

private theorem cert_2_0_8 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 0 (witness (fun i j s => x i j (ix s))) 8 -
      witness (fun i j s => x i j (ix s)) 8 = x 2 0 (ix 8) := by
  have h0 := congrFun (h.commute 0 2 1 2 (by decide) (by decide)) (ix 3)
  have h1 := congrFun (h.commute 1 0 1 2 (by decide) (by decide)) (ix 6)
  have h2 := congrFun (h.commute 1 0 3 2 (by decide) (by decide)) (ix 9)
  have h3 := congrFun (h.steinberg 1 2 0 (by decide) (by decide) (by decide)) (ix 6)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3

private theorem cert_2_0_9 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 0 (witness (fun i j s => x i j (ix s))) 9 -
      witness (fun i j s => x i j (ix s)) 9 = x 2 0 (ix 9) := by
  have h0 := congrFun (h.commute 1 3 2 0 (by decide) (by decide)) (ix 6)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_1_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 1 (witness (fun i j s => x i j (ix s))) 0 -
      witness (fun i j s => x i j (ix s)) 0 = x 2 1 (ix 0) := by
  have h0 := congrFun (h.commute 2 0 2 1 (by decide) (by decide)) (ix 4)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_1_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 1 (witness (fun i j s => x i j (ix s))) 1 -
      witness (fun i j s => x i j (ix s)) 1 = x 2 1 (ix 1) := by
  have h0 := congrFun (h.commute 0 1 2 1 (by decide) (by decide)) (ix 1)
  have h1 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h2 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
  have h3 := congrFun (h.commute 0 2 3 1 (by decide) (by decide)) (ix 2)
  have h4 := congrFun (h.steinberg 0 2 1 (by decide) (by decide) (by decide)) (ix 1)
  have h5 := congrFun (h.steinberg 0 3 1 (by decide) (by decide) (by decide)) (ix 1)
  have h6 := congrFun (h.steinberg 2 0 1 (by decide) (by decide) (by decide)) (ix 1)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 h6 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5 + h6

private theorem cert_2_1_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 1 (witness (fun i j s => x i j (ix s))) 2 -
      witness (fun i j s => x i j (ix s)) 2 = x 2 1 (ix 2) := by
  have h0 := congrFun (h.commute 2 0 2 1 (by decide) (by decide)) (ix 7)
  have h1 := congrFun (h.commute 2 0 4 1 (by decide) (by decide)) (ix 9)
  simp [act, source, witness, action_coord] at h0 h1 ⊢
  linear_combination (norm := square_ring) h0 + h1

private theorem cert_2_1_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 1 (witness (fun i j s => x i j (ix s))) 3 -
      witness (fun i j s => x i j (ix s)) 3 = x 2 1 (ix 3) := by
  have h0 := congrFun (h.commute 2 0 2 1 (by decide) (by decide)) (ix 8)
  have h1 := congrFun (h.commute 2 0 3 1 (by decide) (by decide)) (ix 9)
  simp [act, source, witness, action_coord] at h0 h1 ⊢
  linear_combination (norm := square_ring) h0 + h1

private theorem cert_2_1_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 1 (witness (fun i j s => x i j (ix s))) 4 -
      witness (fun i j s => x i j (ix s)) 4 = x 2 1 (ix 4) := by
  have h0 := congrFun (h.commute 0 1 2 1 (by decide) (by decide)) (ix 1)
  have h1 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h2 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
  have h3 := congrFun (h.commute 0 2 3 1 (by decide) (by decide)) (ix 2)
  have h4 := congrFun (h.steinberg 0 2 1 (by decide) (by decide) (by decide)) (ix 1)
  have h5 := congrFun (h.steinberg 0 3 1 (by decide) (by decide) (by decide)) (ix 1)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5

private theorem cert_2_1_5 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 1 (witness (fun i j s => x i j (ix s))) 5 -
      witness (fun i j s => x i j (ix s)) 5 = x 2 1 (ix 5) := by
  have h0 := congrFun (h.commute 0 1 2 1 (by decide) (by decide)) (ix 2)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_1_6 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 1 (witness (fun i j s => x i j (ix s))) 6 -
      witness (fun i j s => x i j (ix s)) 6 = x 2 1 (ix 6) := by
  have h0 := congrFun (h.commute 0 1 2 1 (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_1_7 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 1 (witness (fun i j s => x i j (ix s))) 7 -
      witness (fun i j s => x i j (ix s)) 7 = x 2 1 (ix 7) := by
  have h0 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h1 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 5)
  have h2 := congrFun (h.steinberg 0 2 1 (by decide) (by decide) (by decide)) (ix 2)
  simp [act, source, witness, action_coord] at h0 h1 h2 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2

private theorem cert_2_1_8 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 1 (witness (fun i j s => x i j (ix s))) 8 -
      witness (fun i j s => x i j (ix s)) 8 = x 2 1 (ix 8) := by
  have h0 := congrFun (h.commute 0 1 3 2 (by decide) (by decide)) (ix 9)
  have h1 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 6)
  have h2 := congrFun (h.steinberg 0 2 1 (by decide) (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 h1 h2 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2

private theorem cert_2_1_9 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 1 (witness (fun i j s => x i j (ix s))) 9 -
      witness (fun i j s => x i j (ix s)) 9 = x 2 1 (ix 9) := by
  have h0 := congrFun (h.commute 0 3 2 1 (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_2_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 2 (witness (fun i j s => x i j (ix s))) 0 -
      witness (fun i j s => x i j (ix s)) 0 = x 2 2 (ix 0) := by
  have h0 := congrFun (h.diagonal 2) (ix 0)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_2_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 2 (witness (fun i j s => x i j (ix s))) 1 -
      witness (fun i j s => x i j (ix s)) 1 = x 2 2 (ix 1) := by
  have h0 := congrFun (h.diagonal 2) (ix 1)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_2_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 2 (witness (fun i j s => x i j (ix s))) 2 -
      witness (fun i j s => x i j (ix s)) 2 = x 2 2 (ix 2) := by
  have h0 := congrFun (h.diagonal 2) (ix 2)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_2_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 2 (witness (fun i j s => x i j (ix s))) 3 -
      witness (fun i j s => x i j (ix s)) 3 = x 2 2 (ix 3) := by
  have h0 := congrFun (h.diagonal 2) (ix 3)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_2_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 2 (witness (fun i j s => x i j (ix s))) 4 -
      witness (fun i j s => x i j (ix s)) 4 = x 2 2 (ix 4) := by
  have h0 := congrFun (h.diagonal 2) (ix 4)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_2_5 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 2 (witness (fun i j s => x i j (ix s))) 5 -
      witness (fun i j s => x i j (ix s)) 5 = x 2 2 (ix 5) := by
  have h0 := congrFun (h.diagonal 2) (ix 5)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_2_6 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 2 (witness (fun i j s => x i j (ix s))) 6 -
      witness (fun i j s => x i j (ix s)) 6 = x 2 2 (ix 6) := by
  have h0 := congrFun (h.diagonal 2) (ix 6)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_2_7 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 2 (witness (fun i j s => x i j (ix s))) 7 -
      witness (fun i j s => x i j (ix s)) 7 = x 2 2 (ix 7) := by
  have h0 := congrFun (h.diagonal 2) (ix 7)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_2_8 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 2 (witness (fun i j s => x i j (ix s))) 8 -
      witness (fun i j s => x i j (ix s)) 8 = x 2 2 (ix 8) := by
  have h0 := congrFun (h.diagonal 2) (ix 8)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_2_9 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 2 (witness (fun i j s => x i j (ix s))) 9 -
      witness (fun i j s => x i j (ix s)) 9 = x 2 2 (ix 9) := by
  have h0 := congrFun (h.diagonal 2) (ix 9)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_3_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 3 (witness (fun i j s => x i j (ix s))) 0 -
      witness (fun i j s => x i j (ix s)) 0 = x 2 3 (ix 0) := by
  have h0 := congrFun (h.commute 2 0 2 3 (by decide) (by decide)) (ix 4)
  have h1 := congrFun (h.commute 2 0 4 1 (by decide) (by decide)) (ix 9)
  simp [act, source, witness, action_coord] at h0 h1 ⊢
  linear_combination (norm := square_ring) h0 + h1

private theorem cert_2_3_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 3 (witness (fun i j s => x i j (ix s))) 1 -
      witness (fun i j s => x i j (ix s)) 1 = x 2 3 (ix 1) := by
  have h0 := congrFun (h.commute 1 0 2 3 (by decide) (by decide)) (ix 4)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_3_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 3 (witness (fun i j s => x i j (ix s))) 2 -
      witness (fun i j s => x i j (ix s)) 2 = x 2 3 (ix 2) := by
  have h0 := congrFun (h.commute 1 0 2 3 (by decide) (by decide)) (ix 5)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_3_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 3 (witness (fun i j s => x i j (ix s))) 3 -
      witness (fun i j s => x i j (ix s)) 3 = x 2 3 (ix 3) := by
  have h0 := congrFun (h.commute 1 0 2 3 (by decide) (by decide)) (ix 6)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_3_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 3 (witness (fun i j s => x i j (ix s))) 4 -
      witness (fun i j s => x i j (ix s)) 4 = x 2 3 (ix 4) := by
  have h0 := congrFun (h.commute 0 1 2 3 (by decide) (by decide)) (ix 1)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_3_5 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 3 (witness (fun i j s => x i j (ix s))) 5 -
      witness (fun i j s => x i j (ix s)) 5 = x 2 3 (ix 5) := by
  have h0 := congrFun (h.commute 0 1 2 3 (by decide) (by decide)) (ix 2)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_3_6 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 3 (witness (fun i j s => x i j (ix s))) 6 -
      witness (fun i j s => x i j (ix s)) 6 = x 2 3 (ix 6) := by
  have h0 := congrFun (h.commute 0 1 2 3 (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_3_7 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 3 (witness (fun i j s => x i j (ix s))) 7 -
      witness (fun i j s => x i j (ix s)) 7 = x 2 3 (ix 7) := by
  have h0 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 1)
  have h1 := congrFun (h.commute 0 1 2 3 (by decide) (by decide)) (ix 1)
  have h2 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h3 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 5)
  have h4 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 0)
  have h5 := congrFun (h.steinberg 0 2 3 (by decide) (by decide) (by decide)) (ix 0)
  have h6 := congrFun (h.steinberg 0 2 3 (by decide) (by decide) (by decide)) (ix 2)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 h6 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5 + h6

private theorem cert_2_3_8 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 3 (witness (fun i j s => x i j (ix s))) 8 -
      witness (fun i j s => x i j (ix s)) 8 = x 2 3 (ix 8) := by
  have h0 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 3)
  have h1 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 6)
  have h2 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 9)
  have h3 := congrFun (h.steinberg 0 2 3 (by decide) (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3

private theorem cert_2_3_9 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 3 (witness (fun i j s => x i j (ix s))) 9 -
      witness (fun i j s => x i j (ix s)) 9 = x 2 3 (ix 9) := by
  have h0 := congrFun (h.commute 0 3 2 3 (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_4_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 4 (witness (fun i j s => x i j (ix s))) 0 -
      witness (fun i j s => x i j (ix s)) 0 = x 2 4 (ix 0) := by
  have h0 := congrFun (h.commute 2 0 2 4 (by decide) (by decide)) (ix 4)
  have h1 := congrFun (h.commute 2 0 3 1 (by decide) (by decide)) (ix 9)
  simp [act, source, witness, action_coord] at h0 h1 ⊢
  linear_combination (norm := square_ring) h0 + h1

private theorem cert_2_4_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 4 (witness (fun i j s => x i j (ix s))) 1 -
      witness (fun i j s => x i j (ix s)) 1 = x 2 4 (ix 1) := by
  have h0 := congrFun (h.commute 1 0 2 4 (by decide) (by decide)) (ix 4)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_4_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 4 (witness (fun i j s => x i j (ix s))) 2 -
      witness (fun i j s => x i j (ix s)) 2 = x 2 4 (ix 2) := by
  have h0 := congrFun (h.commute 1 0 2 4 (by decide) (by decide)) (ix 5)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_4_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 4 (witness (fun i j s => x i j (ix s))) 3 -
      witness (fun i j s => x i j (ix s)) 3 = x 2 4 (ix 3) := by
  have h0 := congrFun (h.commute 1 0 2 4 (by decide) (by decide)) (ix 6)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_4_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 4 (witness (fun i j s => x i j (ix s))) 4 -
      witness (fun i j s => x i j (ix s)) 4 = x 2 4 (ix 4) := by
  have h0 := congrFun (h.commute 0 1 2 4 (by decide) (by decide)) (ix 1)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_4_5 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 4 (witness (fun i j s => x i j (ix s))) 5 -
      witness (fun i j s => x i j (ix s)) 5 = x 2 4 (ix 5) := by
  have h0 := congrFun (h.commute 0 1 2 4 (by decide) (by decide)) (ix 2)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_4_6 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 4 (witness (fun i j s => x i j (ix s))) 6 -
      witness (fun i j s => x i j (ix s)) 6 = x 2 4 (ix 6) := by
  have h0 := congrFun (h.commute 0 1 2 4 (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_2_4_7 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 4 (witness (fun i j s => x i j (ix s))) 7 -
      witness (fun i j s => x i j (ix s)) 7 = x 2 4 (ix 7) := by
  have h0 := congrFun (h.square 0 1) (ix 2)
  have h1 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 2)
  have h2 := congrFun (h.commute 0 1 2 3 (by decide) (by decide)) (ix 8)
  have h3 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 5)
  have h4 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 9)
  have h5 := congrFun (h.steinberg 0 1 4 (by decide) (by decide) (by decide)) (ix 2)
  have h6 := congrFun (h.steinberg 0 2 4 (by decide) (by decide) (by decide)) (ix 2)
  have h7 := congrFun (h.commute 0 3 1 4 (by decide) (by decide)) (ix 0)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7

private theorem cert_2_4_8 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 4 (witness (fun i j s => x i j (ix s))) 8 -
      witness (fun i j s => x i j (ix s)) 8 = x 2 4 (ix 8) := by
  have h0 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 1)
  have h1 := congrFun (h.commute 0 1 2 4 (by decide) (by decide)) (ix 1)
  have h2 := congrFun (h.commute 0 1 3 2 (by decide) (by decide)) (ix 9)
  have h3 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 6)
  have h4 := congrFun (h.steinberg 0 1 4 (by decide) (by decide) (by decide)) (ix 0)
  have h5 := congrFun (h.steinberg 0 2 4 (by decide) (by decide) (by decide)) (ix 0)
  have h6 := congrFun (h.steinberg 0 2 4 (by decide) (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 h6 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5 + h6

private theorem cert_2_4_9 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 2 4 (witness (fun i j s => x i j (ix s))) 9 -
      witness (fun i j s => x i j (ix s)) 9 = x 2 4 (ix 9) := by
  have h0 := congrFun (h.commute 0 3 2 4 (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_0_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 0 (witness (fun i j s => x i j (ix s))) 0 -
      witness (fun i j s => x i j (ix s)) 0 = x 3 0 (ix 0) := by
  have h0 := congrFun (h.commute 2 0 3 0 (by decide) (by decide)) (ix 4)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_0_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 0 (witness (fun i j s => x i j (ix s))) 1 -
      witness (fun i j s => x i j (ix s)) 1 = x 3 0 (ix 1) := by
  have h0 := congrFun (h.commute 1 0 3 0 (by decide) (by decide)) (ix 4)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_0_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 0 (witness (fun i j s => x i j (ix s))) 2 -
      witness (fun i j s => x i j (ix s)) 2 = x 3 0 (ix 2) := by
  have h0 := congrFun (h.square 0 1) (ix 1)
  have h1 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h2 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 0)
  have h3 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 1)
  have h4 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
  have h5 := congrFun (h.commute 0 2 3 1 (by decide) (by decide)) (ix 2)
  have h6 := congrFun (h.steinberg 0 3 1 (by decide) (by decide) (by decide)) (ix 1)
  have h7 := congrFun (h.commute 1 0 3 0 (by decide) (by decide)) (ix 5)
  have h8 := congrFun (h.steinberg 1 0 2 (by decide) (by decide) (by decide)) (ix 0)
  have h9 := congrFun (h.steinberg 1 2 0 (by decide) (by decide) (by decide)) (ix 4)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8 + h9

private theorem cert_3_0_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 0 (witness (fun i j s => x i j (ix s))) 3 -
      witness (fun i j s => x i j (ix s)) 3 = x 3 0 (ix 3) := by
  have h0 := congrFun (h.commute 1 0 3 0 (by decide) (by decide)) (ix 6)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_0_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 0 (witness (fun i j s => x i j (ix s))) 4 -
      witness (fun i j s => x i j (ix s)) 4 = x 3 0 (ix 4) := by
  have h0 := congrFun (h.commute 3 0 4 1 (by decide) (by decide)) (ix 8)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_0_5 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 0 (witness (fun i j s => x i j (ix s))) 5 -
      witness (fun i j s => x i j (ix s)) 5 = x 3 0 (ix 5) := by
  have h0 := congrFun (h.commute 0 1 2 1 (by decide) (by decide)) (ix 1)
  have h1 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h2 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
  have h3 := congrFun (h.commute 0 2 3 1 (by decide) (by decide)) (ix 2)
  have h4 := congrFun (h.steinberg 0 2 1 (by decide) (by decide) (by decide)) (ix 1)
  have h5 := congrFun (h.steinberg 0 3 1 (by decide) (by decide) (by decide)) (ix 1)
  have h6 := congrFun (h.steinberg 2 0 1 (by decide) (by decide) (by decide)) (ix 1)
  have h7 := congrFun (h.commute 2 1 3 0 (by decide) (by decide)) (ix 7)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7

private theorem cert_3_0_6 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 0 (witness (fun i j s => x i j (ix s))) 6 -
      witness (fun i j s => x i j (ix s)) 6 = x 3 0 (ix 6) := by
  have h0 := congrFun (h.commute 2 1 3 0 (by decide) (by decide)) (ix 8)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_0_7 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 0 (witness (fun i j s => x i j (ix s))) 7 -
      witness (fun i j s => x i j (ix s)) 7 = x 3 0 (ix 7) := by
  have h0 := congrFun (h.square 0 1) (ix 1)
  have h1 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h2 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 0)
  have h3 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 1)
  have h4 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
  have h5 := congrFun (h.commute 0 2 3 1 (by decide) (by decide)) (ix 2)
  have h6 := congrFun (h.steinberg 0 3 1 (by decide) (by decide) (by decide)) (ix 1)
  have h7 := congrFun (h.steinberg 1 0 2 (by decide) (by decide) (by decide)) (ix 0)
  have h8 := congrFun (h.commute 1 2 3 0 (by decide) (by decide)) (ix 5)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8

private theorem cert_3_0_8 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 0 (witness (fun i j s => x i j (ix s))) 8 -
      witness (fun i j s => x i j (ix s)) 8 = x 3 0 (ix 8) := by
  have h0 := congrFun (h.commute 1 2 3 0 (by decide) (by decide)) (ix 6)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_0_9 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 0 (witness (fun i j s => x i j (ix s))) 9 -
      witness (fun i j s => x i j (ix s)) 9 = x 3 0 (ix 9) := by
  have h0 := congrFun (h.commute 0 3 1 3 (by decide) (by decide)) (ix 3)
  have h1 := congrFun (h.commute 1 0 1 3 (by decide) (by decide)) (ix 6)
  have h2 := congrFun (h.commute 1 0 2 3 (by decide) (by decide)) (ix 8)
  have h3 := congrFun (h.steinberg 1 3 0 (by decide) (by decide) (by decide)) (ix 6)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3

private theorem cert_3_1_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 1 (witness (fun i j s => x i j (ix s))) 0 -
      witness (fun i j s => x i j (ix s)) 0 = x 3 1 (ix 0) := by
  have h0 := congrFun (h.commute 2 0 3 1 (by decide) (by decide)) (ix 4)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_1_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 1 (witness (fun i j s => x i j (ix s))) 1 -
      witness (fun i j s => x i j (ix s)) 1 = x 3 1 (ix 1) := by
  have h0 := congrFun (h.commute 3 0 3 1 (by decide) (by decide)) (ix 7)
  have h1 := congrFun (h.commute 3 0 4 1 (by decide) (by decide)) (ix 8)
  simp [act, source, witness, action_coord] at h0 h1 ⊢
  linear_combination (norm := square_ring) h0 + h1

private theorem cert_3_1_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 1 (witness (fun i j s => x i j (ix s))) 2 -
      witness (fun i j s => x i j (ix s)) 2 = x 3 1 (ix 2) := by
  have h0 := congrFun (h.commute 2 0 3 1 (by decide) (by decide)) (ix 7)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_1_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 1 (witness (fun i j s => x i j (ix s))) 3 -
      witness (fun i j s => x i j (ix s)) 3 = x 3 1 (ix 3) := by
  have h0 := congrFun (h.commute 2 0 3 1 (by decide) (by decide)) (ix 8)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_1_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 1 (witness (fun i j s => x i j (ix s))) 4 -
      witness (fun i j s => x i j (ix s)) 4 = x 3 1 (ix 4) := by
  have h0 := congrFun (h.commute 0 1 3 1 (by decide) (by decide)) (ix 1)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_1_5 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 1 (witness (fun i j s => x i j (ix s))) 5 -
      witness (fun i j s => x i j (ix s)) 5 = x 3 1 (ix 5) := by
  have h0 := congrFun (h.commute 0 1 3 1 (by decide) (by decide)) (ix 2)
  have h1 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h2 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
  have h3 := congrFun (h.commute 0 2 3 1 (by decide) (by decide)) (ix 2)
  have h4 := congrFun (h.steinberg 0 2 1 (by decide) (by decide) (by decide)) (ix 1)
  have h5 := congrFun (h.steinberg 0 3 1 (by decide) (by decide) (by decide)) (ix 1)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5

private theorem cert_3_1_6 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 1 (witness (fun i j s => x i j (ix s))) 6 -
      witness (fun i j s => x i j (ix s)) 6 = x 3 1 (ix 6) := by
  have h0 := congrFun (h.commute 0 1 3 1 (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_1_7 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 1 (witness (fun i j s => x i j (ix s))) 7 -
      witness (fun i j s => x i j (ix s)) 7 = x 3 1 (ix 7) := by
  have h0 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h1 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
  have h2 := congrFun (h.steinberg 0 3 1 (by decide) (by decide) (by decide)) (ix 1)
  simp [act, source, witness, action_coord] at h0 h1 h2 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2

private theorem cert_3_1_8 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 1 (witness (fun i j s => x i j (ix s))) 8 -
      witness (fun i j s => x i j (ix s)) 8 = x 3 1 (ix 8) := by
  have h0 := congrFun (h.commute 0 2 3 1 (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_1_9 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 1 (witness (fun i j s => x i j (ix s))) 9 -
      witness (fun i j s => x i j (ix s)) 9 = x 3 1 (ix 9) := by
  have h0 := congrFun (h.commute 0 1 2 3 (by decide) (by decide)) (ix 8)
  have h1 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 6)
  have h2 := congrFun (h.steinberg 0 3 1 (by decide) (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 h1 h2 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2

private theorem cert_3_2_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 2 (witness (fun i j s => x i j (ix s))) 0 -
      witness (fun i j s => x i j (ix s)) 0 = x 3 2 (ix 0) := by
  have h0 := congrFun (h.commute 3 0 3 2 (by decide) (by decide)) (ix 5)
  have h1 := congrFun (h.commute 3 0 4 1 (by decide) (by decide)) (ix 8)
  simp [act, source, witness, action_coord] at h0 h1 ⊢
  linear_combination (norm := square_ring) h0 + h1

private theorem cert_3_2_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 2 (witness (fun i j s => x i j (ix s))) 1 -
      witness (fun i j s => x i j (ix s)) 1 = x 3 2 (ix 1) := by
  have h0 := congrFun (h.commute 1 0 3 2 (by decide) (by decide)) (ix 4)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_2_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 2 (witness (fun i j s => x i j (ix s))) 2 -
      witness (fun i j s => x i j (ix s)) 2 = x 3 2 (ix 2) := by
  have h0 := congrFun (h.commute 1 0 3 2 (by decide) (by decide)) (ix 5)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_2_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 2 (witness (fun i j s => x i j (ix s))) 3 -
      witness (fun i j s => x i j (ix s)) 3 = x 3 2 (ix 3) := by
  have h0 := congrFun (h.commute 1 0 3 2 (by decide) (by decide)) (ix 6)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_2_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 2 (witness (fun i j s => x i j (ix s))) 4 -
      witness (fun i j s => x i j (ix s)) 4 = x 3 2 (ix 4) := by
  have h0 := congrFun (h.commute 0 1 3 2 (by decide) (by decide)) (ix 1)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_2_5 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 2 (witness (fun i j s => x i j (ix s))) 5 -
      witness (fun i j s => x i j (ix s)) 5 = x 3 2 (ix 5) := by
  have h0 := congrFun (h.commute 0 1 3 2 (by decide) (by decide)) (ix 2)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_2_6 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 2 (witness (fun i j s => x i j (ix s))) 6 -
      witness (fun i j s => x i j (ix s)) 6 = x 3 2 (ix 6) := by
  have h0 := congrFun (h.commute 0 1 3 2 (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_2_7 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 2 (witness (fun i j s => x i j (ix s))) 7 -
      witness (fun i j s => x i j (ix s)) 7 = x 3 2 (ix 7) := by
  have h0 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h1 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 0)
  have h2 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
  have h3 := congrFun (h.commute 0 2 3 1 (by decide) (by decide)) (ix 2)
  have h4 := congrFun (h.commute 0 2 3 2 (by decide) (by decide)) (ix 2)
  have h5 := congrFun (h.steinberg 0 3 1 (by decide) (by decide) (by decide)) (ix 1)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5

private theorem cert_3_2_8 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 2 (witness (fun i j s => x i j (ix s))) 8 -
      witness (fun i j s => x i j (ix s)) 8 = x 3 2 (ix 8) := by
  have h0 := congrFun (h.commute 0 2 3 2 (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_2_9 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 2 (witness (fun i j s => x i j (ix s))) 9 -
      witness (fun i j s => x i j (ix s)) 9 = x 3 2 (ix 9) := by
  have h0 := congrFun (h.commute 0 1 0 3 (by decide) (by decide)) (ix 3)
  have h1 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 6)
  have h2 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 8)
  have h3 := congrFun (h.steinberg 0 3 2 (by decide) (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3

private theorem cert_3_3_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 3 (witness (fun i j s => x i j (ix s))) 0 -
      witness (fun i j s => x i j (ix s)) 0 = x 3 3 (ix 0) := by
  have h0 := congrFun (h.diagonal 3) (ix 0)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_3_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 3 (witness (fun i j s => x i j (ix s))) 1 -
      witness (fun i j s => x i j (ix s)) 1 = x 3 3 (ix 1) := by
  have h0 := congrFun (h.diagonal 3) (ix 1)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_3_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 3 (witness (fun i j s => x i j (ix s))) 2 -
      witness (fun i j s => x i j (ix s)) 2 = x 3 3 (ix 2) := by
  have h0 := congrFun (h.diagonal 3) (ix 2)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_3_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 3 (witness (fun i j s => x i j (ix s))) 3 -
      witness (fun i j s => x i j (ix s)) 3 = x 3 3 (ix 3) := by
  have h0 := congrFun (h.diagonal 3) (ix 3)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_3_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 3 (witness (fun i j s => x i j (ix s))) 4 -
      witness (fun i j s => x i j (ix s)) 4 = x 3 3 (ix 4) := by
  have h0 := congrFun (h.diagonal 3) (ix 4)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_3_5 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 3 (witness (fun i j s => x i j (ix s))) 5 -
      witness (fun i j s => x i j (ix s)) 5 = x 3 3 (ix 5) := by
  have h0 := congrFun (h.diagonal 3) (ix 5)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_3_6 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 3 (witness (fun i j s => x i j (ix s))) 6 -
      witness (fun i j s => x i j (ix s)) 6 = x 3 3 (ix 6) := by
  have h0 := congrFun (h.diagonal 3) (ix 6)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_3_7 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 3 (witness (fun i j s => x i j (ix s))) 7 -
      witness (fun i j s => x i j (ix s)) 7 = x 3 3 (ix 7) := by
  have h0 := congrFun (h.diagonal 3) (ix 7)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_3_8 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 3 (witness (fun i j s => x i j (ix s))) 8 -
      witness (fun i j s => x i j (ix s)) 8 = x 3 3 (ix 8) := by
  have h0 := congrFun (h.diagonal 3) (ix 8)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_3_9 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 3 (witness (fun i j s => x i j (ix s))) 9 -
      witness (fun i j s => x i j (ix s)) 9 = x 3 3 (ix 9) := by
  have h0 := congrFun (h.diagonal 3) (ix 9)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_4_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 4 (witness (fun i j s => x i j (ix s))) 0 -
      witness (fun i j s => x i j (ix s)) 0 = x 3 4 (ix 0) := by
  have h0 := congrFun (h.commute 2 0 3 4 (by decide) (by decide)) (ix 4)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_4_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 4 (witness (fun i j s => x i j (ix s))) 1 -
      witness (fun i j s => x i j (ix s)) 1 = x 3 4 (ix 1) := by
  have h0 := congrFun (h.commute 1 0 3 4 (by decide) (by decide)) (ix 4)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_4_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 4 (witness (fun i j s => x i j (ix s))) 2 -
      witness (fun i j s => x i j (ix s)) 2 = x 3 4 (ix 2) := by
  have h0 := congrFun (h.commute 1 0 3 4 (by decide) (by decide)) (ix 5)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_4_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 4 (witness (fun i j s => x i j (ix s))) 3 -
      witness (fun i j s => x i j (ix s)) 3 = x 3 4 (ix 3) := by
  have h0 := congrFun (h.commute 1 0 3 4 (by decide) (by decide)) (ix 6)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_4_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 4 (witness (fun i j s => x i j (ix s))) 4 -
      witness (fun i j s => x i j (ix s)) 4 = x 3 4 (ix 4) := by
  have h0 := congrFun (h.commute 0 1 3 4 (by decide) (by decide)) (ix 1)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_4_5 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 4 (witness (fun i j s => x i j (ix s))) 5 -
      witness (fun i j s => x i j (ix s)) 5 = x 3 4 (ix 5) := by
  have h0 := congrFun (h.commute 0 1 3 4 (by decide) (by decide)) (ix 2)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_4_6 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 4 (witness (fun i j s => x i j (ix s))) 6 -
      witness (fun i j s => x i j (ix s)) 6 = x 3 4 (ix 6) := by
  have h0 := congrFun (h.commute 0 1 3 4 (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_4_7 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 4 (witness (fun i j s => x i j (ix s))) 7 -
      witness (fun i j s => x i j (ix s)) 7 = x 3 4 (ix 7) := by
  have h0 := congrFun (h.commute 0 2 3 4 (by decide) (by decide)) (ix 2)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_4_8 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 4 (witness (fun i j s => x i j (ix s))) 8 -
      witness (fun i j s => x i j (ix s)) 8 = x 3 4 (ix 8) := by
  have h0 := congrFun (h.commute 0 2 3 4 (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_3_4_9 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 3 4 (witness (fun i j s => x i j (ix s))) 9 -
      witness (fun i j s => x i j (ix s)) 9 = x 3 4 (ix 9) := by
  have h0 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 1)
  have h1 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 3)
  have h2 := congrFun (h.commute 0 1 0 3 (by decide) (by decide)) (ix 3)
  have h3 := congrFun (h.commute 0 1 2 4 (by decide) (by decide)) (ix 1)
  have h4 := congrFun (h.commute 0 1 3 2 (by decide) (by decide)) (ix 9)
  have h5 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 6)
  have h6 := congrFun (h.steinberg 0 1 4 (by decide) (by decide) (by decide)) (ix 0)
  have h7 := congrFun (h.steinberg 0 2 4 (by decide) (by decide) (by decide)) (ix 0)
  have h8 := congrFun (h.steinberg 0 3 4 (by decide) (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8

private theorem cert_4_0_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 0 (witness (fun i j s => x i j (ix s))) 0 -
      witness (fun i j s => x i j (ix s)) 0 = x 4 0 (ix 0) := by
  have h0 := congrFun (h.commute 2 0 4 0 (by decide) (by decide)) (ix 4)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_0_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 0 (witness (fun i j s => x i j (ix s))) 1 -
      witness (fun i j s => x i j (ix s)) 1 = x 4 0 (ix 1) := by
  have h0 := congrFun (h.commute 1 0 4 0 (by decide) (by decide)) (ix 4)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_0_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 0 (witness (fun i j s => x i j (ix s))) 2 -
      witness (fun i j s => x i j (ix s)) 2 = x 4 0 (ix 2) := by
  have h0 := congrFun (h.commute 1 0 4 0 (by decide) (by decide)) (ix 5)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_0_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 0 (witness (fun i j s => x i j (ix s))) 3 -
      witness (fun i j s => x i j (ix s)) 3 = x 4 0 (ix 3) := by
  have h0 := congrFun (h.square 0 1) (ix 1)
  have h1 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h2 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 0)
  have h3 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 1)
  have h4 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
  have h5 := congrFun (h.commute 0 2 3 1 (by decide) (by decide)) (ix 2)
  have h6 := congrFun (h.steinberg 0 3 1 (by decide) (by decide) (by decide)) (ix 1)
  have h7 := congrFun (h.commute 1 0 4 0 (by decide) (by decide)) (ix 6)
  have h8 := congrFun (h.steinberg 1 0 2 (by decide) (by decide) (by decide)) (ix 0)
  have h9 := congrFun (h.steinberg 1 2 0 (by decide) (by decide) (by decide)) (ix 4)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8 + h9

private theorem cert_4_0_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 0 (witness (fun i j s => x i j (ix s))) 4 -
      witness (fun i j s => x i j (ix s)) 4 = x 4 0 (ix 4) := by
  have h0 := congrFun (h.commute 3 1 4 0 (by decide) (by decide)) (ix 7)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_0_5 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 0 (witness (fun i j s => x i j (ix s))) 5 -
      witness (fun i j s => x i j (ix s)) 5 = x 4 0 (ix 5) := by
  have h0 := congrFun (h.commute 2 1 4 0 (by decide) (by decide)) (ix 7)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_0_6 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 0 (witness (fun i j s => x i j (ix s))) 6 -
      witness (fun i j s => x i j (ix s)) 6 = x 4 0 (ix 6) := by
  have h0 := congrFun (h.commute 0 1 2 1 (by decide) (by decide)) (ix 1)
  have h1 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h2 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
  have h3 := congrFun (h.commute 0 2 3 1 (by decide) (by decide)) (ix 2)
  have h4 := congrFun (h.steinberg 0 2 1 (by decide) (by decide) (by decide)) (ix 1)
  have h5 := congrFun (h.steinberg 0 3 1 (by decide) (by decide) (by decide)) (ix 1)
  have h6 := congrFun (h.steinberg 2 0 1 (by decide) (by decide) (by decide)) (ix 1)
  have h7 := congrFun (h.commute 2 1 4 0 (by decide) (by decide)) (ix 8)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7

private theorem cert_4_0_7 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 0 (witness (fun i j s => x i j (ix s))) 7 -
      witness (fun i j s => x i j (ix s)) 7 = x 4 0 (ix 7) := by
  have h0 := congrFun (h.commute 1 2 4 0 (by decide) (by decide)) (ix 5)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_0_8 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 0 (witness (fun i j s => x i j (ix s))) 8 -
      witness (fun i j s => x i j (ix s)) 8 = x 4 0 (ix 8) := by
  have h0 := congrFun (h.square 0 1) (ix 1)
  have h1 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h2 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 0)
  have h3 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 1)
  have h4 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
  have h5 := congrFun (h.commute 0 2 3 1 (by decide) (by decide)) (ix 2)
  have h6 := congrFun (h.steinberg 0 3 1 (by decide) (by decide) (by decide)) (ix 1)
  have h7 := congrFun (h.steinberg 1 0 2 (by decide) (by decide) (by decide)) (ix 0)
  have h8 := congrFun (h.commute 1 2 4 0 (by decide) (by decide)) (ix 6)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8

private theorem cert_4_0_9 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 0 (witness (fun i j s => x i j (ix s))) 9 -
      witness (fun i j s => x i j (ix s)) 9 = x 4 0 (ix 9) := by
  have h0 := congrFun (h.square 0 1) (ix 2)
  have h1 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 1)
  have h2 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 2)
  have h3 := congrFun (h.commute 0 1 2 3 (by decide) (by decide)) (ix 1)
  have h4 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h5 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 0)
  have h6 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 2)
  have h7 := congrFun (h.steinberg 0 2 3 (by decide) (by decide) (by decide)) (ix 0)
  have h8 := congrFun (h.steinberg 1 0 3 (by decide) (by decide) (by decide)) (ix 0)
  have h9 := congrFun (h.commute 1 3 4 0 (by decide) (by decide)) (ix 6)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5 + h6 + h7 + h8 + h9

private theorem cert_4_1_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 1 (witness (fun i j s => x i j (ix s))) 0 -
      witness (fun i j s => x i j (ix s)) 0 = x 4 1 (ix 0) := by
  have h0 := congrFun (h.commute 2 0 4 1 (by decide) (by decide)) (ix 4)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_1_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 1 (witness (fun i j s => x i j (ix s))) 1 -
      witness (fun i j s => x i j (ix s)) 1 = x 4 1 (ix 1) := by
  have h0 := congrFun (h.commute 3 0 4 1 (by decide) (by decide)) (ix 7)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_1_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 1 (witness (fun i j s => x i j (ix s))) 2 -
      witness (fun i j s => x i j (ix s)) 2 = x 4 1 (ix 2) := by
  have h0 := congrFun (h.commute 2 0 4 1 (by decide) (by decide)) (ix 7)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_1_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 1 (witness (fun i j s => x i j (ix s))) 3 -
      witness (fun i j s => x i j (ix s)) 3 = x 4 1 (ix 3) := by
  have h0 := congrFun (h.commute 2 0 4 1 (by decide) (by decide)) (ix 8)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_1_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 1 (witness (fun i j s => x i j (ix s))) 4 -
      witness (fun i j s => x i j (ix s)) 4 = x 4 1 (ix 4) := by
  have h0 := congrFun (h.commute 0 1 4 1 (by decide) (by decide)) (ix 1)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_1_5 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 1 (witness (fun i j s => x i j (ix s))) 5 -
      witness (fun i j s => x i j (ix s)) 5 = x 4 1 (ix 5) := by
  have h0 := congrFun (h.commute 0 1 4 1 (by decide) (by decide)) (ix 2)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_1_6 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 1 (witness (fun i j s => x i j (ix s))) 6 -
      witness (fun i j s => x i j (ix s)) 6 = x 4 1 (ix 6) := by
  have h0 := congrFun (h.commute 0 1 4 1 (by decide) (by decide)) (ix 3)
  have h1 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h2 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
  have h3 := congrFun (h.commute 0 2 3 1 (by decide) (by decide)) (ix 2)
  have h4 := congrFun (h.steinberg 0 2 1 (by decide) (by decide) (by decide)) (ix 1)
  have h5 := congrFun (h.steinberg 0 3 1 (by decide) (by decide) (by decide)) (ix 1)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5

private theorem cert_4_1_7 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 1 (witness (fun i j s => x i j (ix s))) 7 -
      witness (fun i j s => x i j (ix s)) 7 = x 4 1 (ix 7) := by
  have h0 := congrFun (h.commute 0 2 4 1 (by decide) (by decide)) (ix 2)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_1_8 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 1 (witness (fun i j s => x i j (ix s))) 8 -
      witness (fun i j s => x i j (ix s)) 8 = x 4 1 (ix 8) := by
  have h0 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h1 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
  have h2 := congrFun (h.commute 0 2 3 1 (by decide) (by decide)) (ix 2)
  have h3 := congrFun (h.commute 0 2 4 1 (by decide) (by decide)) (ix 3)
  have h4 := congrFun (h.steinberg 0 3 1 (by decide) (by decide) (by decide)) (ix 1)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4

private theorem cert_4_1_9 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 1 (witness (fun i j s => x i j (ix s))) 9 -
      witness (fun i j s => x i j (ix s)) 9 = x 4 1 (ix 9) := by
  have h0 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 1)
  have h1 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 2)
  have h2 := congrFun (h.commute 0 1 2 3 (by decide) (by decide)) (ix 1)
  have h3 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h4 := congrFun (h.steinberg 0 2 3 (by decide) (by decide) (by decide)) (ix 0)
  have h5 := congrFun (h.commute 0 3 4 1 (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5

private theorem cert_4_2_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 2 (witness (fun i j s => x i j (ix s))) 0 -
      witness (fun i j s => x i j (ix s)) 0 = x 4 2 (ix 0) := by
  have h0 := congrFun (h.commute 3 0 4 2 (by decide) (by decide)) (ix 5)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_2_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 2 (witness (fun i j s => x i j (ix s))) 1 -
      witness (fun i j s => x i j (ix s)) 1 = x 4 2 (ix 1) := by
  have h0 := congrFun (h.commute 1 0 4 2 (by decide) (by decide)) (ix 4)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_2_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 2 (witness (fun i j s => x i j (ix s))) 2 -
      witness (fun i j s => x i j (ix s)) 2 = x 4 2 (ix 2) := by
  have h0 := congrFun (h.commute 1 0 4 2 (by decide) (by decide)) (ix 5)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_2_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 2 (witness (fun i j s => x i j (ix s))) 3 -
      witness (fun i j s => x i j (ix s)) 3 = x 4 2 (ix 3) := by
  have h0 := congrFun (h.commute 1 0 4 2 (by decide) (by decide)) (ix 6)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_2_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 2 (witness (fun i j s => x i j (ix s))) 4 -
      witness (fun i j s => x i j (ix s)) 4 = x 4 2 (ix 4) := by
  have h0 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 1)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_2_5 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 2 (witness (fun i j s => x i j (ix s))) 5 -
      witness (fun i j s => x i j (ix s)) 5 = x 4 2 (ix 5) := by
  have h0 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 2)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_2_6 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 2 (witness (fun i j s => x i j (ix s))) 6 -
      witness (fun i j s => x i j (ix s)) 6 = x 4 2 (ix 6) := by
  have h0 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_2_7 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 2 (witness (fun i j s => x i j (ix s))) 7 -
      witness (fun i j s => x i j (ix s)) 7 = x 4 2 (ix 7) := by
  have h0 := congrFun (h.commute 0 2 4 2 (by decide) (by decide)) (ix 2)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_2_8 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 2 (witness (fun i j s => x i j (ix s))) 8 -
      witness (fun i j s => x i j (ix s)) 8 = x 4 2 (ix 8) := by
  have h0 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h1 := congrFun (h.steinberg 0 1 2 (by decide) (by decide) (by decide)) (ix 0)
  have h2 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 4)
  have h3 := congrFun (h.commute 0 2 3 1 (by decide) (by decide)) (ix 2)
  have h4 := congrFun (h.commute 0 2 4 2 (by decide) (by decide)) (ix 3)
  have h5 := congrFun (h.steinberg 0 3 1 (by decide) (by decide) (by decide)) (ix 1)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5

private theorem cert_4_2_9 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 2 (witness (fun i j s => x i j (ix s))) 9 -
      witness (fun i j s => x i j (ix s)) 9 = x 4 2 (ix 9) := by
  have h0 := congrFun (h.square 0 1) (ix 1)
  have h1 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h2 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 1)
  have h3 := congrFun (h.commute 0 2 1 3 (by decide) (by decide)) (ix 0)
  have h4 := congrFun (h.commute 0 3 4 2 (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4

private theorem cert_4_3_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 3 (witness (fun i j s => x i j (ix s))) 0 -
      witness (fun i j s => x i j (ix s)) 0 = x 4 3 (ix 0) := by
  have h0 := congrFun (h.commute 2 0 4 3 (by decide) (by decide)) (ix 4)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_3_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 3 (witness (fun i j s => x i j (ix s))) 1 -
      witness (fun i j s => x i j (ix s)) 1 = x 4 3 (ix 1) := by
  have h0 := congrFun (h.commute 1 0 4 3 (by decide) (by decide)) (ix 4)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_3_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 3 (witness (fun i j s => x i j (ix s))) 2 -
      witness (fun i j s => x i j (ix s)) 2 = x 4 3 (ix 2) := by
  have h0 := congrFun (h.commute 1 0 4 3 (by decide) (by decide)) (ix 5)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_3_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 3 (witness (fun i j s => x i j (ix s))) 3 -
      witness (fun i j s => x i j (ix s)) 3 = x 4 3 (ix 3) := by
  have h0 := congrFun (h.commute 1 0 4 3 (by decide) (by decide)) (ix 6)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_3_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 3 (witness (fun i j s => x i j (ix s))) 4 -
      witness (fun i j s => x i j (ix s)) 4 = x 4 3 (ix 4) := by
  have h0 := congrFun (h.commute 0 1 4 3 (by decide) (by decide)) (ix 1)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_3_5 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 3 (witness (fun i j s => x i j (ix s))) 5 -
      witness (fun i j s => x i j (ix s)) 5 = x 4 3 (ix 5) := by
  have h0 := congrFun (h.commute 0 1 4 3 (by decide) (by decide)) (ix 2)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_3_6 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 3 (witness (fun i j s => x i j (ix s))) 6 -
      witness (fun i j s => x i j (ix s)) 6 = x 4 3 (ix 6) := by
  have h0 := congrFun (h.commute 0 1 4 3 (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_3_7 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 3 (witness (fun i j s => x i j (ix s))) 7 -
      witness (fun i j s => x i j (ix s)) 7 = x 4 3 (ix 7) := by
  have h0 := congrFun (h.commute 0 2 4 3 (by decide) (by decide)) (ix 2)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_3_8 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 3 (witness (fun i j s => x i j (ix s))) 8 -
      witness (fun i j s => x i j (ix s)) 8 = x 4 3 (ix 8) := by
  have h0 := congrFun (h.commute 0 2 4 3 (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_3_9 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 3 (witness (fun i j s => x i j (ix s))) 9 -
      witness (fun i j s => x i j (ix s)) 9 = x 4 3 (ix 9) := by
  have h0 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 1)
  have h1 := congrFun (h.commute 0 1 0 2 (by decide) (by decide)) (ix 2)
  have h2 := congrFun (h.commute 0 1 2 3 (by decide) (by decide)) (ix 1)
  have h3 := congrFun (h.commute 0 1 4 2 (by decide) (by decide)) (ix 9)
  have h4 := congrFun (h.steinberg 0 1 3 (by decide) (by decide) (by decide)) (ix 0)
  have h5 := congrFun (h.steinberg 0 2 3 (by decide) (by decide) (by decide)) (ix 0)
  have h6 := congrFun (h.commute 0 3 4 3 (by decide) (by decide)) (ix 3)
  simp [act, source, witness, action_coord] at h0 h1 h2 h3 h4 h5 h6 ⊢
  linear_combination (norm := square_ring) h0 + h1 + h2 + h3 + h4 + h5 + h6

private theorem cert_4_4_0 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 4 (witness (fun i j s => x i j (ix s))) 0 -
      witness (fun i j s => x i j (ix s)) 0 = x 4 4 (ix 0) := by
  have h0 := congrFun (h.diagonal 4) (ix 0)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_4_1 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 4 (witness (fun i j s => x i j (ix s))) 1 -
      witness (fun i j s => x i j (ix s)) 1 = x 4 4 (ix 1) := by
  have h0 := congrFun (h.diagonal 4) (ix 1)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_4_2 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 4 (witness (fun i j s => x i j (ix s))) 2 -
      witness (fun i j s => x i j (ix s)) 2 = x 4 4 (ix 2) := by
  have h0 := congrFun (h.diagonal 4) (ix 2)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_4_3 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 4 (witness (fun i j s => x i j (ix s))) 3 -
      witness (fun i j s => x i j (ix s)) 3 = x 4 4 (ix 3) := by
  have h0 := congrFun (h.diagonal 4) (ix 3)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_4_4 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 4 (witness (fun i j s => x i j (ix s))) 4 -
      witness (fun i j s => x i j (ix s)) 4 = x 4 4 (ix 4) := by
  have h0 := congrFun (h.diagonal 4) (ix 4)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_4_5 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 4 (witness (fun i j s => x i j (ix s))) 5 -
      witness (fun i j s => x i j (ix s)) 5 = x 4 4 (ix 5) := by
  have h0 := congrFun (h.diagonal 4) (ix 5)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_4_6 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 4 (witness (fun i j s => x i j (ix s))) 6 -
      witness (fun i j s => x i j (ix s)) 6 = x 4 4 (ix 6) := by
  have h0 := congrFun (h.diagonal 4) (ix 6)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_4_7 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 4 (witness (fun i j s => x i j (ix s))) 7 -
      witness (fun i j s => x i j (ix s)) 7 = x 4 4 (ix 7) := by
  have h0 := congrFun (h.diagonal 4) (ix 7)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_4_8 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 4 (witness (fun i j s => x i j (ix s))) 8 -
      witness (fun i j s => x i j (ix s)) 8 = x 4 4 (ix 8) := by
  have h0 := congrFun (h.diagonal 4) (ix 8)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

private theorem cert_4_4_9 (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) :
    act 4 4 (witness (fun i j s => x i j (ix s))) 9 -
      witness (fun i j s => x i j (ix s)) 9 = x 4 4 (ix 9) := by
  have h0 := congrFun (h.diagonal 4) (ix 9)
  simp [act, source, witness] at h0 ⊢
  linear_combination (norm := square_ring) h0

/-- Assembly of the 250 scalar certificates, with all vector coordinates arbitrary. -/

private theorem certificates_exact (x : Fin 5 → Fin 5 → ExteriorCoordinates 2)
    (h : ElementaryRelations 2 x) (i j : Fin 5) (s : Fin 10) :
    act i j (witness (fun i j s => x i j (ix s))) s -
      witness (fun i j s => x i j (ix s)) s = x i j (ix s) := by
  fin_cases i <;> fin_cases j <;> fin_cases s
  · exact cert_0_0_0 x h
  · exact cert_0_0_1 x h
  · exact cert_0_0_2 x h
  · exact cert_0_0_3 x h
  · exact cert_0_0_4 x h
  · exact cert_0_0_5 x h
  · exact cert_0_0_6 x h
  · exact cert_0_0_7 x h
  · exact cert_0_0_8 x h
  · exact cert_0_0_9 x h
  · exact cert_0_1_0 x h
  · exact cert_0_1_1 x h
  · exact cert_0_1_2 x h
  · exact cert_0_1_3 x h
  · exact cert_0_1_4 x h
  · exact cert_0_1_5 x h
  · exact cert_0_1_6 x h
  · exact cert_0_1_7 x h
  · exact cert_0_1_8 x h
  · exact cert_0_1_9 x h
  · exact cert_0_2_0 x h
  · exact cert_0_2_1 x h
  · exact cert_0_2_2 x h
  · exact cert_0_2_3 x h
  · exact cert_0_2_4 x h
  · exact cert_0_2_5 x h
  · exact cert_0_2_6 x h
  · exact cert_0_2_7 x h
  · exact cert_0_2_8 x h
  · exact cert_0_2_9 x h
  · exact cert_0_3_0 x h
  · exact cert_0_3_1 x h
  · exact cert_0_3_2 x h
  · exact cert_0_3_3 x h
  · exact cert_0_3_4 x h
  · exact cert_0_3_5 x h
  · exact cert_0_3_6 x h
  · exact cert_0_3_7 x h
  · exact cert_0_3_8 x h
  · exact cert_0_3_9 x h
  · exact cert_0_4_0 x h
  · exact cert_0_4_1 x h
  · exact cert_0_4_2 x h
  · exact cert_0_4_3 x h
  · exact cert_0_4_4 x h
  · exact cert_0_4_5 x h
  · exact cert_0_4_6 x h
  · exact cert_0_4_7 x h
  · exact cert_0_4_8 x h
  · exact cert_0_4_9 x h
  · exact cert_1_0_0 x h
  · exact cert_1_0_1 x h
  · exact cert_1_0_2 x h
  · exact cert_1_0_3 x h
  · exact cert_1_0_4 x h
  · exact cert_1_0_5 x h
  · exact cert_1_0_6 x h
  · exact cert_1_0_7 x h
  · exact cert_1_0_8 x h
  · exact cert_1_0_9 x h
  · exact cert_1_1_0 x h
  · exact cert_1_1_1 x h
  · exact cert_1_1_2 x h
  · exact cert_1_1_3 x h
  · exact cert_1_1_4 x h
  · exact cert_1_1_5 x h
  · exact cert_1_1_6 x h
  · exact cert_1_1_7 x h
  · exact cert_1_1_8 x h
  · exact cert_1_1_9 x h
  · exact cert_1_2_0 x h
  · exact cert_1_2_1 x h
  · exact cert_1_2_2 x h
  · exact cert_1_2_3 x h
  · exact cert_1_2_4 x h
  · exact cert_1_2_5 x h
  · exact cert_1_2_6 x h
  · exact cert_1_2_7 x h
  · exact cert_1_2_8 x h
  · exact cert_1_2_9 x h
  · exact cert_1_3_0 x h
  · exact cert_1_3_1 x h
  · exact cert_1_3_2 x h
  · exact cert_1_3_3 x h
  · exact cert_1_3_4 x h
  · exact cert_1_3_5 x h
  · exact cert_1_3_6 x h
  · exact cert_1_3_7 x h
  · exact cert_1_3_8 x h
  · exact cert_1_3_9 x h
  · exact cert_1_4_0 x h
  · exact cert_1_4_1 x h
  · exact cert_1_4_2 x h
  · exact cert_1_4_3 x h
  · exact cert_1_4_4 x h
  · exact cert_1_4_5 x h
  · exact cert_1_4_6 x h
  · exact cert_1_4_7 x h
  · exact cert_1_4_8 x h
  · exact cert_1_4_9 x h
  · exact cert_2_0_0 x h
  · exact cert_2_0_1 x h
  · exact cert_2_0_2 x h
  · exact cert_2_0_3 x h
  · exact cert_2_0_4 x h
  · exact cert_2_0_5 x h
  · exact cert_2_0_6 x h
  · exact cert_2_0_7 x h
  · exact cert_2_0_8 x h
  · exact cert_2_0_9 x h
  · exact cert_2_1_0 x h
  · exact cert_2_1_1 x h
  · exact cert_2_1_2 x h
  · exact cert_2_1_3 x h
  · exact cert_2_1_4 x h
  · exact cert_2_1_5 x h
  · exact cert_2_1_6 x h
  · exact cert_2_1_7 x h
  · exact cert_2_1_8 x h
  · exact cert_2_1_9 x h
  · exact cert_2_2_0 x h
  · exact cert_2_2_1 x h
  · exact cert_2_2_2 x h
  · exact cert_2_2_3 x h
  · exact cert_2_2_4 x h
  · exact cert_2_2_5 x h
  · exact cert_2_2_6 x h
  · exact cert_2_2_7 x h
  · exact cert_2_2_8 x h
  · exact cert_2_2_9 x h
  · exact cert_2_3_0 x h
  · exact cert_2_3_1 x h
  · exact cert_2_3_2 x h
  · exact cert_2_3_3 x h
  · exact cert_2_3_4 x h
  · exact cert_2_3_5 x h
  · exact cert_2_3_6 x h
  · exact cert_2_3_7 x h
  · exact cert_2_3_8 x h
  · exact cert_2_3_9 x h
  · exact cert_2_4_0 x h
  · exact cert_2_4_1 x h
  · exact cert_2_4_2 x h
  · exact cert_2_4_3 x h
  · exact cert_2_4_4 x h
  · exact cert_2_4_5 x h
  · exact cert_2_4_6 x h
  · exact cert_2_4_7 x h
  · exact cert_2_4_8 x h
  · exact cert_2_4_9 x h
  · exact cert_3_0_0 x h
  · exact cert_3_0_1 x h
  · exact cert_3_0_2 x h
  · exact cert_3_0_3 x h
  · exact cert_3_0_4 x h
  · exact cert_3_0_5 x h
  · exact cert_3_0_6 x h
  · exact cert_3_0_7 x h
  · exact cert_3_0_8 x h
  · exact cert_3_0_9 x h
  · exact cert_3_1_0 x h
  · exact cert_3_1_1 x h
  · exact cert_3_1_2 x h
  · exact cert_3_1_3 x h
  · exact cert_3_1_4 x h
  · exact cert_3_1_5 x h
  · exact cert_3_1_6 x h
  · exact cert_3_1_7 x h
  · exact cert_3_1_8 x h
  · exact cert_3_1_9 x h
  · exact cert_3_2_0 x h
  · exact cert_3_2_1 x h
  · exact cert_3_2_2 x h
  · exact cert_3_2_3 x h
  · exact cert_3_2_4 x h
  · exact cert_3_2_5 x h
  · exact cert_3_2_6 x h
  · exact cert_3_2_7 x h
  · exact cert_3_2_8 x h
  · exact cert_3_2_9 x h
  · exact cert_3_3_0 x h
  · exact cert_3_3_1 x h
  · exact cert_3_3_2 x h
  · exact cert_3_3_3 x h
  · exact cert_3_3_4 x h
  · exact cert_3_3_5 x h
  · exact cert_3_3_6 x h
  · exact cert_3_3_7 x h
  · exact cert_3_3_8 x h
  · exact cert_3_3_9 x h
  · exact cert_3_4_0 x h
  · exact cert_3_4_1 x h
  · exact cert_3_4_2 x h
  · exact cert_3_4_3 x h
  · exact cert_3_4_4 x h
  · exact cert_3_4_5 x h
  · exact cert_3_4_6 x h
  · exact cert_3_4_7 x h
  · exact cert_3_4_8 x h
  · exact cert_3_4_9 x h
  · exact cert_4_0_0 x h
  · exact cert_4_0_1 x h
  · exact cert_4_0_2 x h
  · exact cert_4_0_3 x h
  · exact cert_4_0_4 x h
  · exact cert_4_0_5 x h
  · exact cert_4_0_6 x h
  · exact cert_4_0_7 x h
  · exact cert_4_0_8 x h
  · exact cert_4_0_9 x h
  · exact cert_4_1_0 x h
  · exact cert_4_1_1 x h
  · exact cert_4_1_2 x h
  · exact cert_4_1_3 x h
  · exact cert_4_1_4 x h
  · exact cert_4_1_5 x h
  · exact cert_4_1_6 x h
  · exact cert_4_1_7 x h
  · exact cert_4_1_8 x h
  · exact cert_4_1_9 x h
  · exact cert_4_2_0 x h
  · exact cert_4_2_1 x h
  · exact cert_4_2_2 x h
  · exact cert_4_2_3 x h
  · exact cert_4_2_4 x h
  · exact cert_4_2_5 x h
  · exact cert_4_2_6 x h
  · exact cert_4_2_7 x h
  · exact cert_4_2_8 x h
  · exact cert_4_2_9 x h
  · exact cert_4_3_0 x h
  · exact cert_4_3_1 x h
  · exact cert_4_3_2 x h
  · exact cert_4_3_3 x h
  · exact cert_4_3_4 x h
  · exact cert_4_3_5 x h
  · exact cert_4_3_6 x h
  · exact cert_4_3_7 x h
  · exact cert_4_3_8 x h
  · exact cert_4_3_9 x h
  · exact cert_4_4_0 x h
  · exact cert_4_4_1 x h
  · exact cert_4_4_2 x h
  · exact cert_4_4_3 x h
  · exact cert_4_4_4 x h
  · exact cert_4_4_5 x h
  · exact cert_4_4_6 x h
  · exact cert_4_4_7 x h
  · exact cert_4_4_8 x h
  · exact cert_4_4_9 x h

/-- Every exterior-square family satisfying the elementary relations is principal. -/
public theorem elementaryRelations_exact_two :
    ∀ x : Fin 5 → Fin 5 → ExteriorCoordinates 2, ElementaryRelations 2 x →
      ∃ v : ExteriorCoordinates 2, ∀ i j, elementaryAction 2 i j v - v = x i j := by
  intro x h
  refine ⟨fun s => witness (fun i j t => x i j (ix t)) (indexEquiv.symm s), ?_⟩
  intro i j
  funext s
  obtain ⟨s, rfl⟩ := ix_bij.surjective s
  change elementaryAction 2 i j _ (ix s) - _ = _
  rw [action_coord]
  change act i j (fun t => witness (fun i j t => x i j (ix t))
      (indexEquiv.symm (indexEquiv t))) s -
    witness (fun i j t => x i j (ix t)) (indexEquiv.symm (indexEquiv s)) = _
  simpa only [Equiv.symm_apply_apply] using certificates_exact x h i j s

end Representation.SL5TenDimensional
