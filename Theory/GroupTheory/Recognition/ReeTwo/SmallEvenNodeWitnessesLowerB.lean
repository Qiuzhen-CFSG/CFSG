module

public import Theory.GroupTheory.FinitePredicateSeparation
public import Theory.GroupTheory.FrattiniNormalizerWordCertificates
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodePartition

/-!
# Lower small even node witnesses, batch B

For each listed node, products of squares certify the generator displacements.
A Boolean mask on the first few root coordinates contains the identity, is
preserved by right multiplication by every generator, and excludes the witness.
The finite predicate separation lemma proves nonmembership; the square-word
criterion then gives normalization and trivial Frattini action.

The complement-action tables reduce transition checks to the triangular core
multiplication formulas. The tables, transitions, separating values, and square
identities are all checked by kernel reduction. The original node definitions
and their generator order are retained.

Source: Shinoda (1975), (2.3), pp. 81–82, via the verified Ree two coordinates.
Exploratory square words and masks only guide these independently checked proofs.
-/

namespace ReeTwo.SylowModel.SmallEvenLower
set_option maxRecDepth 10000

namespace Node61
private def gen : Fin 8 → SylowModel :=
  ![rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3 * root 4 * root 6 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 61 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[0, 3]], [[0, 3]], [[2]], [[3]], [[2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (13298352258233846886423622947233703897330924415498923301752213244395948534509601765575354734931522045729465200414361849813123626058337145230839307632705 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨1, 1, 0, 0, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨1, 0, 0, 1, 1, 0, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 2, Multiplicative.ofAdd 2, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5, b6] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 61 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 61).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node61

namespace Node62
private def gen : Fin 8 → SylowModel :=
  ![root 3 * root 4 * root 7 * root 8, rootOne ^ 2, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 62 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 4 * root 7 * root 8
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[], [], [], [[0, 2]], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (25961880433486709464340449366179845 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (0)))))))
private def sample (v : Fin 5 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 5 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 62 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 62).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node62

namespace Node64
private def gen : Fin 8 → SylowModel :=
  ![root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 64 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 1 * root 3 * root 6 * root 7 * root 8 * root 9
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[1, 3], [0, 1], [2]], [[1, 3]], [[0, 2], [0, 1]], [[0, 2], [0, 1]], [], [[0, 4], [0]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (17 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (0))))
private def sample (v : Fin 2 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 2 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 64 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 64).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node64

namespace Node65
private def gen : Fin 8 → SylowModel :=
  ![rootOne ^ 2 * root 3, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 65 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[], [], [[2]], [], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (281492156841985 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 65 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 65).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node65

namespace Node66
private def gen : Fin 8 → SylowModel :=
  ![root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 66 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 1 * root 3 * root 6 * root 7 * root 8 * root 9
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[1]], [[1, 4], [0]], [[0, 2], [2]], [[0, 2], [2]], [], [[0, 1]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (17 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (0))))
private def sample (v : Fin 2 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 0, 1, 1, 0, 1, 0⟩, ⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 0, 1, 1, 0, 1, 0⟩, ⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 0, 0, 1, 0, 1, 0⟩, ⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 2 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 66 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 66).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node66

namespace Node67
private def gen : Fin 8 → SylowModel :=
  ![root 0, rootOne ^ 2 * root 0 * root 3, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 67 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[3]], [[3]], [[1, 4], [1, 4], [1, 4], [1]], [], [[0, 4]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1833304346943717966639457288182613347555181315388407769450673506091025 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 67 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 67).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node67

namespace Node68
private def gen : Fin 8 → SylowModel :=
  ![root 0, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 5 * root 6 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 68 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[3]], [[3]], [[1, 4], [1, 4], [1, 4], [1]], [], [[0, 4]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (27973684186818380184488806725387609116061554710313635284835893265 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 68 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 68).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node68

namespace Node69
private def gen : Fin 8 → SylowModel :=
  ![root 0, rootOne ^ 2 * root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 69 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2 * root 0 * root 2 * root 4 * root 9
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[1, 3], [0, 1]], [[3]], [[0, 4], [0, 2]], [[0, 4]], [[0, 4], [0, 1]], [], [[0, 4]], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (88274434192350308993204202194075665 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨1, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 1, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 69 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 69).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node69

namespace Node70
private def gen : Fin 8 → SylowModel :=
  ![root 3, rootOne ^ 2, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 70 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 6
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[0, 4], [0]], [[0]], [], [[0, 4], [0]], [[0, 4], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1022950173948470061766538872221396667997250615273975654116981948853408134299875428208698317807198835300662709728770060313169034675785848606106237337605 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5, b6] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 70 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 70).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node70

namespace Node71
private def gen : Fin 8 → SylowModel :=
  ![root 3, rootOne ^ 2, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 71 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 9
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[3, 4]], [], [[0]], [], [[0, 4], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (8834235325948802345046899913040398051563744573439477497449511976603484165 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 71 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 71).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node71

namespace Node72
private def gen : Fin 8 → SylowModel :=
  ![root 3, rootOne ^ 2, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 72 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[3]], [[3]], [[0, 3]], [], [[0, 3], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (25961880439531430797541360145858565 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 72 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 72).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node72

namespace Node73
private def gen : Fin 8 → SylowModel :=
  ![root 3, rootOne ^ 2, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 73 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[1, 3]], [[1, 3]], [[0, 3]], [], [[2, 3]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (5 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (0)))))
private def sample (v : Fin 3 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 3 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 73 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 73).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node73

namespace Node74
private def gen : Fin 8 → SylowModel :=
  ![root 3, rootOne ^ 2, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 74 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 9
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[3, 4]], [], [[0]], [], [[0, 2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (8834370125682169483275645324887558334434591839660707837291041070231388165 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 74 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 74).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node74

namespace Node75
private def gen : Fin 8 → SylowModel :=
  ![root 3, rootOne ^ 2, root 4 * root 6 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 75 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 9
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[4]], [], [[0, 2]], [], [[0, 2], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1022950173948470061711084632174428872890016328595466798091101177698837924278228541633137323919040006893069753807510196826401136374665241819734784409605 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5, b6] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 75 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 75).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node75

namespace Node76
private def gen : Fin 8 → SylowModel :=
  ![root 3, rootOne ^ 2, root 4 * root 6 * root 9, root 2 * root 3 * root 4 * root 5 * root 8, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 76 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[4]], [[4]], [[0]], [[0, 2], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (15608742755214210231779915929259032571055514498693472829907953377414432804651641362342633689117848536250422419404885561633930146422505940294041605 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5, b6] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 76 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 76).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node76

namespace Node77
private def gen : Fin 8 → SylowModel :=
  ![root 3, rootOne ^ 2, root 4 * root 6 * root 9, root 2 * root 3 * root 4 * root 5 * root 8, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 77 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[2, 4], [0]], [[2, 4], [0]], [[0]], [[0, 2], [0]], [[0, 2], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (55454240046967795113246647431754370515869792755885950270787439502838716120715076881598207001671317475256178742512314874404452761605 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5, b6] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 77 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 77).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node77

namespace Node78
private def gen : Fin 8 → SylowModel :=
  ![root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 78 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[], [], [], [[1]], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1766954904976454179975506043398033716755045979863409803625819418625572865 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 78 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 78).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node78

namespace Node79
private def gen : Fin 8 → SylowModel :=
  ![root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 79 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[], [[3]], [], [], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (7067496100545735587003645991222272547677715595663377443617001788500148225 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 79 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 79).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node79

namespace Node80
private def gen : Fin 8 → SylowModel :=
  ![root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 7 * root 8, root 5 * root 6 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 80 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[1, 3]], [[1, 3]], [[0]], [], [[0, 2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (327685 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 80 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 80).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node80

namespace Node82
private def gen : Fin 8 → SylowModel :=
  ![root 0, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 2 * root 3 * root 7 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 82 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 1 * root 3 * root 6 * root 7 * root 8 * root 9
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[2, 3], [1]], [[1, 3], [0, 2], [0, 1]], [[0, 6], [0, 2], [0, 1]], [], [], [[0, 6]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (17 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (0))))
private def sample (v : Fin 2 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 2 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 82 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 82).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node82

namespace Node84
private def gen : Fin 8 → SylowModel :=
  ![root 0, root 0 * root 3 * root 5 * root 6 * root 7, root 2 * root 3 * root 7 * root 9, root 5 * root 6 * root 7, root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 84 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 1 * root 3 * root 6 * root 7 * root 8 * root 9
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[1, 3], [0, 1]], [[1, 3], [0, 1]], [[0, 2], [0, 1]], [], [], [[0, 6]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (17 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (0))))
private def sample (v : Fin 2 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨1, 1, 1, 1, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨1, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 2 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 84 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 84).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node84

namespace Node85
private def gen : Fin 8 → SylowModel :=
  ![root 1 * root 5 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 85 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 1 * root 3 * root 6 * root 7 * root 8 * root 9
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[0, 5], [0]], [[0, 1], [0]], [[0, 5], [0, 1]], [[2, 3]], [[0, 5], [0]], [[0, 5], [0]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (72339069014638849 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 85 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 85).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node85

namespace Node86
private def gen : Fin 8 → SylowModel :=
  ![root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 5 * root 8, root 6 * root 8, root 7, root 8, root 9]
private theorem generated : smallEvenDescentNode 86 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 4 * root 7 * root 8
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[], [[2], [0]], [[0]], [[0, 2], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1334420292954144636173298358315647233 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (0)))))))
private def sample (v : Fin 5 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 5 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 86 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 86).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node86

namespace Node88
private def gen : Fin 8 → SylowModel :=
  ![root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 8, root 5 * root 8, root 6 * root 8, root 7, root 8, root 9]
private theorem generated : smallEvenDescentNode 88 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[2], [0]], [[1, 2], [1]], [[0, 4]], [[0, 2]], [[0, 2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (72340172838076673 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (0)))))))
private def sample (v : Fin 5 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 5 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 88 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 88).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node88

namespace Node89
private def gen : Fin 8 → SylowModel :=
  ![root 2 * root 4 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 5 * root 8, root 6 * root 8, root 7, root 8, root 9]
private theorem generated : smallEvenDescentNode 89 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[1, 4], [1, 2], [0]], [[1, 4], [0, 1], [0]], [[0]], [[0, 2]], [[0, 2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (72058693549621249 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 89 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 89).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node89

namespace Node90
private def gen : Fin 8 → SylowModel :=
  ![rootOne ^ 2 * root 1 * root 5 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 90 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 3 * root 8
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[0], [0]], [[1]], [[1, 4]], [], [[0], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (288511851128423425 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 90 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 90).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node90

namespace Node91
private def gen : Fin 8 → SylowModel :=
  ![root 0 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 5 * root 6 * root 8 * root 9, root 2 * root 3 * root 4 * root 8, root 6 * root 9, root 7 * root 9, root 8, root 9]
private theorem generated : smallEvenDescentNode 91 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[3], [0]], [[3]], [[0, 2], [0]], [], [[2, 3]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1809251396044390299384554520806713036961713831735447723091766283969562148865 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨1, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, ⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 1, 0, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 0, 0, 1, 0, 1, 0⟩, ⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 1, 1, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 0, 0, 0, 0, 0, 1⟩, ⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 91 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 91).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node91

namespace Node92
private def gen : Fin 8 → SylowModel :=
  ![root 3, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 5 * root 8 * root 9, root 6 * root 8, root 7, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 92 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[2]], [[1, 2], [1]], [], [[0]], [[3]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (27633945340263533243800647826395627996865359237749590512510438264013825 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (0))))))))
private def sample (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 6 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 92 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 92).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node92

namespace Node94
private def gen : Fin 8 → SylowModel :=
  ![root 2 * root 4 * root 8, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 4 * root 5 * root 8 * root 9, root 6 * root 8, root 7, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 94 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[1, 4], [1, 2]], [[1, 2], [1, 2], [1, 2], [0, 1], [0]], [[0]], [[3], [0]], [[3]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (288234774198288385 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 94 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 94).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node94

namespace Node95
private def gen : Fin 8 → SylowModel :=
  ![root 1 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 5 * root 9, root 4 * root 7 * root 8 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 8 * root 9, root 8, root 9]
private theorem generated : smallEvenDescentNode 95 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 1 * root 3 * root 6 * root 7 * root 8 * root 9
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[2, 3]], [[0, 1], [0, 1], [0, 1], [0]], [], [[1, 2]], [], [[2, 3]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1285 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 95 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 95).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node95

namespace Node100
private def gen : Fin 8 → SylowModel :=
  ![root 0, root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 7, root 2 * root 3 * root 8, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 8, root 9]
private theorem generated : smallEvenDescentNode 100 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 1 * root 3 * root 6 * root 7 * root 8 * root 9
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[2], [1]], [[0, 2], [0, 1], [2]], [[0, 2], [0, 1], [2], [1]], [[0, 3]], [[0, 3]], [[0, 3]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1229764173248860433 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨1, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, ⟨1, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, ⟨1, 0, 0, 1, 1, 1, 1, 1, 0, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 100 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 100).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node100

namespace Node101
private def gen : Fin 8 → SylowModel :=
  ![root 0 * root 4 * root 7 * root 8, root 0 * root 1 * root 2 * root 3 * root 6 * root 8, root 2 * root 3 * root 4 * root 7, root 5 * root 7 * root 8 * root 9, root 6, root 7 * root 9, root 8, root 9]
private theorem generated : smallEvenDescentNode 101 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 1 * root 3 * root 6 * root 7 * root 8 * root 9
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[1, 2], [2]], [[1, 2], [0, 2]], [[0, 2], [2]], [[0, 6], [0]], [[0, 6], [0]], [[0, 6], [0]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1229764173248860433 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨1, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 0, 0, 1, 1, 0, 1, 0⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 1, 1, 0, 1, 1, 0, 1, 0⟩, ⟨1, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 1, 0, 0, 1, 0, 1, 0⟩, ⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 101 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 101).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node101

namespace Node102
private def gen : Fin 8 → SylowModel :=
  ![root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 7 * root 8, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 102 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 4 * root 7 * root 8
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[1, 2], [1]], [[1, 2], [0, 2]], [[1, 2], [0, 1]], [[0, 1], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (21272840229746016617024623764565921793 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (0)))))))
private def sample (v : Fin 5 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 1⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 5 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 102 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 102).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node102

namespace Node103
private def gen : Fin 8 → SylowModel :=
  ![root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 7 * root 8, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 7 * root 8, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 103 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[], [[1, 2], [0, 1]], [[0, 2], [1]], [], [[2, 3]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (269484289 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (0)))))
private def sample (v : Fin 3 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, 0, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 1⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 3 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 103 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 103).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node103

namespace Node104
private def gen : Fin 8 → SylowModel :=
  ![root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 8, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 7 * root 8, root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 104 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 2 * root 3 * root 4 * root 5 * root 6
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[], [[1, 2], [1]], [[0, 2], [2], [1]], [], [[0, 1], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (21267649200228672565668157016812552193 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (0)))))))
private def sample (v : Fin 5 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 1, 1, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 1⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 5 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 104 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 104).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node104

namespace Node105
private def gen : Fin 8 → SylowModel :=
  ![rootOne ^ 2 * root 3, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8, root 4 * root 7 * root 8, root 6 * root 8, root 7 * root 8 * root 9, root 8, root 9]
private theorem generated : smallEvenDescentNode 105 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[], [[0, 1], [1, 3], [0]], [[0, 2], [0]], [], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (1116691497985 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 105 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 105).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node105

namespace Node106
private def gen : Fin 8 → SylowModel :=
  ![root 1 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 9, root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 8, root 8, root 9]
private theorem generated : smallEvenDescentNode 106 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[1, 4], [1, 4], [1, 4], [0, 3]], [[1, 4], [1, 4], [1, 4], [0, 3]], [[1, 2], [1]], [], [[1, 4], [1, 4], [1, 4], [1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (4415226380545 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (0))))))
private def sample (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, 0, 0, 0, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 1⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 4 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 106 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 106).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node106

namespace Node107
private def gen : Fin 8 → SylowModel :=
  ![root 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8, root 4 * root 7 * root 8 * root 9, root 8, root 7 * root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 107 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 6
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[3, 4]], [[0]], [[3, 4]], [], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (3995838145334823623483436093942010574302542681028322829984706239297186070538865999768368788825543626039963757487980877829328448537148011300939366405 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5, b6] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 107 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 107).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node107

namespace Node108
private def gen : Fin 8 → SylowModel :=
  ![root 3, rootOne ^ 2 * root 6 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8, root 4 * root 7 * root 8 * root 9, root 8, root 7 * root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 108 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := rootOne ^ 2
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[], [[0]], [[1, 2], [2, 4], [0]], [[1, 3], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (811654623271136048520072956581970897905203982083878074840643454857240920578234762767094333465208359171670928725429124544764484536685230623587042305 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5, b6] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 108 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 108).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node108

namespace Node109
private def gen : Fin 8 → SylowModel :=
  ![root 3 * root 6 * root 8, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8, root 4 * root 7 * root 8 * root 9, root 8, root 7 * root 8 * root 9, root 9]
private theorem generated : smallEvenDescentNode 109 = Subgroup.closure (Set.range gen) := by
  simp only [gen, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : SylowModel := root 6
private def squares : Fin 8 → List (List (Fin 8)) :=
  ![[[0, 1]], [[0, 1], [0]], [[0, 1]], [], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i,
    Subgroup.evalSquareWord gen (squares i) = (gen i)⁻¹ * (g * gen i * g⁻¹) := by decide +kernel
private def pred (x : SylowModel) : Bool := (4011446887156050017542813411777458882009959255941137257686287377387171936990140899781263567352954427936037190809512373905172124839467102806076294405 : ℕ).testBit (x.right.toAdd.val + 4 * (x.left.b0.val + 2 * (x.left.b1.val + 2 * (x.left.b2.val + 2 * (x.left.b3.val + 2 * (x.left.b4.val + 2 * (x.left.b5.val + 2 * (x.left.b6.val + 2 * (0)))))))))
private def sample (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4) : SylowModel := ⟨⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, 0, 0, 0⟩, t⟩
private def actTable (t : FiveFour.Cyclic 4) : Fin 8 → Core :=
  ![![⟨0, 0, 0, 1, 0, 0, 1, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩], ![⟨0, 0, 0, 1, 1, 0, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 1, 1, 1, 1, 1, 1⟩, ⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩]] t.toAdd
private def rightTable : Fin 8 → FiveFour.Cyclic 4 :=
  ![Multiplicative.ofAdd 0, Multiplicative.ofAdd 2, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0, Multiplicative.ofAdd 0]
set_option maxHeartbeats 4000000 in
private theorem act_checked : ∀ t i, actTable t i =
    Core.complementAction (SemidirectProduct.inr t) (gen i).left := by decide +kernel
private theorem right_checked : ∀ i, rightTable i = (gen i).right := by decide +kernel
set_option maxHeartbeats 4000000 in
private theorem invariant_table : ∀ (v : Fin 7 → ZMod 2) (t : FiveFour.Cyclic 4),
    pred (sample v t) = true → ∀ i,
    pred ⟨(sample v t).left * actTable t i, t * rightTable i⟩ = true := by decide +kernel
private theorem invariant : ∀ x, pred x = true → ∀ i, pred (x * gen i) = true := by
  rintro ⟨⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9⟩, t⟩ hx i
  have h := invariant_table ![b0, b1, b2, b3, b4, b5, b6] t hx i
  rw [act_checked, right_checked] at h
  exact h
private theorem not_mem : g ∉ smallEvenDescentNode 109 := by
  rw [generated]
  exact Subgroup.not_mem_closure_of_right_invariant_predicate gen g pred invariant (by decide +kernel) (by decide +kernel)
private theorem witness : (smallEvenDescentNode 109).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) gen generated g not_mem squares checked
end Node109

/-- The certified indices in batch B. -/
@[expose] public def indicesB : List (Fin 600) :=
  [61, 62, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 82, 84, 85, 86, 88, 89, 90, 91, 92, 94, 95, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109]

/-- Every node listed in batch B has an outside Frattini normalizer witness. -/
public theorem witnessesB (i : Fin 600) (hi : i ∈ indicesB) :
    (smallEvenDescentNode i).HasFrattiniNormalizerWitness := by
  simp only [indicesB, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact Node61.witness
  · exact Node62.witness
  · exact Node64.witness
  · exact Node65.witness
  · exact Node66.witness
  · exact Node67.witness
  · exact Node68.witness
  · exact Node69.witness
  · exact Node70.witness
  · exact Node71.witness
  · exact Node72.witness
  · exact Node73.witness
  · exact Node74.witness
  · exact Node75.witness
  · exact Node76.witness
  · exact Node77.witness
  · exact Node78.witness
  · exact Node79.witness
  · exact Node80.witness
  · exact Node82.witness
  · exact Node84.witness
  · exact Node85.witness
  · exact Node86.witness
  · exact Node88.witness
  · exact Node89.witness
  · exact Node90.witness
  · exact Node91.witness
  · exact Node92.witness
  · exact Node94.witness
  · exact Node95.witness
  · exact Node100.witness
  · exact Node101.witness
  · exact Node102.witness
  · exact Node103.witness
  · exact Node104.witness
  · exact Node105.witness
  · exact Node106.witness
  · exact Node107.witness
  · exact Node108.witness
  · exact Node109.witness
end ReeTwo.SylowModel.SmallEvenLower
