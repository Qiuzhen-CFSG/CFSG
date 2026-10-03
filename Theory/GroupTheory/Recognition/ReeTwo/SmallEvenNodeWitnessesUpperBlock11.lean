module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeWitnessesUpperCoordinates

/-!
# Frattini witnesses for upper node block 11

Explicit projected orbits separate the proposed witnesses from the node
subgroups. Products of squares certify all generator displacements. The
coordinate bridge transfers these kernel-checked equations to the unchanged
root-word nodes.

Source: Shinoda (1975), (2.3), pp. 81–82, and the fixed node words in
`SmallEvenDescentNodes`. Certificate suggestions are verified here in Lean.
-/

namespace ReeTwo.SylowModel.UpperCertificate
set_option maxRecDepth 10000

namespace Node550
private def roots : Fin 5 → SylowModel := ![root 3 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 550 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 1 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 5 → Fin 1 → Fin 1 := ![![0], ![0], ![0], ![0], ![0]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 0 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 550 := by
  rw [generated]
  exact outside_of_projected_orbit gen 0 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[0, 1]], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 550).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node550
namespace Node551
private def roots : Fin 5 → SylowModel := ![root 3 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 551 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1)
private def rep : Fin 1 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 5 → Fin 1 → Fin 1 := ![![0], ![0], ![0], ![0], ![0]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 0 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 551 := by
  rw [generated]
  exact outside_of_projected_orbit gen 0 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[1], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 551).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node551
namespace Node552
private def roots : Fin 5 → SylowModel := ![root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 552 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 5 → Fin 2 → Fin 2 := ![![1, 0], ![0, 1], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 5 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 552 := by
  rw [generated]
  exact outside_of_projected_orbit gen 5 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 552).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node552
namespace Node554
private def roots : Fin 5 → SylowModel := ![rootOne ^ 2 * root 3 * root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 554 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0)]
private def next : Fin 5 → Fin 4 → Fin 4 := ![![1, 0, 3, 2], ![0, 1, 2, 3], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 554 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 554).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node554
namespace Node555
private def roots : Fin 5 → SylowModel := ![rootOne ^ 2 * root 3 * root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 2 * root 3 * root 4 * root 7 * root 8, root 7 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 555 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 5 → Fin 4 → Fin 4 := ![![1, 0, 3, 2], ![0, 1, 2, 3], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 555 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 555).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node555
namespace Node557
private def roots : Fin 5 → SylowModel := ![root 0 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 8 * root 9, root 9, root 7 * root 9]
private def gen : Fin 5 → E := ![(⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 557 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 5 → Fin 8 → Fin 8 := ![![4, 5, 6, 7, 0, 1, 2, 3], ![6, 7, 4, 5, 1, 0, 3, 2], ![3, 2, 1, 0, 7, 6, 5, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 557 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[2], [0]], [[2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 557).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node557
namespace Node558
private def roots : Fin 5 → SylowModel := ![root 0 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 2 * root 3 * root 4 * root 8 * root 9, root 9, root 7 * root 9]
private def gen : Fin 5 → E := ![(⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 558 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨1, 0, 0, 1, 0, 1, 1, 0, 1, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 5 → Fin 8 → Fin 8 := ![![4, 5, 6, 7, 0, 1, 2, 3], ![5, 4, 7, 6, 2, 3, 0, 1], ![3, 2, 1, 0, 7, 6, 5, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 558 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[1, 2], [0]], [[2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 558).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node558
namespace Node559
private def roots : Fin 5 → SylowModel := ![root 0 * root 2 * root 3 * root 4 * root 5 * root 8 * root 9, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 8 * root 9, root 9, root 7 * root 9]
private def gen : Fin 5 → E := ![(⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 559 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨1, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0)]
private def next : Fin 5 → Fin 8 → Fin 8 := ![![7, 6, 5, 4, 3, 2, 1, 0], ![6, 7, 4, 5, 1, 0, 3, 2], ![3, 2, 1, 0, 7, 6, 5, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 559 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[0, 1], [2]], [[2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 559).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node559
namespace Node561
private def roots : Fin 5 → SylowModel := ![root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 561 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 5 → Fin 4 → Fin 4 := ![![3, 2, 1, 0], ![1, 0, 3, 2], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 561 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[0, 1]], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 561).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node561
namespace Node562
private def roots : Fin 5 → SylowModel := ![root 2 * root 4 * root 5 * root 6 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 562 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 5 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 5 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 562 := by
  rw [generated]
  exact outside_of_projected_orbit gen 5 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[1]], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 562).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node562
namespace Node563
private def roots : Fin 5 → SylowModel := ![root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 563 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 5 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 563 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[], [[0, 1], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 563).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node563
namespace Node564
private def roots : Fin 5 → SylowModel := ![root 3, rootOne ^ 2 * root 5 * root 7 * root 8, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 564 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 5 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![1, 0, 3, 2], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 564 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 564).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node564
namespace Node565
private def roots : Fin 5 → SylowModel := ![root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 565 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 5 → Fin 2 → Fin 2 := ![![0, 1], ![1, 0], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 565 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[0, 1], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 565).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node565
namespace Node566
private def roots : Fin 5 → SylowModel := ![root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 5 * root 6 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 566 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 5 → Fin 2 → Fin 2 := ![![0, 1], ![1, 0], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 566 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 566).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node566
namespace Node567
private def roots : Fin 5 → SylowModel := ![root 2 * root 4 * root 5 * root 7 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 567 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 5 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 567 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[1], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 567).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node567
namespace Node569
private def roots : Fin 5 → SylowModel := ![rootOne ^ 2 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 569 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 5 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 569 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[0, 1], [1]], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 569).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node569
namespace Node570
private def roots : Fin 5 → SylowModel := ![root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 570 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 5 → Fin 2 → Fin 2 := ![![0, 1], ![1, 0], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 570 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[0, 1], [0]], [[0, 1], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 570).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node570
namespace Node571
private def roots : Fin 5 → SylowModel := ![root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 5 * root 7 * root 8, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 571 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 5 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![1, 0, 3, 2], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 571 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[0, 1], [1], [0]], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 571).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node571
namespace Node572
private def roots : Fin 5 → SylowModel := ![root 3 * root 5 * root 6 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 572 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 5 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![1, 0, 3, 2], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 572 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[1]], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 572).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node572
namespace Node573
private def roots : Fin 5 → SylowModel := ![root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 573 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1)
private def rep : Fin 1 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 5 → Fin 1 → Fin 1 := ![![0], ![0], ![0], ![0], ![0]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 0 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 573 := by
  rw [generated]
  exact outside_of_projected_orbit gen 0 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 573).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node573
namespace Node574
private def roots : Fin 5 → SylowModel := ![root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 5, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 574 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0)]
private def next : Fin 5 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![1, 0, 3, 2], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 574 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 574).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node574
namespace Node575
private def roots : Fin 5 → SylowModel := ![root 0 * root 2 * root 5 * root 6 * root 9, root 6 * root 7, root 7, root 5 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 575 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, 0)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 5 → Fin 2 → Fin 2 := ![![1, 0], ![0, 1], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 575 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 575).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node575
namespace Node577
private def roots : Fin 5 → SylowModel := ![root 2 * root 5 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 577 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 5 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 577 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[0, 1]], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 577).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node577
namespace Node578
private def roots : Fin 5 → SylowModel := ![root 2 * root 5 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 578 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 5 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 5 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 578 := by
  rw [generated]
  exact outside_of_projected_orbit gen 5 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[1]], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 578).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node578
namespace Node579
private def roots : Fin 5 → SylowModel := ![rootOne ^ 2 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨0, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 1), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 579 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 1)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 5 → Fin 2 → Fin 2 := ![![1, 0], ![0, 1], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 579 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[1]], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 579).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node579
namespace Node580
private def roots : Fin 5 → SylowModel := ![rootOne ^ 2 * root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 580 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 0)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 5 → Fin 2 → Fin 2 := ![![1, 0], ![0, 1], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 580 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 580).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node580
namespace Node583
private def roots : Fin 5 → SylowModel := ![rootOne ^ 2 * root 1 * root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7 * root 8 * root 9, root 4 * root 5, root 8 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 583 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 1, 0, 0, 1, 1, 0, 1, 0, 0⟩, 1), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 5 → Fin 8 → Fin 8 := ![![7, 6, 5, 4, 1, 0, 3, 2], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 583 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[0, 1], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 583).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node583
namespace Node584
private def roots : Fin 5 → SylowModel := ![root 3, rootOne ^ 2 * root 1 * root 3 * root 5 * root 7 * root 8 * root 9, root 4 * root 5 * root 8 * root 9, root 8, root 9]
private def gen : Fin 5 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 0, 0, 1, 1⟩, 1), (⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 584 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 5 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![7, 6, 5, 4, 2, 3, 0, 1], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 584 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[2]], [[0, 2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 584).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node584
namespace Node585
private def roots : Fin 5 → SylowModel := ![root 3 * root 6 * root 8, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 4 * root 5 * root 8 * root 9, root 8, root 9]
private def gen : Fin 5 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩, 1), (⟨0, 0, 0, 0, 1, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 585 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 1, 0, 1, 1, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 5 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![7, 6, 5, 4, 2, 3, 0, 1], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 585 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[2]], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 585).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node585
namespace Node587
private def roots : Fin 5 → SylowModel := ![root 0 * root 2 * root 3 * root 4 * root 6 * root 7, root 0 * root 1 * root 2 * root 3 * root 8, root 6 * root 8, root 5 * root 7 * root 8 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 587 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 16 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 5 → Fin 16 → Fin 16 := ![![9, 8, 11, 10, 12, 13, 14, 15, 1, 0, 3, 2, 4, 5, 6, 7], ![12, 13, 14, 15, 11, 10, 9, 8, 5, 4, 7, 6, 2, 3, 0, 1], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 587 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[0]], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 587).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node587
namespace Node589
private def roots : Fin 5 → SylowModel := ![root 0 * root 2 * root 3 * root 4 * root 6 * root 7, root 0 * root 1 * root 2 * root 3 * root 7 * root 8 * root 9, root 6 * root 8, root 5 * root 7 * root 8 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 589 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 16 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0)]
private def next : Fin 5 → Fin 16 → Fin 16 := ![![9, 8, 11, 10, 12, 13, 14, 15, 1, 0, 3, 2, 4, 5, 6, 7], ![12, 13, 14, 15, 11, 10, 9, 8, 5, 4, 7, 6, 2, 3, 0, 1], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 589 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[0]], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 589).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node589
namespace Node591
private def roots : Fin 5 → SylowModel := ![root 0 * root 4 * root 7 * root 8, root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 7, root 5 * root 6 * root 7 * root 8, root 6 * root 7 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 591 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 5 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 591 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[0, 1]], [[1], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 591).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node591
namespace Node592
private def roots : Fin 5 → SylowModel := ![root 0 * root 4 * root 8 * root 9, root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 7, root 5 * root 6 * root 7 * root 8, root 6 * root 7 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 592 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 5 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 592 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[1]], [[1], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 592).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node592
namespace Node593
private def roots : Fin 5 → SylowModel := ![root 0 * root 4 * root 7 * root 8, root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 593 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 0, 1, 1, 0⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 5 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 593 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[1]], [[1], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 593).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node593
namespace Node594
private def roots : Fin 5 → SylowModel := ![root 0 * root 4 * root 8 * root 9, root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 5 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 594 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 5 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 594 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[0, 1]], [[0, 1], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 594).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node594
namespace Node595
private def roots : Fin 5 → SylowModel := ![root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 9]
private def gen : Fin 5 → E := ![(⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 595 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 16 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 5 → Fin 16 → Fin 16 := ![![11, 10, 9, 8, 14, 15, 12, 13, 0, 1, 2, 3, 5, 4, 7, 6], ![7, 6, 5, 4, 1, 0, 3, 2, 12, 13, 14, 15, 10, 11, 8, 9], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 595 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[], [[0, 1], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 595).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node595
namespace Node596
private def roots : Fin 5 → SylowModel := ![root 0 * root 2 * root 4 * root 5 * root 6, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 9]
private def gen : Fin 5 → E := ![(⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 596 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨1, 0, 0, 0, 1, 0, 0, 0, 1, 1⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 5 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![1, 0, 3, 2], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 596 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[1]], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 596).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node596
namespace Node597
private def roots : Fin 5 → SylowModel := ![root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 8, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 9]
private def gen : Fin 5 → E := ![(⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 597 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 1⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 5 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![1, 0, 3, 2], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 597 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[1]], [[1], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 597).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node597
namespace Node598
private def roots : Fin 5 → SylowModel := ![root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 1 * root 3 * root 5 * root 6, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 9]
private def gen : Fin 5 → E := ![(⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 598 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)
private def rep : Fin 16 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 5 → Fin 16 → Fin 16 := ![![11, 10, 9, 8, 14, 15, 12, 13, 0, 1, 2, 3, 5, 4, 7, 6], ![7, 6, 5, 4, 1, 0, 3, 2, 12, 13, 14, 15, 10, 11, 8, 9], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 598 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 5 → List (List (Fin 5)) := ![[[0, 1], [1], [0]], [[0, 1], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 598).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node598
namespace Node599
private def roots : Fin 4 → SylowModel := ![rootOne ^ 2 * root 0 * root 3, root 9, root 2 * root 3 * root 4 * root 8, root 7 * root 9]
private def gen : Fin 4 → E := ![(⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 599 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 4 → Fin 4 → Fin 4 := ![![3, 2, 0, 1], ![0, 1, 2, 3], ![1, 0, 3, 2], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 599 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 4 → List (List (Fin 4)) := ![[[2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 599).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node599

/-- Checked witnesses at indices 550 through 599, excluding the prescribed survivors. -/
@[expose] public def block11 :
    List {i : Fin 600 // (smallEvenDescentNode i).HasFrattiniNormalizerWitness} :=
  [⟨550, by exact Node550.witness⟩,
  ⟨551, by exact Node551.witness⟩,
  ⟨552, by exact Node552.witness⟩,
  ⟨554, by exact Node554.witness⟩,
  ⟨555, by exact Node555.witness⟩,
  ⟨557, by exact Node557.witness⟩,
  ⟨558, by exact Node558.witness⟩,
  ⟨559, by exact Node559.witness⟩,
  ⟨561, by exact Node561.witness⟩,
  ⟨562, by exact Node562.witness⟩,
  ⟨563, by exact Node563.witness⟩,
  ⟨564, by exact Node564.witness⟩,
  ⟨565, by exact Node565.witness⟩,
  ⟨566, by exact Node566.witness⟩,
  ⟨567, by exact Node567.witness⟩,
  ⟨569, by exact Node569.witness⟩,
  ⟨570, by exact Node570.witness⟩,
  ⟨571, by exact Node571.witness⟩,
  ⟨572, by exact Node572.witness⟩,
  ⟨573, by exact Node573.witness⟩,
  ⟨574, by exact Node574.witness⟩,
  ⟨575, by exact Node575.witness⟩,
  ⟨577, by exact Node577.witness⟩,
  ⟨578, by exact Node578.witness⟩,
  ⟨579, by exact Node579.witness⟩,
  ⟨580, by exact Node580.witness⟩,
  ⟨583, by exact Node583.witness⟩,
  ⟨584, by exact Node584.witness⟩,
  ⟨585, by exact Node585.witness⟩,
  ⟨587, by exact Node587.witness⟩,
  ⟨589, by exact Node589.witness⟩,
  ⟨591, by exact Node591.witness⟩,
  ⟨592, by exact Node592.witness⟩,
  ⟨593, by exact Node593.witness⟩,
  ⟨594, by exact Node594.witness⟩,
  ⟨595, by exact Node595.witness⟩,
  ⟨596, by exact Node596.witness⟩,
  ⟨597, by exact Node597.witness⟩,
  ⟨598, by exact Node598.witness⟩,
  ⟨599, by exact Node599.witness⟩]

end ReeTwo.SylowModel.UpperCertificate
