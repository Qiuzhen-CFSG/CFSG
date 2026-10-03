module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeWitnessesUpperCoordinates

/-!
# Frattini witnesses for upper node block 8

Explicit projected orbits separate the proposed witnesses from the node
subgroups. Products of squares certify all generator displacements. The
coordinate bridge transfers these kernel-checked equations to the unchanged
root-word nodes.

Source: Shinoda (1975), (2.3), pp. 81–82, and the fixed node words in
`SmallEvenDescentNodes`. Certificate suggestions are verified here in Lean.
-/

namespace ReeTwo.SylowModel.UpperCertificate
set_option maxRecDepth 10000

namespace Node400
private def roots : Fin 6 → SylowModel := ![root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 400 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 1 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 1 → Fin 1 := ![![0], ![0], ![0], ![0], ![0], ![0]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 0 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 400 := by
  rw [generated]
  exact outside_of_projected_orbit gen 0 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[2]], [], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 400).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node400
namespace Node401
private def roots : Fin 6 → SylowModel := ![root 2 * root 4 * root 7 * root 8 * root 9, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 401 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 1 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 1 → Fin 1 := ![![0], ![0], ![0], ![0], ![0], ![0]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 0 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 401 := by
  rw [generated]
  exact outside_of_projected_orbit gen 0 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [], [[2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 401).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node401
namespace Node402
private def roots : Fin 6 → SylowModel := ![root 3, root 4 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 402 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 1 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 1 → Fin 1 := ![![0], ![0], ![0], ![0], ![0], ![0]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 0 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 402 := by
  rw [generated]
  exact outside_of_projected_orbit gen 0 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 402).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node402
namespace Node403
private def roots : Fin 6 → SylowModel := ![root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 403 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 1 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 1 → Fin 1 := ![![0], ![0], ![0], ![0], ![0], ![0]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 0 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 403 := by
  rw [generated]
  exact outside_of_projected_orbit gen 0 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 2]], [], [[2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 403).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node403
namespace Node404
private def roots : Fin 6 → SylowModel := ![root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 4 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 404 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1)
private def rep : Fin 1 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 1 → Fin 1 := ![![0], ![0], ![0], ![0], ![0], ![0]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 0 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 404 := by
  rw [generated]
  exact outside_of_projected_orbit gen 0 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0, 1], [0]], [[0, 1], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 404).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node404
namespace Node405
private def roots : Fin 6 → SylowModel := ![root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 405 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 1 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 1 → Fin 1 := ![![0], ![0], ![0], ![0], ![0], ![0]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 0 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 405 := by
  rw [generated]
  exact outside_of_projected_orbit gen 0 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1, 2], [2]], [], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 405).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node405
namespace Node406
private def roots : Fin 6 → SylowModel := ![root 3, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 406 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![1, 0, 3, 2], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 406 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 406).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node406
namespace Node407
private def roots : Fin 6 → SylowModel := ![root 3, root 4 * root 6 * root 9, root 5 * root 7 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 407 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![4, 5, 6, 7, 0, 1, 2, 3], ![2, 3, 0, 1, 6, 7, 4, 5], ![1, 0, 3, 2, 5, 4, 7, 6], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 407 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [], [[1, 2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 407).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node407
namespace Node408
private def roots : Fin 6 → SylowModel := ![root 3 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 8, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 408 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 1 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 1 → Fin 1 := ![![0], ![0], ![0], ![0], ![0], ![0]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 0 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 408 := by
  rw [generated]
  exact outside_of_projected_orbit gen 0 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 2]], [], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 408).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node408
namespace Node409
private def roots : Fin 6 → SylowModel := ![root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 4 * root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 1, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 409 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![3, 2, 1, 0], ![1, 0, 3, 2], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 409 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1], [0]], [[1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 409).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node409
namespace Node410
private def roots : Fin 6 → SylowModel := ![root 0 * root 2 * root 5 * root 6 * root 9, root 6 * root 7 * root 8 * root 9, root 5 * root 9, root 7, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 410 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 2 → Fin 2 := ![![1, 0], ![0, 1], ![0, 1], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 410 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 1]], [[0, 1], [0]], [], [], [[0, 1], [0]], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 410).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node410
namespace Node411
private def roots : Fin 6 → SylowModel := ![root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 411 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![6, 7, 4, 5, 2, 3, 0, 1], ![7, 6, 5, 4, 3, 2, 1, 0], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 411 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0]], [[2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 411).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node411
namespace Node412
private def roots : Fin 6 → SylowModel := ![root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 412 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![7, 6, 5, 4, 3, 2, 1, 0], ![6, 7, 4, 5, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 412 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[1, 2], [0]], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 412).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node412
namespace Node413
private def roots : Fin 6 → SylowModel := ![root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 413 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![1, 0, 3, 2, 5, 4, 7, 6], ![7, 6, 5, 4, 3, 2, 1, 0], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 413 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0]], [[2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 413).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node413
namespace Node414
private def roots : Fin 6 → SylowModel := ![root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 414 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![1, 0, 3, 2, 5, 4, 7, 6], ![7, 6, 5, 4, 3, 2, 1, 0], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 414 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0]], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 414).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node414
namespace Node415
private def roots : Fin 6 → SylowModel := ![root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 2 * root 3 * root 4, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 415 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![6, 7, 4, 5, 2, 3, 0, 1], ![7, 6, 5, 4, 3, 2, 1, 0], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 415 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 415).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node415
namespace Node416
private def roots : Fin 6 → SylowModel := ![root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 416 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![7, 6, 5, 4, 3, 2, 1, 0], ![6, 7, 4, 5, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 416 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[1, 2], [0]], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 416).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node416
namespace Node417
private def roots : Fin 6 → SylowModel := ![root 3 * root 4 * root 6 * root 9, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 417 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![1, 0, 3, 2, 5, 4, 7, 6], ![6, 7, 4, 5, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 417 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 1], [2], [0]], [], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 417).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node417
namespace Node418
private def roots : Fin 6 → SylowModel := ![root 3 * root 4 * root 6 * root 9, rootOne ^ 2, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 418 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![1, 0, 3, 2, 5, 4, 7, 6], ![6, 7, 4, 5, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 418 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[2], [0]], [[1, 2], [0]], [[0, 1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 418).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node418
namespace Node419
private def roots : Fin 6 → SylowModel := ![root 3 * root 4 * root 6 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 419 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![6, 7, 4, 5, 2, 3, 0, 1], ![7, 6, 5, 4, 3, 2, 1, 0], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 419 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 1], [0]], [[0, 1], [0]], [[2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 419).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node419
namespace Node420
private def roots : Fin 6 → SylowModel := ![root 3 * root 4 * root 6 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 420 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![7, 6, 5, 4, 3, 2, 1, 0], ![6, 7, 4, 5, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 420 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 2], [0]], [[0, 1], [0]], [[0, 2], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 420).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node420
namespace Node421
private def roots : Fin 6 → SylowModel := ![root 2 * root 8, rootOne ^ 2, root 5 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 421 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![1, 0, 3, 2], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 421 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1, 2], [0]], [], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 421).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node421
namespace Node422
private def roots : Fin 6 → SylowModel := ![root 3 * root 4 * root 6 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 422 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![3, 2, 1, 0, 7, 6, 5, 4], ![1, 0, 3, 2, 5, 4, 7, 6], ![7, 6, 5, 4, 3, 2, 1, 0], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 422 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1]], [[1]], [[2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 422).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node422
namespace Node423
private def roots : Fin 6 → SylowModel := ![root 3 * root 4 * root 6 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 423 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![3, 2, 1, 0, 7, 6, 5, 4], ![1, 0, 3, 2, 5, 4, 7, 6], ![7, 6, 5, 4, 3, 2, 1, 0], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 423 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1]], [[1]], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 423).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node423
namespace Node424
private def roots : Fin 6 → SylowModel := ![root 3 * root 4 * root 6 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 424 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![6, 7, 4, 5, 2, 3, 0, 1], ![7, 6, 5, 4, 3, 2, 1, 0], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 424 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 2], [0]], [], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 424).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node424
namespace Node425
private def roots : Fin 6 → SylowModel := ![root 3 * root 4 * root 6 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 425 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![7, 6, 5, 4, 3, 2, 1, 0], ![6, 7, 4, 5, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 425 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 2], [0]], [[2], [0]], [[0, 2], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 425).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node425
namespace Node426
private def roots : Fin 6 → SylowModel := ![root 2 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 5 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 426 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 426 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[1]], [[1, 2], [1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 426).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node426
namespace Node427
private def roots : Fin 6 → SylowModel := ![root 3 * root 4 * root 7 * root 8, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 427 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![1, 0, 3, 2, 5, 4, 7, 6], ![6, 7, 4, 5, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 427 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[2], [0]], [[0, 2], [2]], [[0, 2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 427).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node427
namespace Node428
private def roots : Fin 6 → SylowModel := ![root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 428 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![7, 6, 5, 4, 3, 2, 1, 0], ![6, 7, 4, 5, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 428 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0, 2], [2]], [[0, 2], [2], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 428).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node428
namespace Node429
private def roots : Fin 6 → SylowModel := ![root 2 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 429 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![6, 7, 4, 5, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 429 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 2], [2], [0]], [[2], [0]], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 429).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node429
namespace Node430
private def roots : Fin 6 → SylowModel := ![root 2 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 430 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 5 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 430 := by
  rw [generated]
  exact outside_of_projected_orbit gen 5 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1, 2]], [[1, 2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 430).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node430
namespace Node431
private def roots : Fin 6 → SylowModel := ![root 2 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 431 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![5, 4, 7, 6, 1, 0, 3, 2], ![7, 6, 5, 4, 3, 2, 1, 0], ![6, 7, 4, 5, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 431 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[2], [0]], [[2], [0]], [[0, 2], [2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 431).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node431
namespace Node432
private def roots : Fin 6 → SylowModel := ![root 3 * root 4 * root 7 * root 8, rootOne ^ 2, root 2 * root 3 * root 4, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 432 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![1, 0, 3, 2, 5, 4, 7, 6], ![6, 7, 4, 5, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 432 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 2], [2], [0]], [[2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 432).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node432
namespace Node433
private def roots : Fin 6 → SylowModel := ![root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 2 * root 3 * root 4, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 433 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![7, 6, 5, 4, 3, 2, 1, 0], ![6, 7, 4, 5, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 433 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 433).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node433
namespace Node434
private def roots : Fin 6 → SylowModel := ![root 2 * root 6 * root 7, rootOne ^ 2, root 2 * root 3 * root 4, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 434 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![6, 7, 4, 5, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 434 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 1], [2], [0]], [[2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 434).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node434
namespace Node435
private def roots : Fin 6 → SylowModel := ![root 2 * root 6 * root 7, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 2 * root 3 * root 4, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 435 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![5, 4, 7, 6, 1, 0, 3, 2], ![7, 6, 5, 4, 3, 2, 1, 0], ![6, 7, 4, 5, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 435 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 1]], [[0, 1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 435).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node435
namespace Node436
private def roots : Fin 6 → SylowModel := ![root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 436 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![7, 6, 5, 4, 3, 2, 1, 0], ![6, 7, 4, 5, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 436 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 436).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node436
namespace Node437
private def roots : Fin 6 → SylowModel := ![root 2 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 4, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 437 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![6, 7, 4, 5, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 437 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 2], [0, 1]], [[2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 437).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node437
namespace Node438
private def roots : Fin 6 → SylowModel := ![root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 438 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![6, 7, 4, 5, 2, 3, 0, 1], ![7, 6, 5, 4, 3, 2, 1, 0], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 438 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0]], [[1, 2], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 438).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node438
namespace Node439
private def roots : Fin 6 → SylowModel := ![root 2 * root 6 * root 7, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 439 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![4, 5, 6, 7, 0, 1, 2, 3], ![6, 7, 4, 5, 2, 3, 0, 1], ![7, 6, 5, 4, 3, 2, 1, 0], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 439 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 1]], [[0, 1]], [[1], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 439).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node439
namespace Node440
private def roots : Fin 6 → SylowModel := ![root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 5 * root 7 * root 8, root 2 * root 3 * root 4, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 440 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![1, 0, 3, 2, 5, 4, 7, 6], ![6, 7, 4, 5, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 440 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 440).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node440
namespace Node441
private def roots : Fin 6 → SylowModel := ![root 3 * root 4 * root 7 * root 8, rootOne ^ 2 * root 5 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 7 * root 8, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 441 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![1, 0, 3, 2, 5, 4, 7, 6], ![7, 6, 5, 4, 3, 2, 1, 0], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 441 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[1]], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 441).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node441
namespace Node442
private def roots : Fin 6 → SylowModel := ![root 2 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 6 * root 7 * root 8 * root 9, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 442 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 442 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1, 2]], [[0, 1], [1]], [[0, 1], [1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 442).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node442
namespace Node443
private def roots : Fin 6 → SylowModel := ![root 2 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 443 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![5, 4, 7, 6, 1, 0, 3, 2], ![6, 7, 4, 5, 2, 3, 0, 1], ![7, 6, 5, 4, 3, 2, 1, 0], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 443 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1, 2]], [[0, 2], [0]], [[1], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 443).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node443
namespace Node444
private def roots : Fin 6 → SylowModel := ![root 2 * root 6 * root 7, rootOne ^ 2 * root 5 * root 7 * root 8, root 2 * root 3 * root 4, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 444 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![6, 7, 4, 5, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 444 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 2], [0]], [[1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 444).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node444
namespace Node445
private def roots : Fin 6 → SylowModel := ![root 0, root 0 * root 2 * root 5 * root 6 * root 9, root 6 * root 7 * root 9, root 7, root 5, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 445 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![30, 31, 28, 29, 26, 27, 24, 25, 22, 23, 20, 21, 18, 19, 16, 17, 10, 11, 8, 9, 14, 15, 12, 13, 2, 3, 0, 1, 6, 7, 4, 5], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 445 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 1]], [[0, 1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 445).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node445
namespace Node446
private def roots : Fin 6 → SylowModel := ![root 0 * root 8, root 0 * root 2 * root 5 * root 6 * root 9, root 6 * root 7 * root 9, root 7, root 5, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 446 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![30, 31, 28, 29, 26, 27, 24, 25, 22, 23, 20, 21, 18, 19, 16, 17, 10, 11, 8, 9, 14, 15, 12, 13, 2, 3, 0, 1, 6, 7, 4, 5], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 446 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0]], [[0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 446).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node446
namespace Node447
private def roots : Fin 6 → SylowModel := ![rootOne ^ 2 * root 3, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 447 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![1, 0, 3, 2], ![0, 1, 2, 3], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 447 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [], [[2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 447).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node447
namespace Node448
private def roots : Fin 6 → SylowModel := ![rootOne ^ 2 * root 3, root 2 * root 3 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 448 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![1, 0, 3, 2], ![3, 2, 1, 0], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 448 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [], [[2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 448).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node448
namespace Node449
private def roots : Fin 6 → SylowModel := ![rootOne ^ 2 * root 3, root 2 * root 3 * root 5 * root 6 * root 9, root 2 * root 3 * root 4 * root 9, root 7 * root 9, root 8 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 449 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![1, 0, 3, 2], ![3, 2, 1, 0], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 449 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 449).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node449

/-- Checked witnesses at indices 400 through 449, excluding the prescribed survivors. -/
@[expose] public def block8 :
    List {i : Fin 600 // (smallEvenDescentNode i).HasFrattiniNormalizerWitness} :=
  [⟨400, by exact Node400.witness⟩,
  ⟨401, by exact Node401.witness⟩,
  ⟨402, by exact Node402.witness⟩,
  ⟨403, by exact Node403.witness⟩,
  ⟨404, by exact Node404.witness⟩,
  ⟨405, by exact Node405.witness⟩,
  ⟨406, by exact Node406.witness⟩,
  ⟨407, by exact Node407.witness⟩,
  ⟨408, by exact Node408.witness⟩,
  ⟨409, by exact Node409.witness⟩,
  ⟨410, by exact Node410.witness⟩,
  ⟨411, by exact Node411.witness⟩,
  ⟨412, by exact Node412.witness⟩,
  ⟨413, by exact Node413.witness⟩,
  ⟨414, by exact Node414.witness⟩,
  ⟨415, by exact Node415.witness⟩,
  ⟨416, by exact Node416.witness⟩,
  ⟨417, by exact Node417.witness⟩,
  ⟨418, by exact Node418.witness⟩,
  ⟨419, by exact Node419.witness⟩,
  ⟨420, by exact Node420.witness⟩,
  ⟨421, by exact Node421.witness⟩,
  ⟨422, by exact Node422.witness⟩,
  ⟨423, by exact Node423.witness⟩,
  ⟨424, by exact Node424.witness⟩,
  ⟨425, by exact Node425.witness⟩,
  ⟨426, by exact Node426.witness⟩,
  ⟨427, by exact Node427.witness⟩,
  ⟨428, by exact Node428.witness⟩,
  ⟨429, by exact Node429.witness⟩,
  ⟨430, by exact Node430.witness⟩,
  ⟨431, by exact Node431.witness⟩,
  ⟨432, by exact Node432.witness⟩,
  ⟨433, by exact Node433.witness⟩,
  ⟨434, by exact Node434.witness⟩,
  ⟨435, by exact Node435.witness⟩,
  ⟨436, by exact Node436.witness⟩,
  ⟨437, by exact Node437.witness⟩,
  ⟨438, by exact Node438.witness⟩,
  ⟨439, by exact Node439.witness⟩,
  ⟨440, by exact Node440.witness⟩,
  ⟨441, by exact Node441.witness⟩,
  ⟨442, by exact Node442.witness⟩,
  ⟨443, by exact Node443.witness⟩,
  ⟨444, by exact Node444.witness⟩,
  ⟨445, by exact Node445.witness⟩,
  ⟨446, by exact Node446.witness⟩,
  ⟨447, by exact Node447.witness⟩,
  ⟨448, by exact Node448.witness⟩,
  ⟨449, by exact Node449.witness⟩]

end ReeTwo.SylowModel.UpperCertificate
