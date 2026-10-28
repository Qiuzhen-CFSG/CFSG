module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenNodeWitnessesUpperCoordinates

/-!
# Frattini witnesses for upper node block 6

Explicit projected orbits separate the proposed witnesses from the node
subgroups. Products of squares certify all generator displacements. The
coordinate bridge transfers these kernel-checked equations to the unchanged
root-word nodes.

Source: Shinoda (1975), (2.3), pp. 81–82, and the fixed node words in
`SmallEvenDescentNodes`. Certificate suggestions are verified here in Lean.
-/

namespace ReeTwo.SylowModel.UpperCertificate
set_option maxRecDepth 10000

namespace Node300
private def roots : Fin 7 → SylowModel := ![root 0 * root 2 * root 5 * root 6 * root 9, root 1 * root 3 * root 4 * root 5 * root 6 * root 8, root 5 * root 6 * root 7 * root 8 * root 9, root 6 * root 7, root 7 * root 8, root 8 * root 9, root 9]
private def gen : Fin 7 → E := ![(⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 300 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 7 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![1, 0, 3, 2], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 3 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 300 := by
  rw [generated]
  exact outside_of_projected_orbit gen 3 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 7 → List (List (Fin 7)) := ![[[0, 2]], [[1]], [[0, 2], [0]], [], [[0, 2], [0]], [[0, 2], [0]], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 300).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node300
namespace Node301
private def roots : Fin 7 → SylowModel := ![rootOne ^ 2 * root 3 * root 6 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8, root 4 * root 7 * root 8, root 8, root 7 * root 8 * root 9, root 9]
private def gen : Fin 7 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 301 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 7 → Fin 4 → Fin 4 := ![![1, 0, 3, 2], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 301 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 7 → List (List (Fin 7)) := ![[[0]], [[0]], [], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 301).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node301
namespace Node302
private def roots : Fin 7 → SylowModel := ![root 1 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 8, root 5 * root 9, root 4 * root 9, root 8, root 7 * root 8, root 9]
private def gen : Fin 7 → E := ![(⟨0, 1, 0, 0, 0, 1, 1, 1, 1, 1⟩, 0), (⟨0, 1, 0, 1, 1, 1, 0, 1, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 302 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 7 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 302 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 7 → List (List (Fin 7)) := ![[[2, 3]], [[1], [0]], [], [[0, 3], [0]], [], [[2, 3]], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 302).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node302
namespace Node303
private def roots : Fin 7 → SylowModel := ![root 0, root 0 * root 3 * root 5 * root 6 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 9, root 6 * root 8 * root 9, root 8, root 9]
private def gen : Fin 7 → E := ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 303 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 7 → Fin 32 → Fin 32 := ![![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![23, 22, 21, 20, 19, 18, 17, 16, 31, 30, 29, 28, 27, 26, 25, 24, 4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![15, 14, 13, 12, 11, 10, 9, 8, 5, 4, 7, 6, 1, 0, 3, 2, 28, 29, 30, 31, 24, 25, 26, 27, 22, 23, 20, 21, 18, 19, 16, 17], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 303 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 7 → List (List (Fin 7)) := ![[[0, 4]], [[0, 4]], [[0, 4]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 303).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node303
namespace Node304
private def roots : Fin 7 → SylowModel := ![root 0, root 0 * root 3 * root 5 * root 6 * root 9, root 1 * root 3 * root 5 * root 6, root 5 * root 6 * root 9, root 6 * root 8 * root 9, root 8, root 9]
private def gen : Fin 7 → E := ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 304 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 7 → Fin 32 → Fin 32 := ![![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], ![23, 22, 21, 20, 19, 18, 17, 16, 31, 30, 29, 28, 27, 26, 25, 24, 4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11], ![15, 14, 13, 12, 11, 10, 9, 8, 5, 4, 7, 6, 1, 0, 3, 2, 28, 29, 30, 31, 24, 25, 26, 27, 22, 23, 20, 21, 18, 19, 16, 17], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 304 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 7 → List (List (Fin 7)) := ![[[1, 3], [0, 1]], [[0, 1], [1]], [[0, 4]], [[0, 4]], [[0, 4]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 304).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node304
namespace Node305
private def roots : Fin 7 → SylowModel := ![root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7 * root 9, root 6 * root 7 * root 8, root 8, root 9]
private def gen : Fin 7 → E := ![(⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 305 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 7 → Fin 32 → Fin 32 := ![![20, 21, 22, 23, 16, 17, 18, 19, 29, 28, 31, 30, 25, 24, 27, 26, 4, 5, 6, 7, 0, 1, 2, 3, 13, 12, 15, 14, 9, 8, 11, 10], ![19, 18, 17, 16, 23, 22, 21, 20, 26, 27, 24, 25, 30, 31, 28, 29, 0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14], ![15, 14, 13, 12, 11, 10, 9, 8, 5, 4, 7, 6, 1, 0, 3, 2, 28, 29, 30, 31, 24, 25, 26, 27, 22, 23, 20, 21, 18, 19, 16, 17], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 305 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 7 → List (List (Fin 7)) := ![[[0, 2]], [], [[0, 2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 305).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node305
namespace Node306
private def roots : Fin 7 → SylowModel := ![root 0 * root 2 * root 3 * root 4 * root 7, root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 6 * root 7 * root 9, root 6 * root 7 * root 8, root 8, root 9]
private def gen : Fin 7 → E := ![(⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 306 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 7 → Fin 32 → Fin 32 := ![![20, 21, 22, 23, 16, 17, 18, 19, 29, 28, 31, 30, 25, 24, 27, 26, 4, 5, 6, 7, 0, 1, 2, 3, 13, 12, 15, 14, 9, 8, 11, 10], ![19, 18, 17, 16, 23, 22, 21, 20, 26, 27, 24, 25, 30, 31, 28, 29, 0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14], ![15, 14, 13, 12, 11, 10, 9, 8, 5, 4, 7, 6, 1, 0, 3, 2, 28, 29, 30, 31, 24, 25, 26, 27, 22, 23, 20, 21, 18, 19, 16, 17], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 306 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 7 → List (List (Fin 7)) := ![[[0, 2]], [], [[0, 2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 306).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node306
namespace Node307
private def roots : Fin 7 → SylowModel := ![root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 7 * root 9, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 7 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 307 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0)
private def rep : Fin 64 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 7 → Fin 64 → Fin 64 := ![![33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28], ![47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 60, 61, 62, 63, 56, 57, 58, 59, 52, 53, 54, 55, 48, 49, 50, 51, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 27, 26, 25, 24, 31, 30, 29, 28, 19, 18, 17, 16, 23, 22, 21, 20], ![23, 22, 21, 20, 19, 18, 17, 16, 30, 31, 28, 29, 26, 27, 24, 25, 3, 2, 1, 0, 7, 6, 5, 4, 10, 11, 8, 9, 14, 15, 12, 13, 49, 48, 51, 50, 53, 52, 55, 54, 56, 57, 58, 59, 60, 61, 62, 63, 37, 36, 39, 38, 33, 32, 35, 34, 44, 45, 46, 47, 40, 41, 42, 43], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 49, 48, 51, 50, 53, 52, 55, 54, 57, 56, 59, 58, 61, 60, 63, 62], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27, 36, 37, 38, 39, 32, 33, 34, 35, 44, 45, 46, 47, 40, 41, 42, 43, 52, 53, 54, 55, 48, 49, 50, 51, 60, 61, 62, 63, 56, 57, 58, 59], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28, 35, 34, 33, 32, 39, 38, 37, 36, 43, 42, 41, 40, 47, 46, 45, 44, 51, 50, 49, 48, 55, 54, 53, 52, 59, 58, 57, 56, 63, 62, 61, 60], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 307 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 7 → List (List (Fin 7)) := ![[[0, 1]], [[0, 1]], [[0, 1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 307).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node307
namespace Node308
private def roots : Fin 7 → SylowModel := ![root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 7 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 308 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 7 → Fin 32 → Fin 32 := ![![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![23, 22, 21, 20, 19, 18, 17, 16, 30, 31, 28, 29, 26, 27, 24, 25, 4, 5, 6, 7, 0, 1, 2, 3, 13, 12, 15, 14, 9, 8, 11, 10], ![11, 10, 9, 8, 15, 14, 13, 12, 1, 0, 3, 2, 5, 4, 7, 6, 24, 25, 26, 27, 28, 29, 30, 31, 18, 19, 16, 17, 22, 23, 20, 21], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 308 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 7 → List (List (Fin 7)) := ![[], [], [[0, 1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 308).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node308
namespace Node309
private def roots : Fin 7 → SylowModel := ![root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 7 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 309 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 64 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 7 → Fin 64 → Fin 64 := ![![33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28], ![47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 60, 61, 62, 63, 56, 57, 58, 59, 52, 53, 54, 55, 48, 49, 50, 51, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 27, 26, 25, 24, 31, 30, 29, 28, 19, 18, 17, 16, 23, 22, 21, 20], ![23, 22, 21, 20, 19, 18, 17, 16, 30, 31, 28, 29, 26, 27, 24, 25, 3, 2, 1, 0, 7, 6, 5, 4, 10, 11, 8, 9, 14, 15, 12, 13, 49, 48, 51, 50, 53, 52, 55, 54, 56, 57, 58, 59, 60, 61, 62, 63, 37, 36, 39, 38, 33, 32, 35, 34, 44, 45, 46, 47, 40, 41, 42, 43], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 49, 48, 51, 50, 53, 52, 55, 54, 57, 56, 59, 58, 61, 60, 63, 62], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27, 36, 37, 38, 39, 32, 33, 34, 35, 44, 45, 46, 47, 40, 41, 42, 43, 52, 53, 54, 55, 48, 49, 50, 51, 60, 61, 62, 63, 56, 57, 58, 59], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28, 35, 34, 33, 32, 39, 38, 37, 36, 43, 42, 41, 40, 47, 46, 45, 44, 51, 50, 49, 48, 55, 54, 53, 52, 59, 58, 57, 56, 63, 62, 61, 60], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 309 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 7 → List (List (Fin 7)) := ![[], [], [[0, 1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 309).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node309
namespace Node310
private def roots : Fin 7 → SylowModel := ![root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 8, root 7 * root 9, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 7 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 310 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)
private def rep : Fin 64 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 7 → Fin 64 → Fin 64 := ![![33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28], ![47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 60, 61, 62, 63, 56, 57, 58, 59, 52, 53, 54, 55, 48, 49, 50, 51, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 27, 26, 25, 24, 31, 30, 29, 28, 19, 18, 17, 16, 23, 22, 21, 20], ![23, 22, 21, 20, 19, 18, 17, 16, 30, 31, 28, 29, 26, 27, 24, 25, 3, 2, 1, 0, 7, 6, 5, 4, 10, 11, 8, 9, 14, 15, 12, 13, 49, 48, 51, 50, 53, 52, 55, 54, 56, 57, 58, 59, 60, 61, 62, 63, 37, 36, 39, 38, 33, 32, 35, 34, 44, 45, 46, 47, 40, 41, 42, 43], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 49, 48, 51, 50, 53, 52, 55, 54, 57, 56, 59, 58, 61, 60, 63, 62], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27, 36, 37, 38, 39, 32, 33, 34, 35, 44, 45, 46, 47, 40, 41, 42, 43, 52, 53, 54, 55, 48, 49, 50, 51, 60, 61, 62, 63, 56, 57, 58, 59], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28, 35, 34, 33, 32, 39, 38, 37, 36, 43, 42, 41, 40, 47, 46, 45, 44, 51, 50, 49, 48, 55, 54, 53, 52, 59, 58, 57, 56, 63, 62, 61, 60], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 310 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 7 → List (List (Fin 7)) := ![[[1]], [[2, 3]], [], [[0, 1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 310).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node310
namespace Node311
private def roots : Fin 7 → SylowModel := ![root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 8, root 7 * root 8, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 7 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 311 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)
private def rep : Fin 64 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 7 → Fin 64 → Fin 64 := ![![33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28], ![47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 60, 61, 62, 63, 56, 57, 58, 59, 52, 53, 54, 55, 48, 49, 50, 51, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 27, 26, 25, 24, 31, 30, 29, 28, 19, 18, 17, 16, 23, 22, 21, 20], ![23, 22, 21, 20, 19, 18, 17, 16, 30, 31, 28, 29, 26, 27, 24, 25, 3, 2, 1, 0, 7, 6, 5, 4, 10, 11, 8, 9, 14, 15, 12, 13, 49, 48, 51, 50, 53, 52, 55, 54, 56, 57, 58, 59, 60, 61, 62, 63, 37, 36, 39, 38, 33, 32, 35, 34, 44, 45, 46, 47, 40, 41, 42, 43], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 49, 48, 51, 50, 53, 52, 55, 54, 57, 56, 59, 58, 61, 60, 63, 62], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27, 36, 37, 38, 39, 32, 33, 34, 35, 44, 45, 46, 47, 40, 41, 42, 43, 52, 53, 54, 55, 48, 49, 50, 51, 60, 61, 62, 63, 56, 57, 58, 59], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28, 35, 34, 33, 32, 39, 38, 37, 36, 43, 42, 41, 40, 47, 46, 45, 44, 51, 50, 49, 48, 55, 54, 53, 52, 59, 58, 57, 56, 63, 62, 61, 60], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 311 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 7 → List (List (Fin 7)) := ![[[1]], [[2, 3]], [], [[0, 1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 311).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node311
namespace Node312
private def roots : Fin 7 → SylowModel := ![root 0 * root 4 * root 7 * root 8, root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 7 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 1⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 312 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 7 → Fin 32 → Fin 32 := ![![16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![23, 22, 21, 20, 19, 18, 17, 16, 30, 31, 28, 29, 26, 27, 24, 25, 4, 5, 6, 7, 0, 1, 2, 3, 13, 12, 15, 14, 9, 8, 11, 10], ![11, 10, 9, 8, 15, 14, 13, 12, 1, 0, 3, 2, 5, 4, 7, 6, 24, 25, 26, 27, 28, 29, 30, 31, 18, 19, 16, 17, 22, 23, 20, 21], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21, 26, 27, 24, 25, 30, 31, 28, 29], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 8 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 312 := by
  rw [generated]
  exact outside_of_projected_orbit gen 8 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 7 → List (List (Fin 7)) := ![[], [], [[0, 1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 312).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node312
namespace Node313
private def roots : Fin 7 → SylowModel := ![root 0 * root 4 * root 7 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 7 * root 8, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 7 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 313 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 64 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0)]
private def next : Fin 7 → Fin 64 → Fin 64 := ![![33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28], ![47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 60, 61, 62, 63, 56, 57, 58, 59, 52, 53, 54, 55, 48, 49, 50, 51, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 27, 26, 25, 24, 31, 30, 29, 28, 19, 18, 17, 16, 23, 22, 21, 20], ![23, 22, 21, 20, 19, 18, 17, 16, 30, 31, 28, 29, 26, 27, 24, 25, 3, 2, 1, 0, 7, 6, 5, 4, 10, 11, 8, 9, 14, 15, 12, 13, 49, 48, 51, 50, 53, 52, 55, 54, 56, 57, 58, 59, 60, 61, 62, 63, 37, 36, 39, 38, 33, 32, 35, 34, 44, 45, 46, 47, 40, 41, 42, 43], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 49, 48, 51, 50, 53, 52, 55, 54, 57, 56, 59, 58, 61, 60, 63, 62], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27, 36, 37, 38, 39, 32, 33, 34, 35, 44, 45, 46, 47, 40, 41, 42, 43, 52, 53, 54, 55, 48, 49, 50, 51, 60, 61, 62, 63, 56, 57, 58, 59], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28, 35, 34, 33, 32, 39, 38, 37, 36, 43, 42, 41, 40, 47, 46, 45, 44, 51, 50, 49, 48, 55, 54, 53, 52, 59, 58, 57, 56, 63, 62, 61, 60], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 313 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 7 → List (List (Fin 7)) := ![[], [], [[0, 1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 313).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node313
namespace Node314
private def roots : Fin 7 → SylowModel := ![root 0 * root 4 * root 7 * root 9, root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 1 * root 3 * root 5 * root 6 * root 7 * root 8, root 7 * root 8, root 5 * root 8 * root 9, root 6 * root 7 * root 9, root 9]
private def gen : Fin 7 → E := ![(⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 1⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 314 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)
private def rep : Fin 64 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 0, 1, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 0, 1, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 0, 1, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 1, 0, 1, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 0, 1, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 1, 1, 1, 0, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 0, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 0, 1, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨1, 1, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0)]
private def next : Fin 7 → Fin 64 → Fin 64 := ![![33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13, 19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28], ![47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, 60, 61, 62, 63, 56, 57, 58, 59, 52, 53, 54, 55, 48, 49, 50, 51, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 27, 26, 25, 24, 31, 30, 29, 28, 19, 18, 17, 16, 23, 22, 21, 20], ![23, 22, 21, 20, 19, 18, 17, 16, 30, 31, 28, 29, 26, 27, 24, 25, 3, 2, 1, 0, 7, 6, 5, 4, 10, 11, 8, 9, 14, 15, 12, 13, 49, 48, 51, 50, 53, 52, 55, 54, 56, 57, 58, 59, 60, 61, 62, 63, 37, 36, 39, 38, 33, 32, 35, 34, 44, 45, 46, 47, 40, 41, 42, 43], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 41, 40, 43, 42, 45, 44, 47, 46, 49, 48, 51, 50, 53, 52, 55, 54, 57, 56, 59, 58, 61, 60, 63, 62], ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27, 36, 37, 38, 39, 32, 33, 34, 35, 44, 45, 46, 47, 40, 41, 42, 43, 52, 53, 54, 55, 48, 49, 50, 51, 60, 61, 62, 63, 56, 57, 58, 59], ![3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12, 19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28, 35, 34, 33, 32, 39, 38, 37, 36, 43, 42, 41, 40, 47, 46, 45, 44, 51, 50, 49, 48, 55, 54, 53, 52, 59, 58, 57, 56, 63, 62, 61, 60], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 314 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 7 → List (List (Fin 7)) := ![[[1]], [[2, 3]], [], [[0, 1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 314).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node314
namespace Node315
private def roots : Fin 6 → SylowModel := ![rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 315 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 2 → Fin 2 := ![![1, 0], ![0, 1], ![0, 1], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 1 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 315 := by
  rw [generated]
  exact outside_of_projected_orbit gen 1 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0]], [[0, 3], [0]], [[0, 3], [0]], [[0, 2], [0]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 315).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node315
namespace Node316
private def roots : Fin 6 → SylowModel := ![root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 316 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 1 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 1 → Fin 1 := ![![0], ![0], ![0], ![0], ![0], ![0]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 0 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 316 := by
  rw [generated]
  exact outside_of_projected_orbit gen 0 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 316).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node316
namespace Node317
private def roots : Fin 6 → SylowModel := ![root 0 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 317 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![7, 6, 5, 4, 2, 3, 0, 1], ![3, 2, 1, 0, 7, 6, 5, 4], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 317 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0, 3], [0]], [[0, 3], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 317).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node317
namespace Node318
private def roots : Fin 6 → SylowModel := ![rootOne ^ 2 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 318 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![1, 0, 3, 2], ![3, 2, 1, 0], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 318 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 318).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node318
namespace Node320
private def roots : Fin 6 → SylowModel := ![root 0, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 320 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![4, 5, 6, 7, 0, 1, 2, 3], ![6, 7, 4, 5, 1, 0, 3, 2], ![3, 2, 1, 0, 7, 6, 5, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 320 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[2]], [[2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 320).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node320
namespace Node321
private def roots : Fin 6 → SylowModel := ![root 0, rootOne ^ 2 * root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 321 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨1, 0, 0, 1, 0, 1, 1, 0, 1, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![4, 5, 6, 7, 0, 1, 2, 3], ![5, 4, 7, 6, 2, 3, 0, 1], ![3, 2, 1, 0, 7, 6, 5, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 321 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1, 2], [0, 1]], [[2]], [[0, 3]], [[0, 3]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 321).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node321
namespace Node322
private def roots : Fin 6 → SylowModel := ![root 3, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 322 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 0, 0, 1, 1, 0, 0⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![1, 0, 3, 2, 5, 4, 7, 6], ![6, 7, 4, 5, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 5 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 322 := by
  rw [generated]
  exact outside_of_projected_orbit gen 5 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[2]], [[0]], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 322).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node322
namespace Node323
private def roots : Fin 6 → SylowModel := ![root 3, rootOne ^ 2, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 323 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![1, 0, 3, 2, 5, 4, 7, 6], ![6, 7, 4, 5, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 323 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[2]], [[2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 323).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node323
namespace Node324
private def roots : Fin 6 → SylowModel := ![root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 324 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![6, 7, 4, 5, 2, 3, 0, 1], ![7, 6, 5, 4, 3, 2, 1, 0], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 324 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [], [[1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 324).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node324
namespace Node325
private def roots : Fin 6 → SylowModel := ![root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 325 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![7, 6, 5, 4, 3, 2, 1, 0], ![6, 7, 4, 5, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 325 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 325).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node325
namespace Node326
private def roots : Fin 6 → SylowModel := ![root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2, root 5 * root 6 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 326 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![2, 3, 0, 1], ![1, 0, 3, 2], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 326 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1, 2]], [[1, 2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 326).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node326
namespace Node327
private def roots : Fin 6 → SylowModel := ![root 3 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 327 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 1 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 1 → Fin 1 := ![![0], ![0], ![0], ![0], ![0], ![0]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 0 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 327 := by
  rw [generated]
  exact outside_of_projected_orbit gen 0 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 1]], [[1]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 327).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node327
namespace Node328
private def roots : Fin 6 → SylowModel := ![rootOne ^ 2 * root 0 * root 3, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 328 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![3, 2, 0, 1], ![0, 1, 2, 3], ![1, 0, 3, 2], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 328 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[2]], [[0, 2], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 328).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node328
namespace Node329
private def roots : Fin 6 → SylowModel := ![rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 329 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨1, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 1), (⟨1, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 1), (⟨1, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![7, 6, 5, 4, 1, 0, 3, 2], ![3, 2, 1, 0, 7, 6, 5, 4], ![2, 3, 0, 1, 6, 7, 4, 5], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 329 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[2]], [[0, 2], [0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 329).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node329
namespace Node330
private def roots : Fin 6 → SylowModel := ![root 3, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 330 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 1 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 1 → Fin 1 := ![![0], ![0], ![0], ![0], ![0], ![0]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 0 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 330 := by
  rw [generated]
  exact outside_of_projected_orbit gen 0 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0]], [[2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 330).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node330
namespace Node331
private def roots : Fin 6 → SylowModel := ![root 3, root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 331 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 1 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 1 → Fin 1 := ![![0], ![0], ![0], ![0], ![0], ![0]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 0 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 331 := by
  rw [generated]
  exact outside_of_projected_orbit gen 0 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 331).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node331
namespace Node332
private def roots : Fin 6 → SylowModel := ![root 3, root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 332 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 1, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0)
private def rep : Fin 1 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 1 → Fin 1 := ![![0], ![0], ![0], ![0], ![0], ![0]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 2 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 332 := by
  rw [generated]
  exact outside_of_projected_orbit gen 2 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 1], [0]], [], [[0, 1], [0]], [], [[0, 1], [0]], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 332).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node332
namespace Node333
private def roots : Fin 6 → SylowModel := ![root 3, root 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 333 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 1 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 1 → Fin 1 := ![![0], ![0], ![0], ![0], ![0], ![0]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 0 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 333 := by
  rw [generated]
  exact outside_of_projected_orbit gen 0 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0]], [[2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 333).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node333
namespace Node334
private def roots : Fin 6 → SylowModel := ![root 2 * root 4 * root 7 * root 8 * root 9, root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 334 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩, 0)
private def rep : Fin 2 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 2 → Fin 2 := ![![1, 0], ![0, 1], ![0, 1], ![0, 1], ![0, 1], ![0, 1]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 5 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 334 := by
  rw [generated]
  exact outside_of_projected_orbit gen 5 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 2]], [], [[0, 2], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 334).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node334
namespace Node335
private def roots : Fin 6 → SylowModel := ![rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 0 * root 2 * root 4 * root 5 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7 * root 8, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 335 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 1, 0, 1, 0, 1, 1, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 0, 0, 1, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨1, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 1), (⟨1, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 1), (⟨1, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 1), (⟨1, 0, 0, 1, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 1), (⟨1, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 1), (⟨1, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 1), (⟨1, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![16, 17, 19, 18, 20, 21, 23, 22, 24, 25, 27, 26, 28, 29, 31, 30, 15, 14, 12, 13, 11, 10, 8, 9, 6, 7, 5, 4, 2, 3, 1, 0], ![26, 27, 24, 25, 30, 31, 28, 29, 18, 19, 16, 17, 22, 23, 20, 21, 9, 8, 11, 10, 13, 12, 15, 14, 1, 0, 3, 2, 5, 4, 7, 6], ![15, 14, 13, 12, 11, 10, 9, 8, 6, 7, 4, 5, 2, 3, 0, 1, 30, 31, 28, 29, 26, 27, 24, 25, 23, 22, 21, 20, 19, 18, 17, 16], ![13, 12, 15, 14, 9, 8, 11, 10, 4, 5, 6, 7, 0, 1, 2, 3, 28, 29, 30, 31, 24, 25, 26, 27, 21, 20, 23, 22, 17, 16, 19, 18], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 335 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[2]], [], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 335).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node335
namespace Node336
private def roots : Fin 6 → SylowModel := ![rootOne ^ 2 * root 3 * root 6 * root 7 * root 8 * root 9, root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7 * root 8, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 336 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 0)
private def rep : Fin 4 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 0, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 4 → Fin 4 := ![![1, 0, 3, 2], ![0, 1, 2, 3], ![3, 2, 1, 0], ![3, 2, 1, 0], ![0, 1, 2, 3], ![0, 1, 2, 3]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 4 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 336 := by
  rw [generated]
  exact outside_of_projected_orbit gen 4 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0]], [], [[2]], [[2], [0]], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 336).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node336
namespace Node337
private def roots : Fin 6 → SylowModel := ![root 0 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 8 * root 9, root 9, root 7 * root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 337 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 1, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 0⟩, 1), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 1, 0, 1, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 1, 1, 1, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨1, 0, 0, 1, 0, 0, 0, 1, 0, 0⟩, 1), (⟨1, 0, 0, 1, 0, 1, 1, 0, 1, 0⟩, 1), (⟨1, 0, 0, 1, 0, 1, 1, 1, 1, 0⟩, 1), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨1, 0, 1, 0, 1, 0, 0, 1, 0, 0⟩, 1), (⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 0⟩, 1), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 1), (⟨1, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![27, 26, 24, 25, 31, 30, 28, 29, 19, 18, 16, 17, 23, 22, 20, 21, 7, 6, 4, 5, 3, 2, 0, 1, 14, 15, 13, 12, 10, 11, 9, 8], ![15, 14, 13, 12, 11, 10, 9, 8, 6, 7, 4, 5, 2, 3, 0, 1, 30, 31, 28, 29, 26, 27, 24, 25, 23, 22, 21, 20, 19, 18, 17, 16], ![12, 13, 14, 15, 8, 9, 10, 11, 5, 4, 7, 6, 1, 0, 3, 2, 29, 28, 31, 30, 25, 24, 27, 26, 20, 21, 22, 23, 16, 17, 18, 19], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 337 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[2], [0]], [[0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 337).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node337
namespace Node338
private def roots : Fin 6 → SylowModel := ![root 0 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 0 * root 3, root 8 * root 9, root 2 * root 3 * root 4 * root 8 * root 9, root 9, root 7 * root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 338 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨1, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![4, 5, 6, 7, 0, 1, 2, 3], ![6, 7, 4, 5, 1, 0, 3, 2], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 2, 1, 0, 7, 6, 5, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 338 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[3], [0]], [[3]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 338).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node338
namespace Node339
private def roots : Fin 6 → SylowModel := ![root 0 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 8 * root 9, root 9, root 7 * root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 339 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 1, 1, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 1, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨1, 0, 0, 1, 0, 0, 0, 1, 1, 0⟩, 1), (⟨1, 0, 0, 1, 0, 1, 1, 0, 1, 0⟩, 1), (⟨1, 0, 0, 1, 0, 1, 1, 1, 1, 0⟩, 1), (⟨1, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, 1), (⟨1, 0, 1, 0, 1, 0, 0, 1, 1, 0⟩, 1), (⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 0⟩, 1), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 1), (⟨1, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![27, 26, 24, 25, 31, 30, 28, 29, 19, 18, 16, 17, 23, 22, 20, 21, 7, 6, 4, 5, 3, 2, 0, 1, 14, 15, 13, 12, 10, 11, 9, 8], ![15, 14, 13, 12, 11, 10, 9, 8, 6, 7, 4, 5, 2, 3, 0, 1, 30, 31, 28, 29, 26, 27, 24, 25, 23, 22, 21, 20, 19, 18, 17, 16], ![12, 13, 14, 15, 8, 9, 10, 11, 5, 4, 7, 6, 1, 0, 3, 2, 29, 28, 31, 30, 25, 24, 27, 26, 20, 21, 22, 23, 16, 17, 18, 19], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 339 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[2], [0]], [[2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 339).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node339
namespace Node340
private def roots : Fin 6 → SylowModel := ![root 0 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 0 * root 2 * root 4 * root 5 * root 6 * root 8 * root 9, root 8 * root 9, root 2 * root 3 * root 4 * root 8 * root 9, root 9, root 7 * root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 340 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨1, 0, 0, 1, 0, 1, 1, 0, 1, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨1, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨1, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![4, 5, 6, 7, 0, 1, 2, 3], ![5, 4, 7, 6, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![3, 2, 1, 0, 7, 6, 5, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 340 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1, 2], [1, 2], [1, 2]], [[3]], [[0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 340).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node340
namespace Node341
private def roots : Fin 6 → SylowModel := ![root 0 * root 6 * root 7, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 8, root 2 * root 3 * root 4 * root 8 * root 9, root 9, root 7 * root 9]
private def gen : Fin 6 → E := ![(⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 341 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)
private def rep : Fin 32 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 1, 1, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 1, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 0⟩, 1), (⟨0, 0, 0, 1, 0, 1, 0, 0, 1, 0⟩, 1), (⟨0, 0, 0, 1, 0, 1, 0, 1, 1, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 1, 0, 1, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 1, 1, 1, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 0, 0, 1, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 0, 1, 1, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 1, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 0, 1, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 1, 1, 1, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 0, 1, 1, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 0), (⟨1, 0, 0, 0, 0, 1, 0, 1, 0, 0⟩, 0), (⟨1, 0, 0, 1, 0, 0, 0, 0, 1, 0⟩, 1), (⟨1, 0, 0, 1, 0, 0, 0, 1, 1, 0⟩, 1), (⟨1, 0, 0, 1, 0, 1, 1, 0, 1, 0⟩, 1), (⟨1, 0, 0, 1, 0, 1, 1, 1, 1, 0⟩, 1), (⟨1, 0, 1, 0, 1, 0, 0, 0, 1, 0⟩, 1), (⟨1, 0, 1, 0, 1, 0, 0, 1, 1, 0⟩, 1), (⟨1, 0, 1, 0, 1, 1, 1, 0, 1, 0⟩, 1), (⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩, 1), (⟨1, 0, 1, 1, 1, 0, 1, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 0, 1, 1, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 0, 1, 0⟩, 0), (⟨1, 0, 1, 1, 1, 1, 0, 1, 1, 0⟩, 0)]
private def next : Fin 6 → Fin 32 → Fin 32 := ![![17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30, 1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14], ![27, 26, 24, 25, 31, 30, 28, 29, 19, 18, 16, 17, 23, 22, 20, 21, 7, 6, 4, 5, 3, 2, 0, 1, 14, 15, 13, 12, 10, 11, 9, 8], ![15, 14, 13, 12, 11, 10, 9, 8, 6, 7, 4, 5, 2, 3, 0, 1, 30, 31, 28, 29, 26, 27, 24, 25, 23, 22, 21, 20, 19, 18, 17, 16], ![12, 13, 14, 15, 8, 9, 10, 11, 5, 4, 7, 6, 1, 0, 3, 2, 29, 28, 31, 30, 25, 24, 27, 26, 20, 21, 22, 23, 16, 17, 18, 19], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31], ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22, 25, 24, 27, 26, 29, 28, 31, 30]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 9 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 341 := by
  rw [generated]
  exact outside_of_projected_orbit gen 9 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[1, 2], [1]], [[2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 341).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node341
namespace Node342
private def roots : Fin 6 → SylowModel := ![root 3, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 342 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![1, 0, 3, 2, 5, 4, 7, 6], ![7, 6, 5, 4, 3, 2, 1, 0], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 342 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0]], [[2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 342).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node342
namespace Node343
private def roots : Fin 6 → SylowModel := ![root 3, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 343 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![1, 0, 3, 2, 5, 4, 7, 6], ![6, 7, 4, 5, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 343 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 343).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node343
namespace Node344
private def roots : Fin 6 → SylowModel := ![root 3, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 344 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![3, 2, 1, 0, 7, 6, 5, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 344 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0]], [[1, 2], [0]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 344).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node344
namespace Node345
private def roots : Fin 6 → SylowModel := ![root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 345 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![6, 7, 4, 5, 2, 3, 0, 1], ![7, 6, 5, 4, 3, 2, 1, 0], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 345 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[0]], [[2]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 345).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node345
namespace Node346
private def roots : Fin 6 → SylowModel := ![root 3, rootOne ^ 2 * root 2 * root 3 * root 4 * root 5 * root 8 * root 9, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 1, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 346 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![7, 6, 5, 4, 3, 2, 1, 0], ![6, 7, 4, 5, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 346 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[1, 2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 346).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node346
namespace Node347
private def roots : Fin 6 → SylowModel := ![root 2 * root 4 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8 * root 9, root 5 * root 6 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 1, 0, 1, 0, 0, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 1, 0, 1⟩, 1), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 347 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 0, 0, 1, 1, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 1, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 1, 0, 0, 0⟩, 0)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![4, 5, 6, 7, 0, 1, 2, 3], ![1, 0, 3, 2, 5, 4, 7, 6], ![3, 2, 1, 0, 7, 6, 5, 4], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 7 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 347 := by
  rw [generated]
  exact outside_of_projected_orbit gen 7 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[], [[1]], [[1, 2], [1]], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 347).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node347
namespace Node348
private def roots : Fin 6 → SylowModel := ![root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 348 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 1, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 1, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![1, 0, 3, 2, 5, 4, 7, 6], ![6, 7, 4, 5, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 348 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[2]], [], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 348).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node348
namespace Node349
private def roots : Fin 6 → SylowModel := ![root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2, root 2 * root 3 * root 4 * root 9, root 8 * root 9, root 7 * root 9, root 9]
private def gen : Fin 6 → E := ![(⟨0, 0, 0, 1, 0, 0, 1, 1, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 1⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, 0)]
set_option maxHeartbeats 4000000 in
private theorem gen_eq : encode ∘ gen = roots := by
  funext i
  exact (by decide +kernel : ∀ i, encode (gen i) = roots i) i
private theorem generated : smallEvenDescentNode 349 = Subgroup.closure (Set.range (encode ∘ gen)) := by
  rw [gen_eq]
  simp only [roots, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl
private def g : E := (⟨0, 0, 1, 1, 1, 1, 1, 0, 0, 0⟩, 0)
private def rep : Fin 8 → E := ![(⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 0, 1, 0, 0, 0, 0, 0⟩, 1), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 0), (⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 0⟩, 1)]
private def next : Fin 6 → Fin 8 → Fin 8 := ![![2, 3, 0, 1, 6, 7, 4, 5], ![1, 0, 3, 2, 5, 4, 7, 6], ![6, 7, 4, 5, 2, 3, 0, 1], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]
set_option maxHeartbeats 4000000 in
private theorem steps : ∀ i j, trunc 6 (mul (gen i) (rep j)) = rep (next i j) := by decide +kernel
private theorem outside : encode g ∉ smallEvenDescentNode 349 := by
  rw [generated]
  exact outside_of_projected_orbit gen 6 rep 0 rfl next steps g (by decide +kernel)
private def squares : Fin 6 → List (List (Fin 6)) := ![[[0, 1], [2]], [[2]], [], [], [], []]
set_option maxHeartbeats 4000000 in
private theorem checked : ∀ i, mul (mul (gen i) (squareWord gen (squares i))) g = mul g (gen i) := by decide +kernel
private theorem witness : (smallEvenDescentNode 349).HasFrattiniNormalizerWitness :=
  Subgroup.hasFrattiniNormalizerWitness_of_squareWords _
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) (encode ∘ gen) generated (encode g) outside squares
    (checked_displacements gen g squares checked)
end Node349

/-- Checked witnesses at indices 300 through 349, excluding the prescribed survivors. -/
@[expose] public def block6 :
    List {i : Fin 600 // (smallEvenDescentNode i).HasFrattiniNormalizerWitness} :=
  [⟨300, by exact Node300.witness⟩,
  ⟨301, by exact Node301.witness⟩,
  ⟨302, by exact Node302.witness⟩,
  ⟨303, by exact Node303.witness⟩,
  ⟨304, by exact Node304.witness⟩,
  ⟨305, by exact Node305.witness⟩,
  ⟨306, by exact Node306.witness⟩,
  ⟨307, by exact Node307.witness⟩,
  ⟨308, by exact Node308.witness⟩,
  ⟨309, by exact Node309.witness⟩,
  ⟨310, by exact Node310.witness⟩,
  ⟨311, by exact Node311.witness⟩,
  ⟨312, by exact Node312.witness⟩,
  ⟨313, by exact Node313.witness⟩,
  ⟨314, by exact Node314.witness⟩,
  ⟨315, by exact Node315.witness⟩,
  ⟨316, by exact Node316.witness⟩,
  ⟨317, by exact Node317.witness⟩,
  ⟨318, by exact Node318.witness⟩,
  ⟨320, by exact Node320.witness⟩,
  ⟨321, by exact Node321.witness⟩,
  ⟨322, by exact Node322.witness⟩,
  ⟨323, by exact Node323.witness⟩,
  ⟨324, by exact Node324.witness⟩,
  ⟨325, by exact Node325.witness⟩,
  ⟨326, by exact Node326.witness⟩,
  ⟨327, by exact Node327.witness⟩,
  ⟨328, by exact Node328.witness⟩,
  ⟨329, by exact Node329.witness⟩,
  ⟨330, by exact Node330.witness⟩,
  ⟨331, by exact Node331.witness⟩,
  ⟨332, by exact Node332.witness⟩,
  ⟨333, by exact Node333.witness⟩,
  ⟨334, by exact Node334.witness⟩,
  ⟨335, by exact Node335.witness⟩,
  ⟨336, by exact Node336.witness⟩,
  ⟨337, by exact Node337.witness⟩,
  ⟨338, by exact Node338.witness⟩,
  ⟨339, by exact Node339.witness⟩,
  ⟨340, by exact Node340.witness⟩,
  ⟨341, by exact Node341.witness⟩,
  ⟨342, by exact Node342.witness⟩,
  ⟨343, by exact Node343.witness⟩,
  ⟨344, by exact Node344.witness⟩,
  ⟨345, by exact Node345.witness⟩,
  ⟨346, by exact Node346.witness⟩,
  ⟨347, by exact Node347.witness⟩,
  ⟨348, by exact Node348.witness⟩,
  ⟨349, by exact Node349.witness⟩]

end ReeTwo.SylowModel.UpperCertificate
