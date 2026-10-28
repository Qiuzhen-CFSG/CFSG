module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.PresentationData
public import Theory.GroupTheory.BinaryCollection
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The finite candidate presentation for the local two-group

The power-conjugate relations define a universal group. Their triangular
supports give a binary normal form with at most 21 bits, hence a finite group
of order at most 2²¹. Neither equality of the order nor a matrix comparison is
assumed or asserted here. A surjective realization in the actual matrix
two-group will turn this upper bound into an isomorphism.

Source: the elementary binary collection theorem in
`Theory.GroupTheory.BinaryCollection`; the proposed relations and their matrix
provenance are documented in `PresentationData` and `source/README.md`.
-/

@[expose] public section
namespace Janko4.LocalStructure.SylowNormalEights.Presentation

/-- All squares, and precisely the inverse conjugates with increasing indices. -/
abbrev RelationIndex := Fin 21 ⊕ {ij : Fin 21 × Fin 21 // ij.1 < ij.2}

/-- Relators impose equality by multiplying the proposed right side's inverse. -/
def relator : RelationIndex → FreeGroup (Fin 21)
  | .inl i => FreeGroup.of i * FreeGroup.of i *
      ((squareWord i).map FreeGroup.of).prod⁻¹
  | .inr ij => (FreeGroup.of ij.val.1)⁻¹ * FreeGroup.of ij.val.2 *
      FreeGroup.of ij.val.1 * ((conjugateWord ij.val.1 ij.val.2).map FreeGroup.of).prod⁻¹

/-- The candidate group, with no identification by order. -/
abbrev Carrier := PresentedGroup (Set.range relator)

/-- Canonical generators of the universal presentation. -/
def generator (i : Fin 21) : Carrier := PresentedGroup.of i

/-- The concrete equations required of a realization of the presentation. -/
structure Relations {G : Type*} [Group G] (g : Fin 21 → G) : Prop where
  square : ∀ i, g i * g i = ((squareWord i).map g).prod
  conjugate : ∀ i j, i < j → (g i)⁻¹ * g j * g i = ((conjugateWord i j).map g).prod

theorem generator_relations : Relations generator := by
  constructor
  · intro i
    unfold generator
    have h := PresentedGroup.one_of_mem (Set.mem_range_self (f := relator) (.inl i : RelationIndex))
    simpa only [relator, map_mul, map_inv, map_list_prod, List.map_map,
      Function.comp_def, PresentedGroup.of, generator, mul_inv_eq_one] using h
  · intro i j hij
    unfold generator
    have h := PresentedGroup.one_of_mem
      (Set.mem_range_self (f := relator) (.inr ⟨(i, j), hij⟩ : RelationIndex))
    simpa only [relator, map_mul, map_inv, map_list_prod, List.map_map,
      Function.comp_def, PresentedGroup.of, generator, mul_inv_eq_one] using h

/-- A realization is built only after all its literal group equations are proved. -/
def lift {G : Type*} [Group G] (g : Fin 21 → G) (h : Relations g) : Carrier →* G :=
  PresentedGroup.toGroup (f := g) (by
    rintro _ ⟨i | ⟨⟨i, j⟩, hij⟩, rfl⟩
    · simpa only [relator, map_mul, map_inv, map_list_prod, List.map_map,
        Function.comp_def, FreeGroup.lift_apply_of, mul_inv_eq_one] using h.square i
    · simpa only [relator, map_mul, map_inv, map_list_prod, List.map_map,
        Function.comp_def, FreeGroup.lift_apply_of, mul_inv_eq_one] using h.conjugate i j hij)

@[simp] theorem lift_generator {G : Type*} [Group G]
    (g : Fin 21 → G) (h : Relations g) (i : Fin 21) : lift g h (generator i) = g i :=
  PresentedGroup.toGroup.of _

/-- The literal images generate exactly the range of the realization. -/
theorem range_lift {G : Type*} [Group G] (g : Fin 21 → G) (h : Relations g) :
    (lift g h).range = Subgroup.closure (Set.range g) := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of (Set.range relator),
    MonoidHom.map_closure, ← Set.range_comp]
  have he : (lift g h) ∘ (PresentedGroup.of : Fin 21 → Carrier) = g :=
    funext (lift_generator g h)
  rw [he]


/-- The triangular relations suffice for collection; consistency is not needed. -/
theorem generator_triangular :
    Theory.GroupTheory.BinaryCollection.triangular (List.ofFn generator) := by
  change Theory.GroupTheory.BinaryCollection.triangular
    ((List.finRange 21).map generator)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 0
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] (squareWord 0) (conjugateWord 0)
    (generator_relations.square 0) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro b hb
    exact generator_relations.conjugate 0 b
      ((by decide +kernel : ∀ b : Fin 21, b ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] → (0 : Fin 21) < b) b hb)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 1
    [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] (squareWord 1) (conjugateWord 1)
    (generator_relations.square 1) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro b hb
    exact generator_relations.conjugate 1 b
      ((by decide +kernel : ∀ b : Fin 21, b ∈ [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] → (1 : Fin 21) < b) b hb)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 2
    [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] (squareWord 2) (conjugateWord 2)
    (generator_relations.square 2) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro b hb
    exact generator_relations.conjugate 2 b
      ((by decide +kernel : ∀ b : Fin 21, b ∈ [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] → (2 : Fin 21) < b) b hb)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 3
    [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] (squareWord 3) (conjugateWord 3)
    (generator_relations.square 3) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro b hb
    exact generator_relations.conjugate 3 b
      ((by decide +kernel : ∀ b : Fin 21, b ∈ [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] → (3 : Fin 21) < b) b hb)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 4
    [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] (squareWord 4) (conjugateWord 4)
    (generator_relations.square 4) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro b hb
    exact generator_relations.conjugate 4 b
      ((by decide +kernel : ∀ b : Fin 21, b ∈ [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] → (4 : Fin 21) < b) b hb)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 5
    [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] (squareWord 5) (conjugateWord 5)
    (generator_relations.square 5) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro b hb
    exact generator_relations.conjugate 5 b
      ((by decide +kernel : ∀ b : Fin 21, b ∈ [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] → (5 : Fin 21) < b) b hb)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 6
    [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] (squareWord 6) (conjugateWord 6)
    (generator_relations.square 6) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro b hb
    exact generator_relations.conjugate 6 b
      ((by decide +kernel : ∀ b : Fin 21, b ∈ [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] → (6 : Fin 21) < b) b hb)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 7
    [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] (squareWord 7) (conjugateWord 7)
    (generator_relations.square 7) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro b hb
    exact generator_relations.conjugate 7 b
      ((by decide +kernel : ∀ b : Fin 21, b ∈ [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] → (7 : Fin 21) < b) b hb)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 8
    [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] (squareWord 8) (conjugateWord 8)
    (generator_relations.square 8) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro b hb
    exact generator_relations.conjugate 8 b
      ((by decide +kernel : ∀ b : Fin 21, b ∈ [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] → (8 : Fin 21) < b) b hb)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 9
    [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] (squareWord 9) (conjugateWord 9)
    (generator_relations.square 9) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro b hb
    exact generator_relations.conjugate 9 b
      ((by decide +kernel : ∀ b : Fin 21, b ∈ [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] → (9 : Fin 21) < b) b hb)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 10
    [11, 12, 13, 14, 15, 16, 17, 18, 19, 20] (squareWord 10) (conjugateWord 10)
    (generator_relations.square 10) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro b hb
    exact generator_relations.conjugate 10 b
      ((by decide +kernel : ∀ b : Fin 21, b ∈ [11, 12, 13, 14, 15, 16, 17, 18, 19, 20] → (10 : Fin 21) < b) b hb)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 11
    [12, 13, 14, 15, 16, 17, 18, 19, 20] (squareWord 11) (conjugateWord 11)
    (generator_relations.square 11) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro b hb
    exact generator_relations.conjugate 11 b
      ((by decide +kernel : ∀ b : Fin 21, b ∈ [12, 13, 14, 15, 16, 17, 18, 19, 20] → (11 : Fin 21) < b) b hb)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 12
    [13, 14, 15, 16, 17, 18, 19, 20] (squareWord 12) (conjugateWord 12)
    (generator_relations.square 12) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro b hb
    exact generator_relations.conjugate 12 b
      ((by decide +kernel : ∀ b : Fin 21, b ∈ [13, 14, 15, 16, 17, 18, 19, 20] → (12 : Fin 21) < b) b hb)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 13
    [14, 15, 16, 17, 18, 19, 20] (squareWord 13) (conjugateWord 13)
    (generator_relations.square 13) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro b hb
    exact generator_relations.conjugate 13 b
      ((by decide +kernel : ∀ b : Fin 21, b ∈ [14, 15, 16, 17, 18, 19, 20] → (13 : Fin 21) < b) b hb)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 14
    [15, 16, 17, 18, 19, 20] (squareWord 14) (conjugateWord 14)
    (generator_relations.square 14) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro b hb
    exact generator_relations.conjugate 14 b
      ((by decide +kernel : ∀ b : Fin 21, b ∈ [15, 16, 17, 18, 19, 20] → (14 : Fin 21) < b) b hb)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 15
    [16, 17, 18, 19, 20] (squareWord 15) (conjugateWord 15)
    (generator_relations.square 15) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro b hb
    exact generator_relations.conjugate 15 b
      ((by decide +kernel : ∀ b : Fin 21, b ∈ [16, 17, 18, 19, 20] → (15 : Fin 21) < b) b hb)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 16
    [17, 18, 19, 20] (squareWord 16) (conjugateWord 16)
    (generator_relations.square 16) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro b hb
    exact generator_relations.conjugate 16 b
      ((by decide +kernel : ∀ b : Fin 21, b ∈ [17, 18, 19, 20] → (16 : Fin 21) < b) b hb)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 17
    [18, 19, 20] (squareWord 17) (conjugateWord 17)
    (generator_relations.square 17) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro b hb
    exact generator_relations.conjugate 17 b
      ((by decide +kernel : ∀ b : Fin 21, b ∈ [18, 19, 20] → (17 : Fin 21) < b) b hb)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 18
    [19, 20] (squareWord 18) (conjugateWord 18)
    (generator_relations.square 18) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro b hb
    exact generator_relations.conjugate 18 b
      ((by decide +kernel : ∀ b : Fin 21, b ∈ [19, 20] → (18 : Fin 21) < b) b hb)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 19
    [20] (squareWord 19) (conjugateWord 19)
    (generator_relations.square 19) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro b hb
    exact generator_relations.conjugate 19 b
      ((by decide +kernel : ∀ b : Fin 21, b ∈ [20] → (19 : Fin 21) < b) b hb)
  refine Theory.GroupTheory.BinaryCollection.triangular_cons_of_words generator 20
    [] (squareWord 20) (conjugateWord 20)
    (generator_relations.square 20) ?_ (by decide +kernel) (by decide +kernel) ?_
  · intro b hb
    exact generator_relations.conjugate 20 b
      ((by decide +kernel : ∀ b : Fin 21, b ∈ [] → (20 : Fin 21) < b) b hb)
  trivial

/-- Ascending normal forms; bit zero selects the first generator. -/
def normalForm (n : Fin (2 ^ 21)) : Carrier :=
  Theory.GroupTheory.BinaryCollection.product (List.ofFn generator) n.val

/-- Every element of the presentation has an ascending binary normal form. -/
theorem normalForm_surjective : Function.Surjective normalForm := by
  intro x
  have hx : x ∈ Subgroup.closure (Set.range generator) := by
    rw [show Subgroup.closure (Set.range generator) = ⊤ from
      PresentedGroup.closure_range_of _]
    trivial
  obtain ⟨n, hn⟩ := Theory.GroupTheory.BinaryCollection.cover_ofFn
    generator generator_triangular x hx
  exact ⟨n, (Theory.GroupTheory.BinaryCollection.product_ofFn generator n.val).trans hn⟩

instance : Finite Carrier := Finite.of_surjective normalForm normalForm_surjective

/-- An upper bound proved by collection, independently of any matrix calculation. -/
theorem card_le : Nat.card Carrier ≤ 2 ^ 21 := by
  simpa only [Nat.card_fin] using
    Nat.card_le_card_of_surjective normalForm normalForm_surjective

end Janko4.LocalStructure.SylowNormalEights.Presentation
