module

public import Theory.AlgebraicGroup.RootSystems.TypeD4DiagramTriality

/-!
# Small Weyl-orbit bounds for binary D4 weights

Weights are their four integral simple-coroot coordinates, with the central
vertex numbered `1`, exactly as in `TypeD4DiagramTriality`. A simple reflection
subtracts the corresponding coordinate times a row of the actual D4 Cartan
matrix. Twenty-five explicit reflection words supply at least eight distinct
weights for every nonzero binary weight, and at least twenty-four for every
nonzero weight fixed by the pinned diagram cycle.

Only a subset of each Weyl orbit is enumerated. The subset theorem transports
these bounds to any reflection-invariant weight support. In particular, this
calculation does not assert existence, irreducibility or exhaustivity of
algebraic-group modules.

Sources: GLS3, §§1.14 and 2.8 (`refs/KGroup/GLS3/chapter2.tex`), and the triality
degree argument of Aschbacher--Smith, printed p.356 (PDF p.367).
-/

@[expose] public section

namespace Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight

/-- Integral simple-coroot coordinates. -/
abbrev Weight := Fin 4 → ℤ

/-- All sixteen binary restricted weights. -/
abbrev BasicWeight := Fin 4 → Bool

/-- Embed a binary weight in the integral weight-coordinate lattice. -/
def coefficient (a : BasicWeight) : Weight := fun i => if a i then 1 else 0

/-- The binary parametrization does not identify distinct weights. -/
theorem coefficient_injective : Function.Injective coefficient := by
  intro a b h
  funext i
  have hi := congrFun h i
  cases ha : a i <;> cases hb : b i <;> simp [coefficient, ha, hb] at hi ⊢

/-- The sixteen parameters are exactly the characteristic-two basic range
of GLS3 Definition 2.8.1(a), in simple-coroot coordinates. -/
theorem mem_range_coefficient_iff (x : Weight) :
    x ∈ Set.range coefficient ↔ ∀ i, 0 ≤ x i ∧ x i < 2 := by
  constructor
  · rintro ⟨a, rfl⟩ i
    cases h : a i <;> simp [coefficient, h]
  · intro h
    refine ⟨fun i => if x i = 0 then false else true, ?_⟩
    funext i
    by_cases hi : x i = 0
    · simp [coefficient, hi]
    · have hx := h i
      have hone : x i = 1 := by omega
      simp [coefficient, hone]

/-- The simple reflection in the actual numbered D4 Cartan matrix. -/
def reflection (i : Fin 4) (a : Weight) : Weight :=
  fun j => a j - a i * typeDCartanMatrix 2 i j

/-- Reflection words witnessing the two lower bounds. -/
def words : List (List (Fin 4)) :=
  [[],
    [1],
    [1, 0],
    [1, 2],
    [1, 3],
    [1, 0, 2],
    [1, 0, 3],
    [1, 2, 3],
    [1, 0, 2, 1],
    [1, 0, 2, 3],
    [1, 0, 3, 1],
    [1, 2, 3, 1],
    [1, 0, 2, 1, 3],
    [1, 0, 2, 3, 1],
    [1, 0, 3, 1, 2],
    [1, 2, 3, 1, 0],
    [1, 0, 2, 1, 3, 1],
    [1, 0, 2, 3, 1, 0],
    [1, 0, 2, 3, 1, 2],
    [1, 0, 2, 1, 3, 1, 0],
    [1, 0, 2, 1, 3, 1, 2],
    [1, 0, 2, 3, 1, 0, 2],
    [1, 0, 2, 1, 3, 1, 0, 2],
    [1, 0, 2, 1, 3, 1, 0, 2, 1],
    [0, 1, 2, 1, 0, 3, 1, 0, 2, 1, 3]]

/-- Apply a sequence of simple reflections, in list order. -/
def wordAction (a : Weight) (w : List (Fin 4)) : Weight :=
  w.foldl (fun a i => reflection i a) a

/-- A finite subset of the Weyl orbit sufficient for the degree bounds. -/
def witnesses (a : BasicWeight) : Finset Weight :=
  (words.map (wordAction (coefficient a))).toFinset

/-- The zero restricted weight. -/
def zeroWeight : BasicWeight := fun _ => false

/-- Pullback by the same diagram cycle as the standard graph-field carrier. -/
def diagramAction (a : BasicWeight) : BasicWeight := a ∘ typeD4DiagramPermutation

/-- The diagram-fixed binary weights have equal coefficients on the three arms. -/
theorem diagramAction_eq_iff : ∀ a : BasicWeight,
    diagramAction a = a ↔ a 0 = a 2 ∧ a 2 = a 3 := by decide +kernel

/-- There are sixteen basic weights, without a restriction on the field exponent. -/
theorem card_basicWeight : Fintype.card BasicWeight = 16 := by decide

set_option maxRecDepth 10000 in
/-- Every nonzero binary weight has at least eight distinct Weyl conjugates. -/
theorem eight_le_card_witnesses : ∀ a : BasicWeight,
    a ≠ zeroWeight → 8 ≤ (witnesses a).card := by decide +kernel

set_option maxRecDepth 10000 in
/-- Every nonzero diagram-fixed binary weight has at least twenty-four
distinct Weyl conjugates, including the central fundamental weight. -/
theorem twenty_four_le_card_witnesses : ∀ a : BasicWeight,
    a ≠ zeroWeight → diagramAction a = a → 24 ≤ (witnesses a).card := by
  decide +kernel

/-- Reflection-invariant support contains every reflection word in a weight. -/
theorem wordAction_mem {S : Set Weight}
    (hS : ∀ i a, a ∈ S → reflection i a ∈ S)
    {a : Weight} (ha : a ∈ S) (w : List (Fin 4)) : wordAction a w ∈ S := by
  induction w generalizing a with
  | nil => exact ha
  | cons i w ih => exact ih (hS i a ha)

/-- All the enumerated witnesses occur in any reflection-invariant support
containing the initial weight. -/
theorem witnesses_subset {S : Set Weight}
    (hS : ∀ i a, a ∈ S → reflection i a ∈ S)
    {a : BasicWeight} (ha : coefficient a ∈ S) : (witnesses a : Set Weight) ⊆ S := by
  intro b hb
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
  exact wordAction_mem hS ha w

end Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
