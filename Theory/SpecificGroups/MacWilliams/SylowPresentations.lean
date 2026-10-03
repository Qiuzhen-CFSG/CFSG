module

public import Mathlib.GroupTheory.PresentedGroup

/-!
# Presentations for the two MacWilliams Sylow alternatives

This module fixes power-commutator presentations for the order-128 Hall–Janko
Sylow candidate and the order-64 unitary Sylow candidate. The commutator
convention is `x⁻¹ * y⁻¹ * x * y`, and indices start at zero. It proves the
relations and universal property, without assuming a finite order or a
recognition theorem for either presentation.

The alternatives are those of MacWilliams, Trans. AMS 150 (1970), cited in
Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3, p.386. These choices of
coordinates were obtained from the power-commutator presentations of GAP's
SmallGroup(128,934) and SmallGroup(64,245). GAP was used only to discover the
relations. Identification with the Sylow alternatives, finiteness, and model
calculations are separate proof obligations; no GAP output is a proof here.
-/

@[expose] public section

namespace MacWilliamsSylow

/-- A positive word in specified generators, with the displayed order of factors. -/
def word {n : ℕ} {G : Type*} [Group G] (x : Fin n → G) (w : List (Fin n)) : G :=
  (w.map x).prod

/-- The commutator convention used by the power-commutator tables. -/
def rightComm {G : Type*} [Group G] (x y : G) : G := x⁻¹ * y⁻¹ * x * y

@[simp] theorem map_word {n : ℕ} {G H : Type*} [Group G] [Group H]
    (f : G →* H) (x : Fin n → G) (w : List (Fin n)) :
    f (word x w) = word (fun i => f (x i)) w := by
  simp [word, map_list_prod, List.map_map, Function.comp_def]

@[simp] theorem map_rightComm {G H : Type*} [Group G] [Group H]
    (f : G →* H) (x y : G) : f (rightComm x y) = rightComm (f x) (f y) := by
  simp only [rightComm, map_mul, map_inv]

/-- Squares and commutators determine a power-commutator presentation. -/
structure Table (n : ℕ) where
  square : Fin n → List (Fin n)
  commutator : Fin n → Fin n → List (Fin n)

/-- The relations asserted of a tuple of generators. -/
structure Relations {n : ℕ} {G : Type*} [Group G] (t : Table n) (x : Fin n → G) : Prop where
  square : ∀ i, x i * x i = word x (t.square i)
  commutator : ∀ i j, i < j → rightComm (x j) (x i) = word x (t.commutator j i)

/-- Relators corresponding to the table. -/
def relators {n : ℕ} (t : Table n) : Set (FreeGroup (Fin n)) :=
  {r | (∃ i, r = FreeGroup.of i * FreeGroup.of i * (word FreeGroup.of (t.square i))⁻¹) ∨
    ∃ i j, i < j ∧ r = rightComm (FreeGroup.of j) (FreeGroup.of i) *
      (word FreeGroup.of (t.commutator j i))⁻¹}

abbrev Model {n : ℕ} (t : Table n) := PresentedGroup (relators t)

def generator {n : ℕ} (t : Table n) (i : Fin n) : Model t := PresentedGroup.of i

/-- The canonical generators satisfy every specified relation. -/
theorem generator_relations {n : ℕ} (t : Table n) : Relations t (generator t) where
  square i := by
    have he := PresentedGroup.mk_eq_mk_of_mul_inv_mem
      (rels := relators t) (Or.inl ⟨i, rfl⟩)
    unfold generator PresentedGroup.of
    simpa only [map_mul, map_word] using he
  commutator i j hij := by
    have he := PresentedGroup.mk_eq_mk_of_mul_inv_mem
      (rels := relators t) (Or.inr ⟨i, j, hij, rfl⟩)
    unfold generator PresentedGroup.of
    simpa only [map_rightComm, map_word] using he

/-- The canonical generators generate the whole presented group. -/
theorem generator_closure {n : ℕ} (t : Table n) :
    Subgroup.closure (Set.range (generator t)) = ⊤ :=
  PresentedGroup.closure_range_of (relators t)

/-- Interpret the presentation in any group satisfying its relations. -/
def presentationHom {n : ℕ} {G : Type*} [Group G] {t : Table n} {x : Fin n → G}
    (h : Relations t x) : Model t →* G :=
  PresentedGroup.toGroup (f := x) (by
    intro r hr
    rcases hr with ⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩
    · simp only [map_mul, map_inv, map_word, FreeGroup.lift_apply_of,
        h.square, mul_inv_cancel]
    · simp only [map_mul, map_inv, map_rightComm, map_word, FreeGroup.lift_apply_of,
        h.commutator i j hij, mul_inv_cancel])

@[simp] theorem presentationHom_generator {n : ℕ} {G : Type*} [Group G]
    {t : Table n} {x : Fin n → G} (h : Relations t x) (i : Fin n) :
    presentationHom h (generator t i) = x i := PresentedGroup.toGroup.of _

/-- The seven-generator Hall–Janko Sylow candidate. -/
def hallJankoTable : Table 7 where
  square i := if i = 3 ∨ i = 4 then [6] else []
  commutator j i :=
    match j.val, i.val with
    | 1, 0 => [3]
    | 2, 0 => [4]
    | 3, 0 => [6]
    | 4, 0 => [6]
    | 5, 0 => [6]
    | 3, 1 => [6]
    | 4, 1 => [5, 6]
    | 3, 2 => [5]
    | 4, 2 => [6]
    | 4, 3 => [6]
    | _, _ => []

/-- The six-generator unitary Sylow candidate. -/
def unitaryTable : Table 6 where
  square i :=
    match i.val with
    | 0 => [4]
    | 1 => [5]
    | 2 => [5]
    | 3 => [4]
    | _ => []
  commutator j i :=
    match j.val, i.val with
    | 1, 0 => [4]
    | 2, 0 => [5]
    | 3, 0 => [4, 5]
    | 2, 1 => [4, 5]
    | 3, 1 => [4]
    | _, _ => []

abbrev HallJankoSylow := Model hallJankoTable
abbrev UnitarySylow := Model unitaryTable

end MacWilliamsSylow
