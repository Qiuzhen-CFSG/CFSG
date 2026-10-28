module

public import Theory.SpecificGroups.SymmetricFourConjugacy
public import Mathlib.Data.Fin.VecNotation

/-!
# The five conjugacy classes of the symmetric group on four letters

The classes are ordered as identity, transposition, double transposition,
three-cycle, and four-cycle. A finite kernel check classifies permutations by
order and fixed points and proves the class sizes `1, 6, 3, 8, 6`.
The resulting equivalence and carrier-cardinality formula support ordinary
character calculations without assuming a character table.

Source: the elementary cycle-type classification in S₄; used for Fong,
*Some Sylow subgroups of order 32*, J. Algebra 6 (1967), p. 71.
-/

public section

open scoped BigOperators
namespace SymmetricFourClasses
abbrev G := Equiv.Perm (Fin 4)

/-- The cycle-type index in the class order described above. -/
@[expose] def classIndex (g : G) : Fin 5 :=
  if g = 1 then 0 else if g ^ 2 = 1 then
    if ∃ i, g i = i then 1 else 2
  else if g ^ 3 = 1 then 3 else 4

/-- Explicit representatives of the five classes. -/
@[expose] def representative : Fin 5 → G :=
  ![1, Equiv.swap 0 1, Equiv.swap 0 1 * Equiv.swap 2 3,
    SymmetricFourConjugacy.threeCycle, Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3]

/-- Cardinalities of the five conjugacy classes. -/
@[expose] def classSize : Fin 5 → ℕ := ![1, 6, 3, 8, 6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem classIndex_conj_check : ∀ g h : G,
    classIndex g = classIndex h ↔ ∃ k : G, k * g * k⁻¹ = h := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem classSize_check : ∀ j, (Finset.univ.filter fun g : G => classIndex g = j).card = classSize j := by decide +kernel

theorem classIndex_representative : ∀ j, classIndex (representative j) = j := by decide +kernel

theorem classIndex_eq_iff (g h : G) :
    classIndex g = classIndex h ↔ ConjClasses.mk g = ConjClasses.mk h := by
  rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff, classIndex_conj_check]

/-- The five representatives enumerate the actual conjugacy-class quotient. -/
noncomputable def classEquiv : Fin 5 ≃ ConjClasses G :=
  Equiv.ofBijective (fun j => ConjClasses.mk (representative j)) (by
    constructor
    · intro i j h
      simpa only [classIndex_representative] using (classIndex_eq_iff _ _).mpr h
    · intro c
      obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
      exact ⟨classIndex g, (classIndex_eq_iff _ _).mp (classIndex_representative _)⟩)

theorem card_conjClasses : Nat.card (ConjClasses G) = 5 := by
  rw [← Nat.card_congr classEquiv]
  simp

/-- Size of the conjugacy class of an arbitrary permutation. -/
theorem card_carrier (g : G) : Nat.card (ConjClasses.mk g).carrier = classSize (classIndex g) := by
  have hset : (ConjClasses.mk g).carrier = {h : G | classIndex h = classIndex g} := by
    ext h
    exact ConjClasses.mem_carrier_iff_mk_eq.trans (classIndex_eq_iff h g).symm
  rw [hset, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact classSize_check _

end SymmetricFourClasses
