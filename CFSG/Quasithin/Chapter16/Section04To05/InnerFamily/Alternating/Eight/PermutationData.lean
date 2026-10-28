module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Data.ZMod.Basic

/-!
# Four commuting odd involutions in the A₈ model

On the eight letters numbered 0 through 7, let `transposition i` exchange
letters 2i and 2i + 1. The four disjoint transpositions form a basis of an
elementary abelian subgroup of order 16. Their complementary triple products
`triple i` form another basis of the same subgroup: the change of binary
coordinates, replacing each coordinate by the sum of the other three, is
an involution.

The two faithful homomorphisms below identify binary vectors and subset
products with these actual permutations. We compute their cycle types and
show that each generator is conjugate to any permutation of its cycle type
by an element of the actual alternating group. For the distinguished targets,
parity is corrected by `transposition 1` at `transposition 0`, and by
`transposition 0` at `triple 0`; both corrections are odd centralizers.
The finite calculations use kernel-checked decision procedures on four binary
coordinates, never an enumeration of all permutations of eight letters.

This is the finite permutation input for constructing the marked subgroup in
the A₈ branch; no ambient fusion or Sylow assertions are assumed or proved here.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1192.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.AlternatingEight.PermutationData
open Equiv Equiv.Perm

/-- The multiplicative form of the four-dimensional binary vector space. -/
abbrev Binary := Multiplicative (Fin 4 → ZMod 2)

/-- The disjoint transpositions (0 1), (2 3), (4 5), and (6 7). -/
def transposition (i : Fin 4) : Perm (Fin 8) :=
  ![swap 0 1, swap 2 3, swap 4 5, swap 6 7] i

/-- The product of the three transpositions whose index differs from i. -/
def triple (i : Fin 4) : Perm (Fin 8) :=
  ![transposition 1 * transposition 2 * transposition 3,
    transposition 0 * transposition 2 * transposition 3,
    transposition 0 * transposition 1 * transposition 3,
    transposition 0 * transposition 1 * transposition 2] i

/-- The supports of distinct coordinate transpositions are disjoint. -/
theorem transposition_disjoint :
    Pairwise (fun i j => Disjoint (transposition i) (transposition j)) := by
  unfold Pairwise Equiv.Perm.Disjoint
  decide +kernel

/-- All four transpositions commute, including equal indices. -/
theorem transposition_commute (i j : Fin 4) : Commute (transposition i) (transposition j) := by
  by_cases h : i = j
  · subst j; exact Commute.refl _
  · exact (transposition_disjoint h).commute

/-- The four complementary triple products commute. -/
theorem triple_commute (i j : Fin 4) : Commute (triple i) (triple j) := by
  change triple i * triple j = triple j * triple i
  revert i j
  decide +kernel

/-- Every coordinate transposition commutes with every complementary triple. -/
theorem transposition_triple_commute (i j : Fin 4) :
    Commute (transposition i) (triple j) := by
  change transposition i * triple j = triple j * transposition i
  revert i j
  decide +kernel

/-- Each coordinate transposition squares to the identity. -/
theorem transposition_sq (i : Fin 4) : transposition i ^ 2 = 1 := by
  revert i
  decide +kernel

/-- Each complementary triple squares to the identity. -/
theorem triple_sq (i : Fin 4) : triple i ^ 2 = 1 := by
  revert i
  decide +kernel

/-- A coordinate transposition has one two-cycle and six fixed letters. -/
theorem transposition_cycleType (i : Fin 4) : (transposition i).cycleType = {2} := by
  revert i
  decide +kernel

/-- A complementary triple has three two-cycles and two fixed letters. -/
theorem triple_cycleType (i : Fin 4) : (triple i).cycleType = {2, 2, 2} := by
  revert i
  decide +kernel

/-- The coordinate transpositions are nonidentity involutions. -/
theorem transposition_orderOf (i : Fin 4) : orderOf (transposition i) = 2 := by
  rw [← lcm_cycleType, transposition_cycleType]
  decide +kernel

/-- The complementary triples are nonidentity involutions. -/
theorem triple_orderOf (i : Fin 4) : orderOf (triple i) = 2 := by
  rw [← lcm_cycleType, triple_cycleType]
  decide +kernel

/-- The coordinate transpositions are odd permutations. -/
theorem transposition_sign (i : Fin 4) : sign (transposition i) = -1 := by
  rw [sign_of_cycleType, transposition_cycleType]
  decide +kernel

/-- The complementary triples are odd permutations. -/
theorem triple_sign (i : Fin 4) : sign (triple i) = -1 := by
  rw [sign_of_cycleType, triple_cycleType]
  decide +kernel

/-- Multiply the chosen family members in increasing coordinate order. -/
def coordinateProduct (g : Fin 4 → Perm (Fin 8)) (v : Binary) : Perm (Fin 8) :=
  (if v.toAdd 0 = 0 then 1 else g 0) *
    (if v.toAdd 1 = 0 then 1 else g 1) *
    (if v.toAdd 2 = 0 then 1 else g 2) *
    (if v.toAdd 3 = 0 then 1 else g 3)

/-- The homomorphism sending the four binary basis vectors to disjoint transpositions. -/
def transpositionHom : Binary →* Perm (Fin 8) where
  toFun := coordinateProduct transposition
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

/-- Replace each binary coordinate by the sum of the other three. -/
def complementCoordinates (v : Binary) : Binary :=
  Multiplicative.ofAdd ![v.toAdd 1 + v.toAdd 2 + v.toAdd 3,
    v.toAdd 0 + v.toAdd 2 + v.toAdd 3,
    v.toAdd 0 + v.toAdd 1 + v.toAdd 3,
    v.toAdd 0 + v.toAdd 1 + v.toAdd 2]

/-- In dimension four over F₂ the complementary-coordinate transformation is its own inverse. -/
theorem complementCoordinates_involutive : Function.Involutive complementCoordinates := by
  unfold Function.Involutive
  decide +kernel

/-- The invertible change of basis from transpositions to complementary triples. -/
def complementEquiv : Binary ≃* Binary where
  toFun := complementCoordinates
  invFun := complementCoordinates
  left_inv := complementCoordinates_involutive
  right_inv := complementCoordinates_involutive
  map_mul' := by decide +kernel

/-- The faithful binary-coordinate homomorphism for the complementary triples. -/
def tripleHom : Binary →* Perm (Fin 8) :=
  transpositionHom.comp complementEquiv.toMonoidHom

/-- The second homomorphism is exactly the coordinate product of the triple family. -/
theorem tripleHom_apply (v : Binary) : tripleHom v = coordinateProduct triple v := by
  revert v
  decide +kernel

/-- The four disjoint transpositions are independent. -/
theorem transpositionHom_injective : Function.Injective transpositionHom := by decide +kernel

/-- The complementary triples are independent because the change of basis is invertible. -/
theorem tripleHom_injective : Function.Injective tripleHom :=
  transpositionHom_injective.comp complementEquiv.injective

/-- Both families generate the same actual permutation subgroup. -/
theorem tripleHom_range_eq : tripleHom.range = transpositionHom.range := by
  ext p
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨complementEquiv v, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨complementEquiv.symm v, congrArg transpositionHom (complementEquiv.apply_symm_apply v)⟩

/-- The binary characteristic vector of a subset of the four indices. -/
def word (s : Finset (Fin 4)) : Binary :=
  Multiplicative.ofAdd (fun i => if i ∈ s then 1 else 0)

/-- The empty subset gives the identity vector. -/
@[simp] theorem word_empty : word ∅ = 1 := rfl

/-- Inserting an unused coordinate multiplies by its basis vector. -/
theorem word_insert {s : Finset (Fin 4)} {i : Fin 4} (hi : i ∉ s) :
    word (insert i s) = word {i} * word s := by
  ext j
  change (if j ∈ insert i s then (1 : ZMod 2) else 0) =
    (if j ∈ ({i} : Finset (Fin 4)) then 1 else 0) + (if j ∈ s then 1 else 0)
  by_cases hji : j = i
  · subst j; simp [hi]
  · simp [hji]

/-- Different subsets have different binary characteristic vectors. -/
theorem word_injective : Function.Injective word := by
  intro s t h
  ext i
  have hi := congrArg (fun v : Binary => v.toAdd i) h
  change (if i ∈ s then (1 : ZMod 2) else 0) = (if i ∈ t then 1 else 0) at hi
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all

/-- Every binary vector is the characteristic vector of a subset. -/
theorem word_surjective : Function.Surjective word := by
  intro v
  refine ⟨Finset.univ.filter (fun i => v.toAdd i = 1), ?_⟩
  ext i
  change (if i ∈ Finset.univ.filter (fun j => v.toAdd j = 1) then (1 : ZMod 2) else 0) = v.toAdd i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (show ∀ c : ZMod 2, (if c = 1 then (1 : ZMod 2) else 0) = c by decide +kernel) _

/-- The first embedding sends a singleton word to its specified transposition. -/
theorem transpositionHom_word_singleton (i : Fin 4) :
    transpositionHom (word {i}) = transposition i := by
  revert i
  decide +kernel

/-- The second embedding sends a singleton word to its specified triple. -/
theorem tripleHom_word_singleton (i : Fin 4) : tripleHom (word {i}) = triple i := by
  revert i
  decide +kernel

/-- The triple at i is the subset product of all transpositions except the one at i. -/
theorem triple_eq_transpositionHom_complement (i : Fin 4) :
    triple i = transpositionHom (word (Finset.univ.erase i)) := by
  revert i
  decide +kernel

/-- Conversely, the transposition at i is the product of the other three triples. -/
theorem transposition_eq_tripleHom_complement (i : Fin 4) :
    transposition i = tripleHom (word (Finset.univ.erase i)) := by
  revert i
  decide +kernel

/-- Subset products of the disjoint transpositions are distinct. -/
theorem transpositionHom_word_injective :
    Function.Injective (fun s => transpositionHom (word s)) :=
  transpositionHom_injective.comp word_injective

/-- Subset products of the complementary triples are distinct. -/
theorem tripleHom_word_injective :
    Function.Injective (fun s => tripleHom (word s)) :=
  tripleHom_injective.comp word_injective

set_option backward.isDefEq.respectTransparency false in
private theorem hom_word_eq_noncommProd (f : Binary →* Perm (Fin 8))
    (g : Fin 4 → Perm (Fin 8)) (hg : ∀ i, f (word {i}) = g i)
    (hc : ∀ i j, Commute (g i) (g j)) (s : Finset (Fin 4)) :
    f (word s) = s.noncommProd g (fun i _ j _ _ => hc i j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [word_insert hi, map_mul, hg,
      Finset.noncommProd_insert_of_notMem _ _ _ _ hi, ih]

/-- The binary word embedding agrees with the ordinary commuting subset product. -/
theorem transpositionHom_word_eq_noncommProd (s : Finset (Fin 4)) :
    transpositionHom (word s) =
      s.noncommProd transposition (fun i _ j _ _ => transposition_commute i j) :=
  hom_word_eq_noncommProd transpositionHom transposition
    transpositionHom_word_singleton transposition_commute s

/-- The triple word embedding agrees with the ordinary commuting subset product. -/
theorem tripleHom_word_eq_noncommProd (s : Finset (Fin 4)) :
    tripleHom (word s) = s.noncommProd triple (fun i _ j _ _ => triple_commute i j) :=
  hom_word_eq_noncommProd tripleHom triple tripleHom_word_singleton triple_commute s

/-- A subset of k disjoint transpositions has exactly k two-cycles. -/
theorem transpositionHom_word_cycleType (s : Finset (Fin 4)) :
    (transpositionHom (word s)).cycleType = Multiset.replicate s.card 2 := by
  revert s
  decide +kernel

/-- An even subset of k triples has k two-cycles; an odd subset has 4 − k. -/
theorem tripleHom_word_cycleType (s : Finset (Fin 4)) :
    (tripleHom (word s)).cycleType =
      Multiset.replicate (if s.card % 2 = 0 then s.card else 4 - s.card) 2 := by
  revert s
  decide +kernel

private theorem exists_even_conjugator {σ τ c : Perm (Fin 8)}
    (ht : σ.cycleType = τ.cycleType) (hc : Commute c τ) (hs : sign c = -1) :
    ∃ a : alternatingGroup (Fin 8), MulAut.conj (a : Perm (Fin 8)) σ = τ := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_of_cycleType_eq ht)
  by_cases he : sign g = 1
  · exact ⟨⟨g, mem_alternatingGroup.mpr he⟩, hg⟩
  · have ho : sign g = -1 := by
      exact (Int.units_eq_one_or (sign g)).resolve_left he
    refine ⟨⟨c * g, mem_alternatingGroup.mpr ?_⟩, ?_⟩
    · simp [map_mul, hs, ho]
    · change (c * g) * σ * (c * g)⁻¹ = τ
      calc
        (c * g) * σ * (c * g)⁻¹ = c * (g * σ * g⁻¹) * c⁻¹ := by simp [mul_assoc]
        _ = c * τ * c⁻¹ := by rw [hg]
        _ = τ := by rw [hc.eq, mul_inv_cancel_right]

/-- Conjugate a transposition to the distinguished one using an even permutation.
The odd centralizer correction is the disjoint transposition at index 1. -/
theorem even_conjugate_transposition_zero (σ : Perm (Fin 8)) (hσ : σ.cycleType = {2}) :
    ∃ a : alternatingGroup (Fin 8), MulAut.conj (a : Perm (Fin 8)) σ = transposition 0 := by
  exact exists_even_conjugator (hσ.trans (transposition_cycleType 0).symm)
    (transposition_commute 1 0) (transposition_sign 1)

/-- Conjugate a permutation with three two-cycles to the distinguished triple using
an even permutation. The odd correction is the omitted transposition at index 0. -/
theorem even_conjugate_triple_zero (σ : Perm (Fin 8)) (hσ : σ.cycleType = {2, 2, 2}) :
    ∃ a : alternatingGroup (Fin 8), MulAut.conj (a : Perm (Fin 8)) σ = triple 0 := by
  exact exists_even_conjugator (hσ.trans (triple_cycleType 0).symm)
    (transposition_triple_commute 0 0) (transposition_sign 0)

/-- Every transposition is conjugate under A₈ to each of the four first-family generators. -/
theorem even_conjugate_transposition (σ : Perm (Fin 8)) (hσ : σ.cycleType = {2})
    (i : Fin 4) :
    ∃ a : alternatingGroup (Fin 8), MulAut.conj (a : Perm (Fin 8)) σ = transposition i := by
  exact exists_even_conjugator (hσ.trans (transposition_cycleType i).symm)
    (Commute.refl (transposition i)) (transposition_sign i)

/-- Every permutation with three two-cycles is conjugate under A₈ to each triple generator. -/
theorem even_conjugate_triple (σ : Perm (Fin 8)) (hσ : σ.cycleType = {2, 2, 2})
    (i : Fin 4) :
    ∃ a : alternatingGroup (Fin 8), MulAut.conj (a : Perm (Fin 8)) σ = triple i := by
  exact exists_even_conjugator (hσ.trans (triple_cycleType i).symm)
    (Commute.refl (triple i)) (triple_sign i)

/-- Choose the four independent marked generators for either source cycle type.
The image is the same fixed subgroup in both cases, and each generator is an
actual A₈-conjugate of the specified permutation. -/
theorem exists_markedHom (σ : Perm (Fin 8))
    (hσ : σ.cycleType = {2} ∨ σ.cycleType = {2, 2, 2}) :
    ∃ f : Binary →* Perm (Fin 8), Function.Injective f ∧
      f.range = transpositionHom.range ∧
      ∀ i : Fin 4, ∃ a : alternatingGroup (Fin 8),
        MulAut.conj (a : Perm (Fin 8)) σ = f (word {i}) := by
  rcases hσ with hσ | hσ
  · refine ⟨transpositionHom, transpositionHom_injective, rfl, ?_⟩
    intro i
    rw [transpositionHom_word_singleton]
    exact even_conjugate_transposition σ hσ i
  · refine ⟨tripleHom, tripleHom_injective, tripleHom_range_eq, ?_⟩
    intro i
    rw [tripleHom_word_singleton]
    exact even_conjugate_triple σ hσ i

end CFSG.Quasithin.Chapter16.Intersections.AlternatingEight.PermutationData
