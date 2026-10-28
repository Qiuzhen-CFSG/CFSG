module

public import Theory.Character.AlternatingSix.Blocks
public import Theory.Character.PermutationActionCharacter

/-!
# Permutation formulas for the rational A6 characters

Let `P₁`, `P₂`, `P₃` count fixed points, pairs, and triples in the natural
six-letter action. The four rational rows, with the single three-cycles
in the first order-three column, are
`P₂-P₁`, `P₁²+1-2P₁-P₂`, `P₁-1`, and `P₃-P₂`.

Here the point and subset actions are actual complex representations, and
tensor products and direct sums show that all four formulas are generalized
characters. The explicit integer formulas separate finite permutation
calculations from representation realization. Their degrees are already proved;
the remaining integer calculations and conjugacy separation are named below
for independent construction and are consumed by `AlternatingSix.Rational`.

Source: the ordinary A6 rows used by Janko, *A characterization of the Mathieu
simple groups, I*, Section 6, pp.10–11. The permutation differences are the
standard Young permutation-character construction of these rational rows.
-/

@[expose] public section

open scoped BigOperators
noncomputable section

namespace Theory.Character.AlternatingSix.RationalConstruction

abbrev A6 := alternatingGroup (Fin 6)
abbrev Subsets (k : ℕ) := {s : Finset (Fin 6) // s.card = k}

instance subsetsAction (k : ℕ) : MulAction A6 (Subsets k) where
  smul g s := ⟨s.val.map g.val.toEmbedding, by simp [s.property]⟩
  one_smul s := Subtype.ext Finset.map_refl
  mul_smul g h s := by
    apply Subtype.ext
    change s.val.map _ = (s.val.map _).map _
    rw [Finset.map_map]
    rfl

/-- Number of points fixed by the natural six-letter action. -/
def pointCount (g : A6) : ℕ := (Finset.univ.filter fun i => g.val i = i).card
/-- Number of invariant `k`-element subsets of the six letters. -/
def subsetCount (k : ℕ) (g : A6) : ℕ :=
  ((Finset.univ.powersetCard k).filter fun s => s.map g.val.toEmbedding = s).card

private theorem isCharacter_of_representation
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) : IsCharacter ρ.character := by
  let e := (Module.finBasis ℂ V).equivFun
  let σ := e.conjRingEquiv.toMonoidHom.comp ρ
  refine ⟨_, σ, ?_⟩
  ext g
  exact (LinearMap.trace_conj' (ρ g) e).symm

private theorem character_add {G : Type*} [Group G] {χ ψ : ClassFunction G}
    (hχ : IsCharacter χ) (hψ : IsCharacter ψ) : IsCharacter (χ + ψ) := by
  obtain ⟨n, ρ, rfl⟩ := hχ
  obtain ⟨m, σ, rfl⟩ := hψ
  have he : (ρ.prod σ).character = ρ.character + σ.character := by
    ext g
    exact LinearMap.trace_prodMap' (ρ g) (σ g)
  rw [← he]
  exact isCharacter_of_representation _

private theorem character_mul {G : Type*} [Group G] {χ ψ : ClassFunction G}
    (hχ : IsCharacter χ) (hψ : IsCharacter ψ) : IsCharacter (χ * ψ) := by
  obtain ⟨n, ρ, rfl⟩ := hχ
  obtain ⟨m, σ, rfl⟩ := hψ
  rw [← Representation.char_tensor]
  exact isCharacter_of_representation _

def pointCharacter : ClassFunction A6 := (Representation.permutationAction A6 (Fin 6)).character
def subsetCharacter (k : ℕ) : ClassFunction A6 :=
  (Representation.permutationAction A6 (Subsets k)).character

theorem pointCharacter_eq_count (g : A6) : pointCharacter g = (pointCount g : ℂ) := by
  rw [pointCharacter, Representation.permutationAction_character]
  congr 1
  simp only [pointCount, Nat.card_eq_fintype_card, Fintype.card_subtype, MulAction.fixedBy]
  rfl

theorem subsetCharacter_eq_count (k : ℕ) (g : A6) :
    subsetCharacter k g = (subsetCount k g : ℂ) := by
  rw [subsetCharacter, Representation.permutationAction_character]
  congr 1
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, MulAction.fixedBy]
  change (Finset.univ.filter fun s : Subsets k => g • s = s).card = _
  rw [Finset.card_filter]
  simp only [Subtype.ext_iff]
  change (∑ s : Subsets k, if s.val.map g.val.toEmbedding = s.val then 1 else 0) = _
  rw [← Finset.sum_subtype (p := fun s : Finset (Fin 6) => s.card = k)
    (Finset.univ.powersetCard k) (by simp)
    (fun s => if s.map g.val.toEmbedding = s then (1 : ℕ) else 0)]
  simp only [subsetCount, Finset.card_filter]

/-- Integer formulas for the four rational rows, in the natural order-three marking. -/
def rowValues (j : Fin 4) (g : A6) : ℤ :=
  ![(subsetCount 2 g : ℤ) - pointCount g,
    (pointCount g : ℤ) * pointCount g + 1 - (pointCount g + pointCount g + subsetCount 2 g),
    (pointCount g : ℤ) - 1, (subsetCount 3 g : ℤ) - subsetCount 2 g] j

/-- Each row is a difference of actual permutation characters. -/
def rowCharacter : Fin 4 → ClassFunction A6 :=
  ![subsetCharacter 2 - pointCharacter,
    pointCharacter * pointCharacter + 1 - (pointCharacter + pointCharacter + subsetCharacter 2),
    pointCharacter - 1, subsetCharacter 3 - subsetCharacter 2]

theorem rowCharacter_generalized (j : Fin 4) : IsGeneralizedCharacter (rowCharacter j) := by
  have hp := Representation.permutationAction_isCharacter A6 (Fin 6)
  have hs := fun k => Representation.permutationAction_isCharacter A6 (Subsets k)
  change IsCharacter pointCharacter at hp
  change ∀ k, IsCharacter (subsetCharacter k) at hs
  fin_cases j
  · exact ⟨_, _, hs 2, hp, rfl⟩
  · exact ⟨_, _, character_add (character_mul hp hp) isCharacter_one,
      character_add (character_add hp hp) (hs 2), rfl⟩
  · exact hp.sub_one_isGeneralized
  · exact ⟨_, _, hs 3, hs 2, rfl⟩

theorem rowCharacter_eq_values (j : Fin 4) (g : A6) :
    rowCharacter j g = (rowValues j g : ℂ) := by
  fin_cases j <;> simp [rowCharacter, rowValues, pointCharacter_eq_count,
    subsetCharacter_eq_count]


theorem rowValues_one (j : Fin 4) : rowValues j 1 = rationalValues j 0 := by
  have hp : pointCount 1 = 6 := by decide
  have h2 : subsetCount 2 1 = 15 := by decide
  have h3 : subsetCount 3 1 = 20 := by decide
  fin_cases j <;> norm_num [rowValues, hp, h2, h3, rationalValues]

theorem rowCharacter_degree_pos (j : Fin 4) : 0 < (rowCharacter j 1).re := by
  rw [rowCharacter_eq_values, rowValues_one]
  fin_cases j <;> norm_num [rationalValues]

theorem rowCharacter_norm_of_sum (j : Fin 4)
    (h : ∑ g : A6, rowValues j g ^ 2 = 360) :
    scalarProduct A6 (rowCharacter j) (rowCharacter j) = 1 := by
  have hc : Nat.card A6 = 360 := by
    rw [nat_card_alternatingGroup]
    norm_num
  unfold scalarProduct
  simp only [rowCharacter_eq_values, star_intCast, hc]
  have he : (∑ g : A6, (rowValues j g : ℂ) * rowValues j g) = 360 := by
    exact_mod_cast (by simpa only [pow_two] using h : ∑ g : A6, rowValues j g * rowValues j g = 360)
  rw [he]
  norm_num


/-- Finite integer calculations on the actual six-letter permutations. These
assertions contain no representation-theoretic existence or irreducibility
premises. Together with `rowCharacter_generalized` and positive degree they
suffice to construct the four actual irreducibles. -/
structure PermutationCalculations where
  square_sum : ∀ j, ∑ g : A6, rowValues j g ^ 2 = 360
  two : ∀ j x, orderOf x = 2 → rowValues j x = rationalValues j 1
  three : ∀ j x, orderOf x = 3 → rowValues j x =
    rationalValues j (if pointCount x = 3 then 2 else 3)
  four : ∀ j x, orderOf x = 4 → rowValues j x = rationalValues j 4
  five : ∀ j x, orderOf x = 5 → rowValues j x = rationalValues j 5

/-- Nonconjugate elements of order three lie on opposite sides of the natural
fixed-point marking. This is a statement about conjugacy in A6 itself. -/
def OtherThreeSeparation : Prop :=
  ∀ c x : A6, orderOf c = 3 → orderOf x = 3 → ¬ IsConj x c →
    (pointCount x = 3 ↔ pointCount c ≠ 3)

end Theory.Character.AlternatingSix.RationalConstruction
