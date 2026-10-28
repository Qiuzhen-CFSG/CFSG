module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalModel
public import Theory.GroupTheory.SubgroupClosureFinite

/-!
# Assembly from finite local J4 certificates

The 27 words `u^i v^j z^k` contain the identity and are stable under right
multiplication by the two generators when the two transition identities below
hold. Their coordinate transitions are permutations, so the same family is
stable under multiplication by inverse generators. Subgroup closure induction
therefore proves exhaustiveness. Injectivity gives order 27, and explicit
conjugators for the 26 nonzero coordinates give local cyclic coverage.

The matrix transition identities, injectivity, and conjugator identities are
explicit hypotheses here; this module does not assert their certification.
The words and ATLAS source attribution are in `Threes.LocalModel`.
-/

@[expose] public section

namespace Janko4.Simplicity

/-- Right multiplication coordinates for the first and second generators. -/
def threeLocalNext (t : Fin 3 × Fin 3 × Fin 3) (i : Fin 2) : Fin 3 × Fin 3 × Fin 3 :=
  if i = 0 then (t.1 + 1, t.2.1, t.2.2 - t.2.1)
  else (t.1, t.2.1 + 1, t.2.2)

/-- Inverse coordinate transitions, checked without any matrix computation. -/
def threeLocalPrev (t : Fin 3 × Fin 3 × Fin 3) (i : Fin 2) : Fin 3 × Fin 3 × Fin 3 :=
  if i = 0 then (t.1 - 1, t.2.1, t.2.2 + t.2.1)
  else (t.1, t.2.1 - 1, t.2.2)

theorem threeLocalNext_prev : ∀ t i, threeLocalNext (threeLocalPrev t i) i = t := by
  decide

theorem threeLocalNormalForm_zero
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    threeLocalNormalForm hA hB (0, 0, 0) = 1 := by
  simp [threeLocalNormalForm]

/-- Two finite transition tables suffice to exhaust the generated subgroup. -/
theorem threeLocal_exhaustive_of_transitions
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (hu : ∀ t : Fin 3 × Fin 3 × Fin 3,
      threeLocalNormalForm hA hB t * threeLocalU hA hB =
        threeLocalNormalForm hA hB (t.1 + 1, t.2.1, t.2.2 - t.2.1))
    (hv : ∀ t : Fin 3 × Fin 3 × Fin 3,
      threeLocalNormalForm hA hB t * threeLocalV hA hB =
        threeLocalNormalForm hA hB (t.1, t.2.1 + 1, t.2.2)) :
    ∀ y : Model, y ∈ threeLocalSubgroup hA hB →
      ∃ t, threeLocalNormalForm hA hB t = y := by
  let s : Fin 2 → Model := ![threeLocalU hA hB, threeLocalV hA hB]
  have hs : Set.range s = {threeLocalU hA hB, threeLocalV hA hB} := by
    ext x
    simp [s, or_comm]
  have hn : ∀ t i, threeLocalNormalForm hA hB t * s i =
      threeLocalNormalForm hA hB (threeLocalNext t i) := by
    intro t i
    fin_cases i
    · exact hu t
    · exact hv t
  have he := Theory.GroupTheory.SubgroupEnumeration.closure_range_subset_range_of_transitions
    s (threeLocalNormalForm hA hB) (0, 0, 0) threeLocalNext threeLocalPrev
    (threeLocalNormalForm_zero hA hB) hn threeLocalNext_prev
  rw [hs] at he
  exact he

/-- Distinct and exhaustive normal forms give the exact subgroup order. -/
theorem threeLocal_card_of_normal_forms
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (hinj : Function.Injective (threeLocalNormalForm hA hB))
    (hexh : ∀ y : Model, y ∈ threeLocalSubgroup hA hB →
      ∃ t, threeLocalNormalForm hA hB t = y) :
    Nat.card (threeLocalSubgroup hA hB) = 27 := by
  let f : (Fin 3 × Fin 3 × Fin 3) → threeLocalSubgroup hA hB :=
    fun t => ⟨threeLocalNormalForm hA hB t, threeLocalNormalForm_mem hA hB t⟩
  have hf : Function.Bijective f := by
    constructor
    · exact Subtype.coind_injective (threeLocalNormalForm_mem hA hB) hinj
    · intro y
      obtain ⟨t, ht⟩ := hexh y y.property
      exact ⟨t, Subtype.ext ht⟩
  rw [← Nat.card_eq_of_bijective f hf]
  simp

/-- Conjugacy witnesses for the nonzero coordinates give the local coverage interface. -/
theorem threeLocal_coverage_of_normal_forms
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (hexh : ∀ y : Model, y ∈ threeLocalSubgroup hA hB →
      ∃ t, threeLocalNormalForm hA hB t = y)
    (hconj : ∀ t : Fin 3 × Fin 3 × Fin 3, t ≠ (0, 0, 0) →
      ∃ (i : Fin 2) (g : Model), threeLocalRepresentative hA hB i =
        g * threeLocalNormalForm hA hB t * g⁻¹) :
    ∀ y : Model, y ∈ threeLocalSubgroup hA hB → orderOf y = 3 →
      ∃ i k g, threeLocalRepresentative hA hB i = g * y ^ k * g⁻¹ := by
  intro y hy ho
  obtain ⟨t, rfl⟩ := hexh y hy
  have ht : t ≠ (0, 0, 0) := by
    intro ht
    rw [ht, threeLocalNormalForm_zero, orderOf_one] at ho
    norm_num at ho
  obtain ⟨i, g, hg⟩ := hconj t ht
  exact ⟨i, 1, g, by simpa only [pow_one] using hg⟩

end Janko4.Simplicity
