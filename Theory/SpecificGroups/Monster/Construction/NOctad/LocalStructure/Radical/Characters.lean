module
public import Theory.SpecificGroups.Monster.Construction.NOctad.Basis

/-!
# Even-subset annihilators on an octad

Testing a binary character on every two-point subset forces its restriction
to be constant. Thus the annihilator of all even subsets consists precisely
of empty and full intersections. Since an octad has size eight, both cases
have zero half-intersection parity. These are the two tests used in the
radical block kernel calculation.

Source: Aschbacher, *Sporadic Groups*, 29.13(4), printed p. 160.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.NOctad.LocalStructure.Radical
open Atlas.Codes Atlas.Fischer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

@[simp] theorem subsetWord_zero (c : Octad) : subsetWord c 0 = 0 := by
  funext i
  simp [subsetWord]

theorem binaryDot_subsetWord (c : Octad) (J : EvenSubset c) (d : BinaryWord) :
    binaryDot (subsetWord c J) d = ∑ i : Support c, J.val i * d i.val := by
  change (∑ i, subsetWord c J i * d i) = _
  calc
    _ = ∑ i ∈ Finset.univ.filter (fun i => c.val.val i ≠ 0), subsetWord c J i * d i := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _ hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
      simp [subsetWord, hi]
    _ = _ := by
      rw [Finset.sum_subtype (p := fun i => c.val.val i ≠ 0)
        (F := (inferInstance : Fintype (Support c))) _ (by intro i; simp)]
      simp

/-- Even-subset characters detect restriction modulo the all-one word. -/
theorem evenSubset_annihilator (c : Octad) (d : BinaryWord) :
    (∀ J : EvenSubset c, binaryDot (subsetWord c J) d = 0) ↔
      c.val.val * d = 0 ∨ c.val.val * d = c.val.val := by
  constructor
  · intro h
    let a : Support c := Classical.choice inferInstance
    have hc (i : Support c) : d i.val = d a.val := by
      let J : EvenSubset c := ⟨Pi.single i 1 + Pi.single a 1, by
        simp [BinaryPermutation.mem_core, Finset.sum_add_distrib, CharTwo.add_self_eq_zero]⟩
      have hh := h J
      rw [binaryDot_subsetWord] at hh
      change dotProduct (Pi.single i 1 + Pi.single a 1) (fun j : Support c => d j.val) = 0 at hh
      simp only [add_dotProduct, single_dotProduct, one_mul] at hh
      simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left hh
    rcases bit_cases (d a.val) with ha | ha
    · left
      funext i
      by_cases hi : c.val.val i = 0
      · simp [hi]
      · simp [hc ⟨i, hi⟩, ha]
    · right
      funext i
      by_cases hi : c.val.val i = 0
      · simp [hi]
      · simp [hc ⟨i, hi⟩, ha]
  · intro h J
    rw [binaryDot_subsetWord]
    rcases h with h | h
    · have hd (i : Support c) : d i.val = 0 := by
        have hh := congrFun h i.val
        change c.val.val i.val * d i.val = 0 at hh
        exact (mul_eq_zero.mp hh).resolve_left i.prop
      simp [hd]
    · have hd (i : Support c) : d i.val = 1 := by
        have hh := congrFun h i.val
        change c.val.val i.val * d i.val = c.val.val i.val at hh
        exact mul_left_cancel₀ i.prop (hh.trans (mul_one _).symm)
      have hJ : (∑ i, J.val i) = 0 := J.prop
      simpa only [hd, mul_one] using hJ

/-- Empty or full intersection has even half-intersection parity for an octad. -/
theorem halfOverlap_eq_zero_of_intersection (c : Octad) (d : golay)
    (hd : c.val.val * d.val = 0 ∨ c.val.val * d.val = c.val.val) :
    golayHalfOverlap c.val d = 0 := by
  have hw : overlap c.val.val d.val = hammingNorm (c.val.val * d.val) := by
    simp only [hammingNorm, overlap, Pi.mul_apply, mul_ne_zero_iff]
  change ((overlap c.val.val d.val / 2 : ℕ) : ParkerBit) = 0
  rw [hw]
  rcases hd with hd | hd
  · rw [hd]
    norm_num [hammingNorm]
  · rw [hd, c.prop]
    decide

end Sporadic.Monster.Construction.NOctad.LocalStructure.Radical
