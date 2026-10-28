/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Fischer.ParkerLoopIdentities
public import Theory.AtlasPort.OtherSporadic.Codes.WittDesign

/-!
# The radical of the Golay triple form

A radical word has its coordinatewise product with every Golay word in the
self-dual code. An octad through a nonzero and a zero coordinate would give a
nonzero codeword of weight less than eight. Thus the radical is precisely the
all-ones line. This is the coordinate fact used in Aschbacher, *Sporadic Groups*,
Lemma 27.3(5–6), printed p. 146.

Adapted from Gerald Höhn, ATLAS, `Atlas/Fischer/ParkerTripleRadical.lean`,
revision `1bc46341457aab119f667c43b6ce7216cbb899b6`.
Changes: CFSG module imports and Lean 4.33 boundaries; existence of an octad
through a pair follows directly from the existing Steiner theorem, without
porting the replication-number calculations.
-/

@[expose] public section

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
open scoped BigOperators

/-- A marked octad contains any two distinct marked coordinates. -/
theorem parker_octad_through_pair (p q : Omega) (hpq : p ≠ q) :
    ∃ b : golay, hammingNorm b.val=8 ∧ b.val p ≠ 0 ∧ b.val q ≠ 0 := by
  classical
  obtain ⟨T, hpqT, _, hT⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ ({p,q} : Finset Omega))
    (show ({p,q} : Finset Omega).card ≤ 5 by simp [hpq])
    (show 5 ≤ (Finset.univ : Finset Omega).card by decide)
  obtain ⟨O, ⟨hO, hTO⟩, _⟩ := octad_steiner T hT
  have hpqO := hpqT.trans hTO
  obtain ⟨b,hb,hbs⟩ := (octads_mem O).mp hO
  refine ⟨b,hb,?_,?_⟩
  · have hp : p ∈ support b.val := hbs.symm ▸ hpqO (by simp)
    simpa only [support,Finset.mem_filter,Finset.mem_univ,true_and] using hp
  · have hq : q ∈ support b.val := hbs.symm ▸ hpqO (by simp)
    simpa only [support,Finset.mem_filter,Finset.mem_univ,true_and] using hq

/-- Membership in the radical of the triple form forces every coordinatewise
product with a Golay word to lie in the actual Golay code. -/
theorem parker_radical_product_mem (a : golay)
    (ha : ∀ b c : golay, parkerTripleIntersection a b c=0) (b : golay) :
    (fun p => a.val p*b.val p) ∈ golay := by
  let w : BinaryWord := fun p => a.val p*b.val p
  change w ∈ golay
  rw [golay_selfDual]
  intro c hc
  have h := ha b ⟨c,hc⟩
  simpa only [parkerTripleIntersection,binaryDot_apply,mul_assoc,mul_comm,mul_left_comm] using h

/-- The radical of the actual Golay triple-intersection form is precisely
zero and the all-ones word. The proof uses octads through pairs and minimum8. -/
theorem parkerTripleIntersection_radical (a : golay) :
    (∀ b c : golay, parkerTripleIntersection a b c=0) ↔ a=0 ∨ a=golayOne := by
  classical
  constructor
  · intro ha
    by_cases ha0 : a=0
    · exact Or.inl ha0
    by_cases ha1 : a=golayOne
    · exact Or.inr ha1
    exfalso
    have hp : ∃ p, a.val p ≠ 0 := by
      by_contra h
      push Not at h
      exact ha0 (Subtype.ext (funext h))
    have hq : ∃ q, a.val q ≠ 1 := by
      by_contra h
      push Not at h
      exact ha1 (Subtype.ext (funext h))
    obtain ⟨p,hp⟩ := hp
    obtain ⟨q,hq⟩ := hq
    have hq0 : a.val q=0 := by
      have h : ∀ z : Bit, z ≠ 1 → z=0 := by decide
      exact h _ hq
    have hpq : p ≠ q := by intro he; exact hp (he ▸ hq0)
    obtain ⟨b,hb,hbp,hbq⟩ := parker_octad_through_pair p q hpq
    let w : BinaryWord := fun i => a.val i*b.val i
    have hw : w ∈ golay := parker_radical_product_mem a ha b
    have hw0 : w ≠ 0 := by
      intro h
      have he := congrFun h p
      exact mul_ne_zero hp hbp he
    have hsub : support w ⊆ support b.val := by
      intro i hi
      simp only [support,Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
      exact (mul_ne_zero_iff.mp hi).2
    have hqnot : q ∉ support w := by simp [support,w,hq0]
    have hqmem : q ∈ support b.val := by simp [support,hbq]
    have hstrict : support w ⊂ support b.val := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub,?_⟩
      intro he
      exact hqnot (he.symm ▸ hqmem)
    have hsmall := Finset.card_lt_card hstrict
    change hammingNorm w < hammingNorm b.val at hsmall
    rw [hb] at hsmall
    have hlarge := golay_minimum w hw hw0
    omega
  · rintro (rfl | rfl)
    · intro b c
      simp [parkerTripleIntersection]
    · exact parkerTripleIntersection_one

end Atlas.Fischer
