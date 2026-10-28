module
public import Theory.Representation.BinarySevenCode.WeightTwoSplitting
public import Theory.SpecificGroups.Alternating.SevenFivePlacement

/-!
# The weight-two word fixed by a Sylow-normalized A₅

The seven-letter placement theorem identifies the A₅ with the pointwise
fixer of two letters. Their characteristic word has weight two. Every
permutation normalizing this A₅ preserves its fixed-point set, so it fixes
the word. This includes odd permutations arising from an ambient normalizer.

Source application: Aschbacher--Smith, Lemma 12.3.12, printed p.811,
identifying the A₅ in a proper A₇ overcomponent with the residual in 12.3.7.
-/

@[expose] public noncomputable section
open Subgroup MulAction
open scoped Pointwise
namespace BinarySevenCode.WeightTwoGeometry

/-- A Sylow-normalized A₅ is the pointwise fixer of the support of a
weight-two word. Its full symmetric normalizer fixes that word. -/
theorem exists_weight_two_of_sylow_normalizes_five (B : Subgroup (alternatingGroup (Fin 7)))
    (e : B ≃* alternatingGroup (Fin 5)) (U : Sylow 2 (alternatingGroup (Fin 7)))
    (hU : (U : Subgroup (alternatingGroup (Fin 7))) ≤ normalizer (B : Set (alternatingGroup (Fin 7)))) :
    ∃ w : EvenWord, weight w.val = 2 ∧ five w = B ∧
      normalizer (B.map (alternatingGroup (Fin 7)).subtype : Set (Equiv.Perm (Fin 7))) ≤
        symmetricStabilizer w := by
  classical
  obtain ⟨i,j,hij,hB⟩ :=
    Theory.SpecificGroups.Alternating.SevenFivePlacement.exists_fixed_pair B e U hU
  let w := pairWord i j
  have hs : support w = {i,j} := by
    ext k
    by_cases hki : k = i
    · subst k; simp [support,w,pairWord,hij]
    · by_cases hkj : k = j
      · subst k; simp [support,w,pairWord,hij.symm]
      · simp [support,w,pairWord,hki,hkj]
  have hw : weight w.val = 2 := by
    change (support w).card = 2
    rw [hs,Finset.card_pair hij]
  have hfixed : fixedPoints B (Fin 7) = {i,j} := by
    have hp : ({i,j} : Set (Fin 7)) ⊆ fixedPoints B (Fin 7) := by
      intro x hx b
      have hb : b.val ∈ fixingSubgroup (alternatingGroup (Fin 7)) ({i,j} : Set (Fin 7)) :=
        hB ▸ b.property
      exact hb ⟨x,hx⟩
    exact (Set.eq_of_subset_of_ncard_le hp (by
      rw [Theory.SpecificGroups.Alternating.SevenFivePlacement.fixed_card_two B e U hU,
        Set.ncard_pair hij])).symm
  refine ⟨w,hw,?_,?_⟩
  · simp only [five,hs,Finset.coe_pair,hB]
  · intro g hg
    change g ∈ MulAction.stabilizer (Equiv.Perm (Fin 7)) (support w : Set (Fin 7))
    apply (mem_stabilizer_set' (Set.toFinite _)).mpr
    intro x hx
    have hx' : x ∈ fixedPoints B (Fin 7) := by
      simpa only [hs,Finset.coe_pair,hfixed] using hx
    have hgf : g • x ∈ fixedPoints B (Fin 7) := by
      intro b
      have hb := (mem_normalizer_iff''.mp hg b.val.val).mp
        (mem_map_of_mem (alternatingGroup (Fin 7)).subtype b.property)
      obtain ⟨c,hc,he⟩ := hb
      have hh := hx' ⟨c,hc⟩
      change c.val x = x at hh
      change c.val = g⁻¹ * b.val.val * g at he
      rw [he] at hh
      have hh' := congrArg g hh
      change b.val.val (g x) = g x
      simpa only [Equiv.Perm.coe_mul,Function.comp_apply,Equiv.Perm.coe_inv,
        Equiv.apply_symm_apply] using hh'
    simpa only [hs,Finset.coe_pair,← hfixed] using hgf

end BinarySevenCode.WeightTwoGeometry

