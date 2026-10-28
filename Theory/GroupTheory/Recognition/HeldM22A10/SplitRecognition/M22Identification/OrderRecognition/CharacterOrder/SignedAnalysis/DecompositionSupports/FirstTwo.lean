module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis.DecompositionSupports.SupportFrame

/-!
# The common constituent of Janko's first two inductions

Unit multiplicities and norm three give three signed nonprincipal constituents
in the first induction. Scalar product one leaves six possible projections of
the second induction onto them. Three patterns would use all its norm; in each,
the two degree-zero equations force an irreducible degree to vanish. The other
three are relabelings of one common signed constituent. Enumerating the remaining
norm two supplies two new constituents and the actual five-character family.

Source: Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Lemma 12, p.13.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G]
namespace SignedAnalysis.DecompositionSupports
variable {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
  {I : SpecialInductionData D k} (E : IntegralExpansion I)

private theorem triple_patterns (a : Fin 3 → ℤ)
    (ha : ∀ j, a j = 0 ∨ a j = 1 ∨ a j = -1) (hs : a 0 + a 1 + a 2 = 1) :
    a = ![1,0,0] ∨ a = ![0,1,0] ∨ a = ![0,0,1] ∨
      a = ![-1,1,1] ∨ a = ![1,-1,1] ∨ a = ![1,1,-1] := by
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  rcases h0 with h0 | h0 | h0 <;> rcases h1 with h1 | h1 | h1 <;>
    rcases h2 with h2 | h2 | h2 <;> simp_all [funext_iff, Fin.forall_fin_succ]

private theorem first_three (hU : HasUnitMultiplicities I.induced) :
    ∃ F : Frame E 3, I.induced 0 = F.family.term 0 + F.family.term 1 + F.family.term 2 := by
  let F : Frame E 0 := {
    index := Fin.elim0
    injective := fun j => Fin.elim0 j
    nonprincipal := fun j => Fin.elim0 j
    sign := Fin.elim0
    sign_eq := fun j => Fin.elim0 j }
  have hn := F.norm_rest 0
  have hr : ∑ j ∈ F.rest, E.coefficient 0 j ^ 2 = 3 := by
    simpa [exceptionalCoefficients, exceptionalGram] using hn
  obtain ⟨H, _, he⟩ := F.extend hU 0 3 hr
  refine ⟨H, ?_⟩
  simpa [exceptionalCoefficients, Fin.sum_univ_succ, add_assoc] using he

private theorem term_degree_ne_zero {n : ℕ} (F : Frame E n) (j : Fin n) :
    F.family.term j 1 ≠ 0 := by
  rw [F.family.term_one]
  exact_mod_cast F.family.signedDegree_ne_zero j

/-- Norm three and scalar product one could give three shared constituents.
The two zero-degree equations exclude each such sign pattern. -/
private theorem first_normalized (hU : HasUnitMultiplicities I.induced) :
    ∃ F : Frame E 3,
      I.induced 0 = F.family.term 0 + F.family.term 1 + F.family.term 2 ∧
      F.coeff 1 = ![1,0,0] := by
  obtain ⟨F, he0⟩ := first_three E hU
  have hsum : F.coeff 1 0 + F.coeff 1 1 + F.coeff 1 2 = 1 := by
    have h := I.gram 1 0
    change scalarProduct G (I.induced 1) (I.induced 0) = _ at h
    rw [he0, scalarProduct_add_right, scalarProduct_add_right,
      F.multiplicity, F.multiplicity, F.multiplicity] at h
    have h' : ((F.coeff 1 0 + F.coeff 1 1 + F.coeff 1 2 : ℤ) : ℂ) = 1 := by
      simpa [exceptionalGram] using h
    exact_mod_cast h'
  have hdeg0 : I.induced 0 1 = 0 := I.degree_zero 0
  have hdeg1 : I.induced 1 1 = 0 := I.degree_zero 1
  rcases triple_patterns (F.coeff 1) (F.unit hU 1) hsum with h | h | h | h | h | h
  · exact ⟨F, he0, h⟩
  · refine ⟨F.reindex (Equiv.swap 0 1), ?_, ?_⟩
    · simpa [Frame.reindex_term, Equiv.swap_apply_def, add_comm] using he0
    · ext j
      fin_cases j <;> simp [Frame.reindex_coeff, h, Equiv.swap_apply_def]
  · refine ⟨F.reindex (Equiv.swap 0 2), ?_, ?_⟩
    · simpa [Frame.reindex_term, Equiv.swap_apply_def, add_comm, add_left_comm, add_assoc] using he0
    · ext j
      fin_cases j <;> simp [Frame.reindex_coeff, h, Equiv.swap_apply_def]
  all_goals
    have hn : (exceptionalCoefficients 1 0) ^ 2 + ∑ r, F.coeff 1 r ^ 2 =
        exceptionalGram 1 1 := by norm_num [h, Fin.sum_univ_succ, exceptionalCoefficients, exceptionalGram]
    have he1 := F.expansion_of_norm_eq hU 1 hn
    rw [he0] at hdeg0
    rw [he1] at hdeg1
    simp only [Pi.add_apply] at hdeg0
    simp [h, Fin.sum_univ_succ, exceptionalCoefficients] at hdeg1
  · exact False.elim (term_degree_ne_zero E F 0 (by linear_combination (hdeg0 - hdeg1) / 2))
  · exact False.elim (term_degree_ne_zero E F 1 (by linear_combination (hdeg0 - hdeg1) / 2))
  · exact False.elim (term_degree_ne_zero E F 2 (by linear_combination (hdeg0 - hdeg1) / 2))

/-- The first two exceptional inductions have exactly one common signed
constituent and two further constituents each, all distinct and nonprincipal. -/
public theorem first_two (hU : HasUnitMultiplicities I.induced) :
    ∃ F : Frame E 5,
      I.induced 0 = F.family.term 0 + F.family.term 1 + F.family.term 2 ∧
      I.induced 1 = F.family.term 0 + F.family.term 3 + F.family.term 4 := by
  obtain ⟨F, he0, ha⟩ := first_normalized E hU
  have hn := F.norm_rest 1
  have hr : ∑ j ∈ F.rest, E.coefficient 1 j ^ 2 = 2 := by
    norm_num [ha, Fin.sum_univ_succ, exceptionalCoefficients, exceptionalGram] at hn
    omega
  obtain ⟨H, hH, he1⟩ := F.extend hU 1 2 hr
  have ht0 := hH 0
  have ht1 := hH 1
  have ht2 := hH 2
  change H.family.term 0 = F.family.term 0 at ht0
  change H.family.term 1 = F.family.term 1 at ht1
  change H.family.term 2 = F.family.term 2 at ht2
  refine ⟨H, ?_, ?_⟩
  · simpa only [ht0, ht1, ht2] using he0
  · simpa [ha, Fin.sum_univ_succ, exceptionalCoefficients, ← ht0, add_assoc] using he1

end SignedAnalysis.DecompositionSupports
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
