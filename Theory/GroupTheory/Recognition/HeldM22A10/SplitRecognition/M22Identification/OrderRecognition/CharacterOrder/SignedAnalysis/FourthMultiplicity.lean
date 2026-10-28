module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis.FourthMultiplicity.Patterns
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis.FourthMultiplicity.Endpoints

/-!
# Unit multiplicities in all five exceptional inductions

This completes Janko's Lemma 11 from the actual local and induction data and
Suzuki pairings. If the fourth induction has a nonunit multiplicity, its norm
five gives two signed irreducibles with coefficients one and two. The exact
Gram matrix reduces the other rows to two patterns. In each, the unused norm
one constructs the additional signed irreducible needed for the source Suzuki
equations. The first contradicts the Sylow three-order; the last contradicts an
integer quadratic modulo nine. Positivity of three linear-combination norms
excludes the intermediate source branch without its longer Sylow-two argument.

The proof assumes neither the ambient order nor any multiplicity conclusion.
Combining the fourth row with the four previously established rows gives
`hasUnitMultiplicities`; Lemma 12's decomposition assembly remains in the parent.

Source: Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Lemma 11, pp.12–13.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy SignedAnalysis.DecompositionSupports
universe u
variable {G : Type u} [Group G] [Finite G]
namespace SignedAnalysis.FourthMultiplicity
variable {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
  {I : SpecialInductionData D k} {E : IntegralExpansion I}

omit [Group G] in
private theorem sp_sub_right (f g h : ClassFunction G) :
    scalarProduct G f (g - h) = scalarProduct G f g - scalarProduct G f h := by
  simp only [scalarProduct, Pi.sub_apply, star_sub, mul_sub, Finset.sum_sub_distrib, mul_sub]

private theorem first_case (F : Frame E 2) (L : LocalAnalysisData D k)
    (hI : HasSuzukiPairings I)
    (he4 : I.induced 3 = F.family.term 0 + (2 : ℂ) • F.family.term 1)
    (h1 : F.coeff 1 = ![-1,1]) : False := by
  have hn := F.norm_rest 1
  have hr : ∑ j ∈ F.rest, E.coefficient 1 j ^ 2 = 1 := by
    norm_num [h1, Fin.sum_univ_succ, exceptionalCoefficients, exceptionalGram] at hn
    omega
  obtain ⟨H, hH, he⟩ := extend_one F 1 hr
  have ht0 := hH 0
  have ht1 := hH 1
  change H.family.term 0 = F.family.term 0 at ht0
  change H.family.term 1 = F.family.term 1 at ht1
  have he4' : I.induced 3 = H.family.term 0 + (2 : ℂ) • H.family.term 1 := by
    simpa only [ht0, ht1] using he4
  have he2' : I.induced 1 = H.family.term 1 - H.family.term 0 + H.family.term 2 := by
    simpa [h1, Fin.sum_univ_succ, exceptionalCoefficients, ← ht0, ← ht1,
      sub_eq_add_neg, add_comm] using he
  exact first_pattern_impossible D k L I hI H.family he4' he2'

private theorem last_case (F : Frame E 2) (L : LocalAnalysisData D k)
    (hI : HasSuzukiPairings I)
    (he4 : I.induced 3 = F.family.term 0 + (2 : ℂ) • F.family.term 1)
    (h3 : F.coeff 3 = ![1,2])
    (h1 : F.coeff 1 = ![1,0]) (h2 : F.coeff 2 = ![-1,1])
    (h4 : F.coeff 4 = ![1,-1]) : False := by
  have h0 := first_absent F L hI he4
  have hn : 1 + ∑ r, F.coeff 2 r ^ 2 +
      ∑ j ∈ F.rest, E.coefficient 2 j ^ 2 = 4 := F.norm_rest 2
  have hr : ∑ j ∈ F.rest, E.coefficient 2 j ^ 2 = 1 := by
    norm_num [h2, Fin.sum_univ_succ, exceptionalCoefficients, exceptionalGram] at hn
    omega
  obtain ⟨H, hH, he⟩ := extend_one F 2 hr
  have ht0 := hH 0
  have ht1 := hH 1
  change H.family.term 0 = F.family.term 0 at ht0
  change H.family.term 1 = F.family.term 1 at ht1
  have hc0 (i : Fin 5) : H.coeff i 0 = F.coeff i 0 := by
    have hh := H.multiplicity i 0
    rw [ht0, F.multiplicity] at hh
    exact_mod_cast hh.symm
  have hc1 (i : Fin 5) : H.coeff i 1 = F.coeff i 1 := by
    have hh := H.multiplicity i 1
    rw [ht1, F.multiplicity] at hh
    exact_mod_cast hh.symm
  have he4' : I.induced 3 = H.family.term 0 + (2 : ℂ) • H.family.term 1 := by
    simpa only [ht0, ht1] using he4
  have he3' : I.induced 2 = 1 + H.family.term 1 - H.family.term 0 + H.family.term 2 := by
    simpa [h2, Fin.sum_univ_succ, exceptionalCoefficients, ← ht0, ← ht1,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using he
  have hg (i : Fin 5) : exceptionalCoefficients i 0 + F.coeff i 1 - F.coeff i 0 +
      H.coeff i 2 = exceptionalGram i 2 := by
    have hp : scalarProduct G (I.induced i) 1 = (exceptionalCoefficients i 0 : ℂ) :=
      I.principal_multiplicity i
    have hh := I.gram i 2
    change scalarProduct G (I.induced i) (I.induced 2) = _ at hh
    rw [he3', scalarProduct_add_right, sp_sub_right, scalarProduct_add_right,
      hp, H.multiplicity, H.multiplicity, H.multiplicity,
      hc0, hc1] at hh
    exact_mod_cast hh
  have hy0 : H.coeff 0 2 = 1 := by
    have hh : 0 + F.coeff 0 1 - F.coeff 0 0 + H.coeff 0 2 = 1 := hg 0
    norm_num [h0, exceptionalCoefficients, exceptionalGram] at hh
    exact hh
  have hy1 : H.coeff 1 2 = 1 := by
    have hh : 0 + F.coeff 1 1 - F.coeff 1 0 + H.coeff 1 2 = 0 := hg 1
    norm_num [h1, exceptionalCoefficients, exceptionalGram] at hh
    omega
  have hy2 : H.coeff 2 2 = 1 := by
    have hh : 1 + F.coeff 2 1 - F.coeff 2 0 + H.coeff 2 2 = 4 := hg 2
    norm_num [h2, exceptionalCoefficients, exceptionalGram] at hh
    omega
  have hy3 : H.coeff 3 2 = 0 := by
    have hh : 0 + F.coeff 3 1 - F.coeff 3 0 + H.coeff 3 2 = 1 := hg 3
    norm_num [h3, exceptionalCoefficients, exceptionalGram] at hh
    omega
  have hy4 : H.coeff 4 2 = 1 := by
    have hh : 0 + F.coeff 4 1 - F.coeff 4 0 + H.coeff 4 2 = -1 := hg 4
    norm_num [h4, exceptionalCoefficients, exceptionalGram] at hh
    omega
  have hv0 : H.family.term 0 D.z = 4 := by
    rw [ht0, involution_column]
    norm_num [h0, h1, h2, h3, h4]
  have hv1 : H.family.term 1 D.z = 14 := by
    rw [ht1, involution_column]
    norm_num [h0, h1, h2, h3, h4]
  have hvY : H.family.term 2 D.z = 5 := by
    rw [involution_column, hy0, hy1, hy2, hy3, hy4]
    norm_num
  exact last_pattern_impossible D k L I hI H.family he4' he3' hv0 hv1 hvY

/-- The missing fourth row of Lemma 11, in the complete integral basis. -/
public theorem fourth_unit (D : LocalData G) (k : TwistedModel ≃* D.centralizer)
    (L : LocalAnalysisData D k) (I : SpecialInductionData D k) (hI : HasSuzukiPairings I)
    (E : IntegralExpansion I) (j : E.Index) :
    E.coefficient 3 j = 0 ∨ E.coefficient 3 j = 1 ∨ E.coefficient 3 j = -1 := by
  by_contra h
  obtain ⟨F, he4, h3⟩ := frame_of_nonunit j h
  rcases remaining_patterns F L hI he4 with h1 | ⟨h1, h2, h4⟩
  · exact first_case F L hI he4 h1
  · exact last_case F L hI he4 h3 h1 h2 h4

end SignedAnalysis.FourthMultiplicity

/-- Every irreducible has multiplicity zero or a unit in the fourth induction. -/
public theorem fourth_unit_multiplicities (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hI : HasSuzukiPairings I)
    (χ : ClassFunction G) (hχ : IsIrreducibleCharacter χ) :
    scalarProduct G (I.induced 3) χ = 0 ∨ scalarProduct G (I.induced 3) χ = 1 ∨
      scalarProduct G (I.induced 3) χ = -1 := by
  obtain ⟨E⟩ := exists_integralExpansion I
  obtain ⟨j, rfl⟩ := E.complete χ hχ
  rw [E.multiplicity]
  rcases SignedAnalysis.FourthMultiplicity.fourth_unit D k L I hI E j with h | h | h <;>
    simp [h]

/-- Janko's Lemma 11: all five actual inductions have unit or zero multiplicities. -/
public theorem hasUnitMultiplicities (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (I : SpecialInductionData D k) (hI : HasSuzukiPairings I) :
    HasUnitMultiplicities I.induced := by
  intro χ hχ i
  by_cases hi : i < 3
  · exact first_three_unit_multiplicities I χ hχ i hi
  · have h : i = 3 ∨ i = 4 := by omega
    rcases h with rfl | rfl
    · exact fourth_unit_multiplicities D k L I hI χ hχ
    · exact fifth_unit_multiplicities D k L I hI χ hχ

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
