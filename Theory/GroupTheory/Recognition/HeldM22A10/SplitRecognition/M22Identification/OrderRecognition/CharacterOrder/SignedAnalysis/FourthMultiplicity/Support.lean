module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis.DecompositionSupports.SupportFrame
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis.LowNorm

/-!
# Signed supports for the fourth exceptional induction

A nonunit coordinate in the fourth induction gives two actual signed
nonprincipal irreducibles with coefficients one and two. An unused squared norm
of one appends one actual signed irreducible to a frame. Finally, positivity of
the unused squared norm bounds every integer linear combination of the five
induction rows by their exact Gram matrix.

Source: Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Lemma 11, pp.12–13. The linear-combination bound supplies
an alternative to the longer support enumeration in the middle branch.
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

public theorem combination_norm_le {n : ℕ} (F : Frame E n) (w : Fin 5 → ℤ) :
    (∑ i, w i * exceptionalCoefficients i 0) ^ 2 +
      ∑ r, (∑ i, w i * F.coeff i r) ^ 2 ≤
        ∑ i, ∑ l, w i * w l * exceptionalGram i l := by
  let a (j : E.Index) : ℤ := ∑ i, w i * E.coefficient i j
  have hn : ∑ j, a j ^ 2 = ∑ i, ∑ l, w i * w l * exceptionalGram i l := by
    calc
      _ = ∑ j, ∑ i, ∑ l, w i * w l * (E.coefficient i j * E.coefficient l j) := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [a, pow_two, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = ∑ i, ∑ l, ∑ j, w i * w l * (E.coefficient i j * E.coefficient l j) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by simp only [← Finset.mul_sum, E.gram]
  have hp : a E.principalIndex = ∑ i, w i * exceptionalCoefficients i 0 := by
    simp only [a, E.principal_coefficient]
  have hr (r : Fin n) : a (F.index r) ^ 2 = (∑ i, w i * F.coeff i r) ^ 2 := by
    rcases F.sign_eq r with hs | hs <;>
      simp [a, Frame.coeff, hs, Finset.sum_neg_distrib]
  rw [F.split_sum, hp] at hn
  simp only [hr] at hn
  have hpos : 0 ≤ ∑ j ∈ F.rest, a j ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  omega

public theorem extend_one {n : ℕ} (F : Frame E n) (i : Fin 5)
    (hn : ∑ j ∈ F.rest, E.coefficient i j ^ 2 = 1) :
    ∃ H : Frame E (n + 1),
      (∀ r, H.family.term (Fin.castAdd 1 r) = F.family.term r) ∧
      I.induced i = (exceptionalCoefficients i 0 : ℂ) • (1 : ClassFunction G) +
        ∑ r, (F.coeff i r : ℂ) • F.family.term r +
        H.family.term (Fin.last n) := by
  classical
  obtain ⟨q, hqr, hq⟩ : ∃ q ∈ F.rest, E.coefficient i q ≠ 0 := by
    by_contra h
    have hz : ∀ q ∈ F.rest, E.coefficient i q = 0 := by simpa using h
    have hh : ∑ q ∈ F.rest, E.coefficient i q ^ 2 = 0 :=
      Finset.sum_eq_zero fun q hq => by simp [hz q hq]
    omega
  have hqb : E.coefficient i q ^ 2 ≤ 1 := hn ▸
    Finset.single_le_sum (fun j _ => sq_nonneg (E.coefficient i j)) hqr
  have hqu : E.coefficient i q = 1 ∨ E.coefficient i q = -1 :=
    (int_unit_of_sq_le_three _ (by omega)).resolve_left hq
  have hqs : E.coefficient i q ^ 2 = 1 := by rcases hqu with h | h <;> simp [h]
  have hz (j) (hj : j ∈ F.rest) (hjq : j ≠ q) : E.coefficient i j = 0 := by
    have hh := Finset.sum_erase_add F.rest (fun l => E.coefficient i l ^ 2) hqr
    rw [hn, hqs] at hh
    have hb := Finset.single_le_sum (fun l _ => sq_nonneg (E.coefficient i l))
      (show j ∈ F.rest.erase q by simp [hj, hjq])
    nlinarith [sq_nonneg (E.coefficient i j)]
  let H : Frame E (n + 1) := {
    index := Fin.append F.index (fun _ : Fin 1 => q)
    injective := Fin.append_injective_iff.mpr ⟨F.injective,
      fun _ _ _ => Subsingleton.elim _ _, fun r _ => ((F.mem_rest _).mp hqr).2 r⟩
    nonprincipal := by
      intro r
      refine Fin.addCases (fun j => ?_) (fun j => ?_) r
      · simpa using F.nonprincipal j
      · simpa using ((F.mem_rest _).mp hqr).1
    sign := Fin.append F.sign (fun _ => E.coefficient i q)
    sign_eq := by
      intro r
      refine Fin.addCases (fun j => ?_) (fun j => ?_) r
      · simpa using F.sign_eq j
      · simpa using hqu }
  refine ⟨H, ?_, ?_⟩
  · intro r
    simp [H, Frame.family, SignedFamily.term]
  · rw [E.expansion, F.split_sum, E.principal_coefficient, E.principal_character]
    congr 1
    · simp only [F.coefficient_term]
    · rw [Finset.sum_eq_single q]
      · simp [H, Frame.family, SignedFamily.term, show Fin.last n = Fin.natAdd n (0 : Fin 1) from rfl]
      · intro j hj hjq
        simp [hz j hj hjq]
      · exact fun h => (h hqr).elim

public theorem frame_of_nonunit (p : E.Index)
    (hp : ¬ (E.coefficient 3 p = 0 ∨ E.coefficient 3 p = 1 ∨ E.coefficient 3 p = -1)) :
    ∃ F : Frame E 2,
      I.induced 3 = F.family.term 0 + (2 : ℂ) • F.family.term 1 ∧
      F.coeff 3 = ![1,2] := by
  obtain ⟨q, hqp, hqu, hpu, hz⟩ := norm_five_nonunit_support_two
    (E.coefficient 3) (E.norm_sq 3) p hp
  obtain ⟨s, hs, hps⟩ : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ E.coefficient 3 p = 2 * s := by
    rcases hpu with h | h
    · exact ⟨1, Or.inl rfl, by omega⟩
    · exact ⟨-1, Or.inr rfl, by omega⟩
  have hpn : p ≠ E.principalIndex := by
    intro h
    have hh := E.principal_coefficient 3
    rw [← h] at hh
    have : E.coefficient 3 p = 0 := hh
    exact hp (Or.inl this)
  have hqn : q ≠ E.principalIndex := by
    intro h
    have hh := E.principal_coefficient 3
    rw [← h] at hh
    have : E.coefficient 3 q = 0 := hh
    omega
  let F : Frame E 2 := {
    index := ![q,p]
    injective := by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all
    nonprincipal := by intro j; fin_cases j; exact hqn; exact hpn
    sign := ![E.coefficient 3 q,s]
    sign_eq := by intro j; fin_cases j; exact hqu; exact hs }
  have hc : F.coeff 3 = ![1,2] := by
    ext j
    fin_cases j <;> rcases hqu with hq | hq <;> rcases hs with hs | hs <;>
      simp [Frame.coeff, F, hq, hps, hs]
  refine ⟨F, ?_, hc⟩
  have he := E.expansion_two 3 q p hqp (fun j hjq hjp => hz j hjp hjq)
  have h0 := F.coefficient_term 3 0
  have h1 := F.coefficient_term 3 1
  rw [hc] at h0 h1
  norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_one, Int.cast_ofNat, one_smul] at h0 h1
  change (E.coefficient 3 q : ℂ) • E.character q = F.family.term 0 at h0
  change (E.coefficient 3 p : ℂ) • E.character p = (2 : ℂ) • F.family.term 1 at h1
  simpa only [h0, h1, one_smul] using he

end SignedAnalysis.FourthMultiplicity
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
