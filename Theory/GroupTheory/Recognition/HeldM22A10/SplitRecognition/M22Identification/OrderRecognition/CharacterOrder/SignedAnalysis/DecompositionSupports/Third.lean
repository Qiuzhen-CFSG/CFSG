module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis.DecompositionSupports.FirstTwo

/-!
# Exhausting the third signed support in Janko's Lemma 12

The third induction has principal coefficient one. Its remaining norm is three,
and its scalar products with the first two inductions are one and zero. Its five
signed coordinates in their union therefore have exactly eight possibilities.
Swapping the two unshared constituents of either earlier induction reduces these
to three forms. Enumerating the unused support constructs two, one, or zero new
irreducibles, giving both source alternatives or precisely the rejected pattern.

Source: Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Lemma 12, pp.13–14.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G]
namespace SignedAnalysis.DecompositionSupports

private theorem third_patterns (a : Fin 5 → ℤ)
    (ha : ∀ j, a j = 0 ∨ a j = 1 ∨ a j = -1)
    (h0 : a 0 + a 1 + a 2 = 1) (h1 : a 0 + a 3 + a 4 = 0)
    (hn : ∑ j, a j ^ 2 ≤ 3) :
    a = ![0,0,1,-1,1] ∨ a = ![0,0,1,0,0] ∨ a = ![0,0,1,1,-1] ∨
    a = ![0,1,0,-1,1] ∨ a = ![0,1,0,0,0] ∨ a = ![0,1,0,1,-1] ∨
    a = ![1,0,0,-1,0] ∨ a = ![1,0,0,0,-1] := by
  have ha0 := ha 0
  have ha1 := ha 1
  have ha2 := ha 2
  have ha3 := ha 3
  have ha4 := ha 4
  rcases ha0 with ha0 | ha0 | ha0 <;> rcases ha1 with ha1 | ha1 | ha1 <;>
    rcases ha2 with ha2 | ha2 | ha2 <;> rcases ha3 with ha3 | ha3 | ha3 <;>
    rcases ha4 with ha4 | ha4 | ha4 <;>
    simp_all [funext_iff, Fin.forall_fin_succ, Fin.sum_univ_succ]

private def tailSwap (x y : Bool) : Fin 5 ≃ Fin 5 :=
  (if x then Equiv.swap 1 2 else Equiv.refl _).trans
    (if y then Equiv.swap 3 4 else Equiv.refl _)

variable {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
  {I : SpecialInductionData D k} {E : IntegralExpansion I}

private theorem relabel_first (F : Frame E 5) (x y : Bool)
    (h : I.induced 0 = F.family.term 0 + F.family.term 1 + F.family.term 2) :
    I.induced 0 = (F.reindex (tailSwap x y)).family.term 0 +
      (F.reindex (tailSwap x y)).family.term 1 + (F.reindex (tailSwap x y)).family.term 2 := by
  cases x <;> cases y <;>
    simpa [Frame.reindex_term, tailSwap, Equiv.swap_apply_def, add_comm, add_left_comm, add_assoc] using h

private theorem relabel_second (F : Frame E 5) (x y : Bool)
    (h : I.induced 1 = F.family.term 0 + F.family.term 3 + F.family.term 4) :
    I.induced 1 = (F.reindex (tailSwap x y)).family.term 0 +
      (F.reindex (tailSwap x y)).family.term 3 + (F.reindex (tailSwap x y)).family.term 4 := by
  cases x <;> cases y <;>
    simpa [Frame.reindex_term, tailSwap, Equiv.swap_apply_def, add_comm, add_left_comm, add_assoc] using h

private theorem third_normalized (E : IntegralExpansion I)
    (hU : HasUnitMultiplicities I.induced) :
    ∃ F : Frame E 5,
      I.induced 0 = F.family.term 0 + F.family.term 1 + F.family.term 2 ∧
      I.induced 1 = F.family.term 0 + F.family.term 3 + F.family.term 4 ∧
      (F.coeff 2 = ![0,1,0,0,0] ∨ F.coeff 2 = ![1,0,0,-1,0] ∨
        F.coeff 2 = ![0,1,0,1,-1]) := by
  obtain ⟨F, he0, he1⟩ := first_two E hU
  have hs0 : F.coeff 2 0 + F.coeff 2 1 + F.coeff 2 2 = 1 := by
    have h := I.gram 2 0
    change scalarProduct G (I.induced 2) (I.induced 0) = _ at h
    rw [he0, scalarProduct_add_right, scalarProduct_add_right,
      F.multiplicity, F.multiplicity, F.multiplicity] at h
    have h' : ((F.coeff 2 0 + F.coeff 2 1 + F.coeff 2 2 : ℤ) : ℂ) = 1 := by
      simpa [exceptionalGram] using h
    exact_mod_cast h'
  have hs1 : F.coeff 2 0 + F.coeff 2 3 + F.coeff 2 4 = 0 := by
    have h := I.gram 2 1
    change scalarProduct G (I.induced 2) (I.induced 1) = _ at h
    rw [he1, scalarProduct_add_right, scalarProduct_add_right,
      F.multiplicity, F.multiplicity, F.multiplicity] at h
    have h' : ((F.coeff 2 0 + F.coeff 2 3 + F.coeff 2 4 : ℤ) : ℂ) = 0 := by
      simpa [exceptionalGram] using h
    exact_mod_cast h'
  have hn : ∑ j, F.coeff 2 j ^ 2 ≤ 3 := by
    have h : 1 + ∑ j, F.coeff 2 j ^ 2 ≤ 4 := F.norm_le 2
    omega
  have relabel (x y : Bool)
      (ha : (F.reindex (tailSwap x y)).coeff 2 = ![0,1,0,0,0] ∨
        (F.reindex (tailSwap x y)).coeff 2 = ![1,0,0,-1,0] ∨
        (F.reindex (tailSwap x y)).coeff 2 = ![0,1,0,1,-1]) :
      ∃ F : Frame E 5,
        I.induced 0 = F.family.term 0 + F.family.term 1 + F.family.term 2 ∧
        I.induced 1 = F.family.term 0 + F.family.term 3 + F.family.term 4 ∧
        (F.coeff 2 = ![0,1,0,0,0] ∨ F.coeff 2 = ![1,0,0,-1,0] ∨
          F.coeff 2 = ![0,1,0,1,-1]) :=
    ⟨F.reindex (tailSwap x y), relabel_first F x y he0, relabel_second F x y he1, ha⟩
  rcases third_patterns (F.coeff 2) (F.unit hU 2) hs0 hs1 hn with h | h | h | h | h | h | h | h
  · apply relabel true true
    simp [funext_iff, Fin.forall_fin_succ, Frame.reindex_coeff, tailSwap, Equiv.swap_apply_def, h]
  · apply relabel true false
    simp [funext_iff, Fin.forall_fin_succ, Frame.reindex_coeff, tailSwap, Equiv.swap_apply_def, h]
  · apply relabel true false
    simp [funext_iff, Fin.forall_fin_succ, Frame.reindex_coeff, tailSwap, Equiv.swap_apply_def, h]
  · apply relabel false true
    simp [funext_iff, Fin.forall_fin_succ, Frame.reindex_coeff, tailSwap, Equiv.swap_apply_def, h]
  · apply relabel false false
    simp [funext_iff, Fin.forall_fin_succ, Frame.reindex_coeff, tailSwap, h]
  · apply relabel false false
    simp [funext_iff, Fin.forall_fin_succ, Frame.reindex_coeff, tailSwap, h]
  · apply relabel false false
    simp [funext_iff, Fin.forall_fin_succ, Frame.reindex_coeff, tailSwap, h]
  · apply relabel false true
    simp [funext_iff, Fin.forall_fin_succ, Frame.reindex_coeff, tailSwap, Equiv.swap_apply_def, h]

/-- Exhaustion of the supports: the two source alternatives, or the precise
five-character pattern rejected by Janko's p.14 Suzuki calculation. -/
public theorem alternatives_or_rejected (E : IntegralExpansion I)
    (hU : HasUnitMultiplicities I.induced) :
    HasJankoDecomposition I.induced ∨
      ∃ F : SignedFamily G 5,
        I.induced 0 = F.term 0 + F.term 1 + F.term 2 ∧
        I.induced 1 = F.term 0 + F.term 3 + F.term 4 ∧
        I.induced 2 = 1 + F.term 1 + F.term 3 - F.term 4 := by
  obtain ⟨F, he0, he1, ha | ha | ha⟩ := third_normalized E hU
  · have hn : 1 + ∑ r, F.coeff 2 r ^ 2 +
        ∑ j ∈ F.rest, E.coefficient 2 j ^ 2 = 4 := F.norm_rest 2
    have hr : ∑ j ∈ F.rest, E.coefficient 2 j ^ 2 = 2 := by
      norm_num [ha, Fin.sum_univ_succ] at hn
      omega
    obtain ⟨H, hH, he2⟩ := F.extend hU 2 2 hr
    have ht0 := hH 0
    have ht1 := hH 1
    have ht2 := hH 2
    have ht3 := hH 3
    have ht4 := hH 4
    change H.family.term 0 = F.family.term 0 at ht0
    change H.family.term 1 = F.family.term 1 at ht1
    change H.family.term 2 = F.family.term 2 at ht2
    change H.family.term 3 = F.family.term 3 at ht3
    change H.family.term 4 = F.family.term 4 at ht4
    refine Or.inl (Or.inl ⟨H.family, ?_, ?_, ?_⟩)
    · simpa only [ht0, ht1, ht2] using he0
    · simpa only [ht0, ht3, ht4] using he1
    · simpa [ha, Fin.sum_univ_succ, exceptionalCoefficients, ← ht1, add_assoc] using he2
  · have hn : 1 + ∑ r, F.coeff 2 r ^ 2 +
        ∑ j ∈ F.rest, E.coefficient 2 j ^ 2 = 4 := F.norm_rest 2
    have hr : ∑ j ∈ F.rest, E.coefficient 2 j ^ 2 = 1 := by
      norm_num [ha, Fin.sum_univ_succ] at hn
      omega
    obtain ⟨H, hH, he2⟩ := F.extend hU 2 1 hr
    have ht0 := hH 0
    have ht1 := hH 1
    have ht2 := hH 2
    have ht3 := hH 3
    have ht4 := hH 4
    change H.family.term 0 = F.family.term 0 at ht0
    change H.family.term 1 = F.family.term 1 at ht1
    change H.family.term 2 = F.family.term 2 at ht2
    change H.family.term 3 = F.family.term 3 at ht3
    change H.family.term 4 = F.family.term 4 at ht4
    refine Or.inl (Or.inr ⟨H.family, ?_, ?_, ?_⟩)
    · simpa only [ht0, ht1, ht2] using he0
    · simpa only [ht0, ht3, ht4] using he1
    · simpa [ha, Fin.sum_univ_succ, exceptionalCoefficients, ← ht0, ← ht3,
        sub_eq_add_neg, add_assoc] using he2
  · have hn : (exceptionalCoefficients 2 0) ^ 2 + ∑ r, F.coeff 2 r ^ 2 =
        exceptionalGram 2 2 := by
      change 1 + ∑ r, F.coeff 2 r ^ 2 = 4
      norm_num [ha, Fin.sum_univ_succ]
    have he2 := F.expansion_of_norm_eq hU 2 hn
    refine Or.inr ⟨F.family, he0, he1, ?_⟩
    simpa [ha, Fin.sum_univ_succ, exceptionalCoefficients, sub_eq_add_neg, add_assoc] using he2

end SignedAnalysis.DecompositionSupports
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
