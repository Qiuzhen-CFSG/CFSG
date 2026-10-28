module
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.OddStarModels
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.SourceCompletion
public import Theory.SpecificGroups.OddThreeRank

/-!
# Canonical radical model exclusion without a full C.2.7 callback

The literal map from K/O₂(K) to the star image has central kernel of odd
order. Consequently it preserves two-rank. Odd-prime linear-three groups
have two-rank at most two; the symplectic and G₂ star models have larger
rank. Central-quotient and order comparisons exclude every remaining
star-model row. Together with the proved swapped-component exclusions,
this proves starred membership for the original radical Configuration.

The characteristic-normalizer control in Configuration remains an actual
input. Its construction and the final 11.4.2 application belong to
qt-d-1222-comparison-nonquasisimple; no source conclusion is assumed here.
Source: Aschbacher--Smith, 1.3.8, pp.513--514; C.2.7, pp.145--147.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter3.RadicalCentralization.ChosenStars
open Chapter1 Chapter1.XiEmbedding Chapter1.RadicalExclusions Chapter1.RadicalExclusions.ModelReduction
open FullSieve FullSieve.LinearThreeExclusion ChapterC.C27Source
variable {Q : Type*} [Group Q] [Finite Q]

private def centerQuotientCongr {A : Type*} [Group A] (e : Q ≃* A) :
    (Q ⧸ center Q) ≃* (A ⧸ center A) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

private theorem linearThree_two_rank {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hm : LinearThreeModel p Q) : primeRank 2 Q ≤ 2 := by
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
  · exact Theory.SpecificGroups.OddThreeRank.special_primeRank_two_le e
      (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card ho
        (k := 1) (by simpa using hF))
  · rw [primeRank_equiv 2 e]
    exact Theory.SpecificGroups.OddThreeRank.psl3_primeRank_two_le Fact.out ho hF

/-- The actual star-model catalogue has no odd-prime linear-three central quotient
when its two-rank is at most two. -/
theorem starModel_not_odd_linearThree (h : StarModels.Model Q)
    (hr : primeRank 2 Q ≤ 2) {p : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (ho : Odd p) :
    ¬ ClassicalGroup.IsPSL (Q ⧸ center Q) 3 p := by
  intro hm
  have hcard : Nat.card (Q ⧸ center Q) ≤ Nat.card Q :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (center Q))
  cases h with
  | linearTwo F e =>
    have he : ClassicalGroup.IsPSL (Q ⧸ center Q) 2 (2^F.degree) :=
      ⟨F.Carrier,inferInstance,inferInstance,F.card_eq,⟨centerQuotientCongr e⟩⟩
    exact not_even_rankOne_model hp ho (Or.inr hm) he
  | linearThree F e =>
    have he : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 (2^F.degree) :=
      ⟨F.Carrier,inferInstance,inferInstance,F.card_eq,⟨centerQuotientCongr e⟩⟩
    exact not_even_projective_model hp ho hm he
  | symplectic F _ e =>
    have hlo := Theory.SpecificGroups.SymplecticFour.EvenTwoRank.three_mul_le_rank F.card_eq
    rw [primeRank_equiv 2 e] at hr
    have := F.degree_pos
    change 3 * F.degree ≤ primeRank 2 (Matrix.symplecticGroup (Fin 2) F.Carrier) at hlo
    omega
  | g2 F _ e =>
    have hlo := Atlas.G2.EvenTwoRank.rank_ge F.Carrier F.card_eq
    rw [primeRank_equiv 2 e] at hr
    have := F.degree_pos
    omega
  | g2DerivedTwo e =>
    have hc : Nat.card Q = 6048 := by
      rw [Nat.card_congr e.toEquiv,Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
      exact Atlas.G2.BinaryException.card_H
    exact not_linearThree_of_small_order hp (by omega) (Or.inr hm)
  | alternating n hn e =>
    have hc : Nat.card Q ≤ 20160 := by
      rcases hn with rfl | rfl | rfl | rfl <;>
        rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin] <;> norm_num
    exact not_linearThree_of_small_order hp (hcard.trans hc) (Or.inr hm)
  | linearFiveTwo e =>
    have he : ClassicalGroup.IsPSL (Q ⧸ center Q) 5 2 :=
      ⟨ZMod 2,inferInstance,inferInstance,by simp,⟨centerQuotientCongr e⟩⟩
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := he
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
    rw [←Nat.card_congr a.toEquiv,hF] at hc
    norm_num [Fin.prod_univ_succ] at hc
    exact not_linearThree_of_large_exceptional_order hp (Or.inr hc) (Or.inr hm)
  | tripleSix _ e =>
    have hc : Nat.card (Q ⧸ center Q) = 360 := by
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
      norm_num
    exact not_linearThree_of_small_order hp (by omega) (Or.inr hm)

variable {G : Type*} [Group G] [Finite G]

/-- The original pushing-up input itself excludes the linear-three branch;
no full C.2.7 callback is needed. -/
theorem source_not_odd_linearThree {H R M K : Subgroup G}
    (h : FullSieve.SourceInterface.Input KnownSimple.IsKnownSimple H R M K)
    {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (ho : Odd p) :
    ¬ LinearThreeModel p (XiQuotient K) := by
  intro hm
  have hc : Nat.Coprime 2 (Nat.card (center (XiQuotient K))) := by
    rcases coreQuotient_center_card_from_source h with hc | hc <;> rw [hc] <;> decide
  have hk := hc.coprime_dvd_right (card_dvd_of_le (coreToStar_ker_central_from_source h))
  have hr := (primeRank_le_of_surjective_of_coprime 2 (coreToStar h.normalizes)
    (coreToStar_surjective h.normalizes) hk).trans (linearThree_two_rank ho hm)
  have he := coreStarCenterEquiv h.normalizes h.quasisimple
    (starImage_ne_bot_of_bound h.normalizes h.quasisimple (kernel_offender_from_source h).1.upper)
  exact starModel_not_odd_linearThree (star_model_from_source h) hr hp ho
    ((linearThree_center_model hm).of_mulEquiv he.symm)

/-- Both genuine adequate-embedding branches are impossible in the original
radical configuration. This completes its model-exclusion step. -/
theorem configuration_mem_XiStar
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {p : ℕ} {X P L M : Subgroup G} (h : Configuration p T X P L M) :
    X ∈ XiStar G (T : Subgroup G) := by
  refine ⟨h.xi,?_⟩
  intro K hK hq hXT
  let h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun A _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun A _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
  have hout := Configuration.initial_not_le_of_A36 hG h36 h hK hq hXT
  obtain ⟨B,hB⟩ := Configuration.exists_componentCandidate_knownSimple hG T h
    ⟨hK.2.2,fun _ ht => mem_sup_right ht⟩ hXT hout
  have hc := hB.toPushingUpComponent (ComponentCandidate.not_le_of_configuration h hB)
  rcases hB.alternatives.2 with ⟨hs,hm⟩ | ⟨_,hm⟩
  · exact hc.false_of_swapped T h (lemma_1_1_4_6 T (hG.evenCharacteristic T)) hs hm
  · let : Fact p.Prime := ⟨h.prime⟩
    have hp5 : 5 ≤ p := by obtain ⟨a,ha⟩ := h.odd; have := h.large; omega
    exact source_not_odd_linearThree (FullSieve.SourceInterface.input_of_pushingUpComponent hc)
      hp5 h.odd hm

end CFSG.Quasithin.Chapter3.RadicalCentralization.ChosenStars
