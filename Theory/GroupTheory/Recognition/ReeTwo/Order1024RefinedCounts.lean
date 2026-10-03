module

public import Theory.GroupTheory.Recognition.ReeTwo.Order1024RefinedCoordinates
public import Theory.GroupTheory.Recognition.ReeTwo.Order1024RefinedCountCertificates
public import Theory.GroupTheory.Recognition.ReeTwo.Order1024RefinedCountConjugacy

/-!
# Internal-centralizer fiber counts for the four refined Ree two candidates

The checked binary parametrizations enumerate the original subgroups. Each
index is conjugate inside its subgroup to a specified representative. Lists of
commuting elements and conjugates give matching bounds on the representative's
centralizer order, and conjugation transports both element order and centralizer
order. Cardinality transport then identifies the finite tallies with the two
intrinsic counts in `refinedFiberCounts`.

Source: Shinoda (1975), (2.3), pp. 81–82, through the verified coordinate model
and the kernel-checked witnesses in `Order1024RefinedCountCertificates`.
-/
namespace ReeTwo.SylowModel
open RefinedCounting

private theorem order_four_iff {G : Type*} [Group G] (x : G) :
    orderOf x = 4 ↔ x ^ 4 = 1 ∧ x ^ 2 ≠ 1 := by
  constructor
  · intro h
    constructor
    · rw [← h]; exact pow_orderOf_eq_one x
    · intro hx
      have hd := orderOf_dvd_of_pow_eq_one hx
      rw [h] at hd
      norm_num at hd
  · rintro ⟨hfour, htwo⟩
    exact @orderOf_eq_prime_pow _ _ x 1 2 ⟨by decide⟩ htwo hfour

private theorem count_conj (c : Fin 4) (n : Fin 1024) :
    countEquiv c n * countEquiv c (countConjugators c n) =
      countEquiv c (countConjugators c n) * countEquiv c (countReps c (countClasses c n)) := by
  apply Subtype.ext
  exact (by simpa only [countMul_eq, Subgroup.coe_mul, countEquiv, Equiv.coe_ofBijective] using countConjugators_valid c n)

private theorem representative_centralizer (c : Fin 4) (j : Fin 52)
    (hj : countFour c j = true) :
    Nat.card (Subgroup.centralizer ({countEquiv c (countReps c j)} :
      Set (residualCandidate (refinedIndex c)))) = countCentralizers c j := by
  have hc := countCentralizers_valid c j hj
  simp only [countCentralizerTest, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hcomm, hcard⟩, hprod⟩ := hc
  let I := {n : Fin 1024 // countClasses c n = j}
  let J := {n : Fin 1024 // n ∈ (countCentralizerList c j).toFinset}
  have hI : Nat.card I = countClassSize c j := Nat.card_eq_fintype_card
  have hJ : Nat.card J = countCentralizers c j := by
    simpa only [J, Nat.card_eq_fintype_card, Fintype.card_coe] using hcard
  have hpos : 0 < Nat.card I := by
    rw [hI]
    nlinarith
  apply centralizer_card_bounds
    (fun i : I => countEquiv c i.val)
    ((countEquiv c).injective.comp Subtype.val_injective)
    (fun i : I => countEquiv c (countConjugators c i.val))
    (countEquiv c (countReps c j))
    (fun i => by simpa only [i.property] using count_conj c i.val)
    (fun i : J => countEquiv c i.val)
    ((countEquiv c).injective.comp Subtype.val_injective)
    (fun i => ?_)
    (countCentralizers c j) hpos
    (by rw [hI, countCandidate_card]; exact hprod) hJ
  apply Subtype.ext
  have hh := List.all_eq_true.mp hcomm i.val (List.mem_toFinset.mp i.property)
  simpa only [decide_eq_true_eq, countMul_eq, Subgroup.coe_mul, countEquiv, Equiv.coe_ofBijective] using hh

private theorem representative_four (c : Fin 4) (j : Fin 52) :
    orderOf (countEquiv c (countReps c j)) = 4 ↔ countFour c j = true := by
  rw [← orderOf_injective (residualCandidate (refinedIndex c)).subtype Subtype.val_injective]
  change orderOf (countElement c (countReps c j)) = 4 ↔ _
  rw [order_four_iff, ← countFourTest_iff, countFour_valid]

private theorem selected_label (c : Fin 4) (n : Fin 1024) (k : ℕ) :
    (orderOf (countEquiv c n), Nat.card (Subgroup.centralizer
      ({countEquiv c n} : Set (residualCandidate (refinedIndex c))))) = (4,k) ↔
      countFour c (countClasses c n) = true ∧ countCentralizers c (countClasses c n) = k := by
  have hconj : MulAut.conj (countEquiv c (countConjugators c n))
      (countEquiv c (countReps c (countClasses c n))) = countEquiv c n := by
    rw [MulAut.conj_apply, ← count_conj, mul_inv_cancel_right]
  have hlabel := Subgroup.order_centralizer_label_mulAut
    (MulAut.conj (countEquiv c (countConjugators c n)))
    (countEquiv c (countReps c (countClasses c n)))
  rw [hconj] at hlabel
  rw [hlabel, Prod.mk.injEq, representative_four]
  constructor
  · rintro ⟨hf, hc⟩
    exact ⟨hf, (representative_centralizer c _ hf).symm.trans hc⟩
  · rintro ⟨hf, hc⟩
    exact ⟨hf, (representative_centralizer c _ hf).trans hc⟩

private theorem selected_fiber (c : Fin 4) (v : RefinedQuotient) (k : ℕ) :
    Subgroup.fiberProfile (refinedProjection c)
      (fun x => (orderOf x, Nat.card (Subgroup.centralizer
        ({x} : Set (residualCandidate (refinedIndex c)))))) v (4,k) =
      Fintype.card {n : Fin 1024 //
        refinedCoordinates c (TailQuotient.projection (countElement c n)) = v ∧
        countFour c (countClasses c n) = true ∧ countCentralizers c (countClasses c n) = k} := by
  classical
  rw [Subgroup.fiberProfile_eq_card_filter, ← Fintype.card_subtype]
  apply Fintype.card_congr
  exact ((countEquiv c).subtypeEquiv (fun n =>
    and_congr Iff.rfl (selected_label c n k).symm)).symm

/-- The selected order-four internal-centralizer counts in every quotient fiber. -/
public theorem refinedProjection_fiberCounts (c : Fin 4) (v : RefinedQuotient) :
    refinedFiberCounts (refinedProjection c) v = refinedProfile c v := by
  unfold refinedFiberCounts
  rw [selected_fiber, selected_fiber]
  exact countProfile_valid c v
end ReeTwo.SylowModel
