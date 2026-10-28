module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Reduction
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.QuotientCensus
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Fusion
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases

/-!
# The three local max2 involution census bounds

The certified quotient and fiber covers place every square-one element of the
literal local subgroup H in one of eleven H-conjugacy classes. Positive ambient
fusion identifies the two colors of each representative and its central translate.
Their certified displacement ranks, 50 and 56, separate the two ambient classes.
Consequently the A,A and B,A sets are covered by two local classes each, and the
B,B set by the three prescribed representatives. Multiplying quotient-class and
fiber bounds gives the required upper bounds without assuming disjointness.

Only the upper bound on |H| remains a premise. In particular, nonconjugacy of z
and t is proved here, and H is not identified with the whole centralizer. The
full-centralizer transport belongs to the ambient order calculation.

Source motivation: Aschbacher--Smith, refs/quasithin.pdf, printed pp.64--65,
A.6.1--4. These are the local B₁(z), C₂(z), and C₁(z) counts used by that
argument, with the B,B count refined to a cover by three H-conjugacy classes.
The numerical bounds follow from the actual word certificates in FiberCensus,
QuotientCensus and Fusion, not from a character-table identification.
-/

set_option backward.isDefEq.respectTransparency true

public section
namespace Janko4.Cardinality.LocalInvolutionCensus

private theorem z_displacementRank : FiberCensus.displacementRank z = 50 := by
  have hr := congrArg Prod.fst (FiberCensus.representative_rankPair_of_source
    FiberCensus.sourceRepresentative_rankPair 2)
  change FiberCensus.displacementRank (eH (representative 2)) = 50 at hr
  exact (FiberCensus.displacementRank_of_isConj
    (firstTarget_isConj_representative 2)).trans hr

private theorem t_displacementRank : FiberCensus.displacementRank t = 56 := by
  have hr := congrArg Prod.fst (FiberCensus.representative_rankPair_of_source
    FiberCensus.sourceRepresentative_rankPair 3)
  change FiberCensus.displacementRank (eH (representative 3)) = 56 at hr
  exact (FiberCensus.displacementRank_of_isConj
    (firstTarget_isConj_representative 3)).trans hr

/-- The two literal ambient representatives are not conjugate: their
displacement ranks are 50 and 56, and that rank is conjugacy invariant. -/
theorem not_isConj_z_t : ¬ IsConj z t := by
  intro hc
  have hr := FiberCensus.displacementRank_of_isConj hc
  rw [z_displacementRank, t_displacementRank] at hr
  contradiction

private theorem not_isConj_t_z : ¬ IsConj t z := fun hc => not_isConj_z_t hc.symm

private theorem z_ne_one : z ≠ 1 := by
  intro he
  have ho := orderOf_z
  rw [he, orderOf_one] at ho
  contradiction

private theorem t_ne_one : t ≠ 1 := by
  intro he
  have hr := t_displacementRank
  simp [he, FiberCensus.displacementRank] at hr

private theorem z_pow_two : z ^ 2 = 1 := by
  simpa only [orderOf_z] using pow_orderOf_eq_one z

private theorem square_one_of_ambient_conjugacy {p : Model} {u : H}
    (hp : p ^ 2 = 1) (hu : IsConj p (eH u)) : u ^ 2 = 1 := by
  apply eH_injective
  rw [map_pow, map_one]
  have hs := hu.pow 2
  rwa [hp, isConj_one_right] at hs

/-- The actual eleven H-classes cover every square-one element of H. -/
theorem square_one_coverage (hH : Nat.card H ≤ 21799895040)
    (u : H) (hu : u ^ 2 = 1) : ∃ i : Fin 11, IsConj (representative i) u :=
  square_one_coverage_of_quotient_and_fibers hH
    (QuotientCensus.quotient_involution_coverage hH) (FiberCensus.coverage hH) u hu

private theorem pair_coverage (hH : Nat.card H ≤ 21799895040)
    {p s : Model} (hp : p ^ 2 = 1) {u : H}
    (hu : IsConj p (eH u) ∧ IsConj s (eH (u * zH))) :
    ∃ i : Fin 11, IsConj (representative i) u ∧
      IsConj p (firstTarget i) ∧ IsConj s (secondTarget i) := by
  obtain ⟨i, hi⟩ := square_one_coverage hH u (square_one_of_ambient_conjugacy hp hu.1)
  have hf := ambient_pair_of_isConj (representative_fusion i) hi
  exact ⟨i, hi, hu.1.trans hf.1.symm, hu.2.trans hf.2.symm⟩

attribute [local irreducible] z t

/-- Only representatives 2 and 7 can contribute to the A,A set. -/
theorem aa_coverage (hH : Nat.card H ≤ 21799895040) :
    aa ⊆ localClass (representative 2) ∪ localClass (representative 7) := by
  intro u hu
  obtain ⟨i, hi, hf, hs⟩ := pair_coverage hH z_pow_two hu
  have he : i = 2 ∨ i = 7 := by
    fin_cases i <;>
      simp only [firstTarget, secondTarget, Matrix.cons_val_zero', Matrix.cons_val_succ', isConj_one_left, z_ne_one, not_isConj_z_t] at hf hs
    all_goals decide
  rcases he with rfl | rfl
  · exact Or.inl hi
  · exact Or.inr hi

/-- Only representatives 6 and 9 can contribute to the B,A set. -/
theorem ba_coverage (hH : Nat.card H ≤ 21799895040) :
    ba ⊆ localClass (representative 6) ∪ localClass (representative 9) := by
  intro u hu
  obtain ⟨i, hi, hf, hs⟩ := pair_coverage hH FusionCertificates.target_sq hu
  have he : i = 6 ∨ i = 9 := by
    fin_cases i <;>
      simp only [firstTarget, secondTarget, Matrix.cons_val_zero', Matrix.cons_val_succ', isConj_one_left, t_ne_one,
        not_isConj_z_t, not_isConj_t_z] at hf hs
    all_goals decide
  rcases he with rfl | rfl
  · exact Or.inl hi
  · exact Or.inr hi

/-- All three prescribed B,B representatives have the required ambient colors. -/
theorem bbRepresentative_mem_bb (i : Fin 3) : bbRepresentative i ∈ bb := by
  fin_cases i
  · exact representative_fusion 3
  · exact representative_fusion 8
  · exact representative_fusion 4

/-- Every B,B element is conjugate inside H to one of the three actual words. -/
theorem bb_coverage (hH : Nat.card H ≤ 21799895040) {u : H} (hu : u ∈ bb) :
    ∃ i : Fin 3, IsConj (bbRepresentative i) u := by
  obtain ⟨i, hi, hf, hs⟩ := pair_coverage hH FusionCertificates.target_sq hu
  have he : i = 3 ∨ i = 8 ∨ i = 4 := by
    fin_cases i <;>
      simp only [firstTarget, secondTarget, Matrix.cons_val_zero', Matrix.cons_val_succ', isConj_one_left, t_ne_one, not_isConj_t_z] at hf hs
    all_goals decide
  rcases he with rfl | rfl | rfl
  · exact ⟨0, hi⟩
  · exact ⟨1, hi⟩
  · exact ⟨2, hi⟩

/-- The seven needed H-class bounds follow from the proved quotient and fiber
certificates; no unproved finite census premise remains. -/
theorem representative_class_card_le (hH : Nat.card H ≤ 21799895040)
    (i : Fin 11) (hi : FiberCensus.Required i) :
    Nat.card (localClass (representative i)) ≤
      quotientBound (fiberIndex i) * fiberBound i :=
  representative_class_bound_of_quotient_and_fiber i
    (QuotientCensus.quotient_class_bounds hH (fiberIndex i))
    (FiberCensus.classFiber_card_le hH i hi)

/-- The local A,A count is at most 1386 + 110880. -/
theorem aa_card_le (hH : Nat.card H ≤ 21799895040) : Nat.card aa ≤ 112266 := by
  calc
    Nat.card aa ≤ Nat.card (localClass (representative 2) ∪
        localClass (representative 7) : Set H) := Set.ncard_mono (aa_coverage hH)
    _ ≤ Nat.card (localClass (representative 2)) +
        Nat.card (localClass (representative 7)) := Set.ncard_union_le _ _
    _ ≤ 1386 + 110880 := Nat.add_le_add
      (representative_class_card_le hH 2 (by simp [FiberCensus.Required]))
      (representative_class_card_le hH 7 (by simp [FiberCensus.Required]))
    _ = 112266 := by decide

/-- The local B,A count is at most 63360 + 18480. -/
theorem ba_card_le (hH : Nat.card H ≤ 21799895040) : Nat.card ba ≤ 81840 := by
  calc
    Nat.card ba ≤ Nat.card (localClass (representative 6) ∪
        localClass (representative 9) : Set H) := Set.ncard_mono (ba_coverage hH)
    _ ≤ Nat.card (localClass (representative 6)) +
        Nat.card (localClass (representative 9)) := Set.ncard_union_le _ _
    _ ≤ 63360 + 18480 := Nat.add_le_add
      (representative_class_card_le hH 6 (by simp [FiberCensus.Required]))
      (representative_class_card_le hH 9 (by simp [FiberCensus.Required]))
    _ = 81840 := by decide

/-- The three B,B H-classes have bounds 2772, 221760, and 532224,
respectively, in the order of `bbRepresentative`. -/
theorem bbRepresentative_class_card_le (hH : Nat.card H ≤ 21799895040)
    (i : Fin 3) :
    Nat.card (localClass (bbRepresentative i)) ≤ ![2772, 221760, 532224] i := by
  fin_cases i
  · exact representative_class_card_le hH 3 (by simp [FiberCensus.Required])
  · exact representative_class_card_le hH 8 (by simp [FiberCensus.Required])
  · exact representative_class_card_le hH 4 (by simp [FiberCensus.Required])

/-- All three requested finite outputs for the literal H and eH. The final
ambient order argument only has to supply the local cardinality upper bound. -/
theorem census (hH : Nat.card H ≤ 21799895040) :
    Nat.card aa ≤ 112266 ∧ Nat.card ba ≤ 81840 ∧
      ∃ r : Fin 3 → H, (∀ i, r i ∈ bb) ∧
        (∀ u ∈ bb, ∃ i, IsConj (r i) u) ∧
        (∀ i, Nat.card (localClass (r i)) ≤ ![2772, 221760, 532224] i) :=
  ⟨aa_card_le hH, ba_card_le hH, bbRepresentative, bbRepresentative_mem_bb,
    fun _ hu => bb_coverage hH hu, bbRepresentative_class_card_le hH⟩

end Janko4.Cardinality.LocalInvolutionCensus
