module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.SporadicTwoLocalContaining
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.SporadicSmallContaining
public import Theory.SpecificGroups.Held.OddOrderBound
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.PairBound

/-!
# Held exclusion and the remaining source containing quotients

The certified graph and pair-stabilizer bounds give the actual Held carrier
order divisor. Its two-part bounds any Suzuki parameter, and both possible
Suzuki orders fail divisibility. The source representation has solvable kernel,
so the original quotient has a factor of three. The proved Held distinctness
and ranked-enlargement contradiction now exclude either strict Held factor.

For Rudvalis, distinctness and the same rank contradiction force the original
quotient to be three-free, hence actually Suzuki by the source nonnormal-component
catalogue. Combining the full Theorem C sieve retains only a strict J4 quotient
or a strict Rudvalis quotient above an original Suzuki group, using the original
exchanger and literal half-join throughout.

Those remaining rows, the zero-kernel binary-three normalizer and final assembly
remain with qt-d-10-nona5-half-sylow-unique. ModuleChoiceAt is the independent input
of qt-d-10-nona5-point-selection; qt-d-10-nona5-point-control retains its final
discharge and the unconditional half-Sylow theorem.
Source: Aschbacher--Smith A.3.12 and 10.2.6, pp.47--48,748--749; the Held carrier
calculations retain their ATLAS and GLS3 attribution in the imported modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 ClassificationModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}

/-- The actual Held order bound excludes every nonabelian Suzuki carrier. -/
theorem suzuki_order_not_dvd_held {m : ℕ} (hm : 1 ≤ m) :
    ¬ Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) ∣ Nat.card Held.He := by
  intro hd
  have hg := Held.Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup
  have ho := Held.OddOrderBound.card_dvd_of_graph_and_pair_bound hg
    (Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.pairStabilizer_card_dvd hg)
  have hdiv := hd.trans ho
  rw [BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card m (by omega)] at hdiv
  have hbound : m ≤ 2 := by
    by_contra h
    have h22 : 2 ^ 14 ∣ 2 ^ 12 * (3 ^ 3 * 5 ^ 2 * 7 ^ 3 * 17) := by
      apply dvd_trans _ hdiv
      apply dvd_trans _ (dvd_mul_of_dvd_left (dvd_mul_left _ _) _)
      rw [←pow_mul]
      exact Nat.pow_dvd_pow 2 (by omega)
    norm_num at h22
  interval_cases m <;> norm_num at hdiv

/-- Held cannot be the first strict containing quotient. -/
theorem ContainingPair.impossible_of_first_strict_held_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hstrict : L.subgroupOf H < K₁)
    (hm : Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* Held.He)) : False := by
  apply C.impossible_of_distinct_three hchoice hmany hn hna
    (C.distinct_of_first_strict_held_or_rudvalis_quotient hchoice hmany hn hna hstrict (.inl hm))
  apply C.three_dvd_of_first_quotient_without_suzuki hn
  intro m h
  rw [Nat.card_congr hm.some.toEquiv]
  exact suzuki_order_not_dvd_held h

/-- The second Held exclusion retains the original exchanger. -/
theorem ContainingPair.impossible_of_second_strict_held_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hstrict : (L.map (MulAut.conj t).toMonoidHom).subgroupOf H < K₂)
    (hm : Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* Held.He)) : False := by
  apply C.impossible_of_distinct_three hchoice hmany hn hna
    (C.distinct_of_second_strict_held_or_rudvalis_quotient hchoice hmany hn hna hstrict (.inl hm))
  apply C.three_dvd_of_second_quotient_without_suzuki hn
  intro m h
  rw [Nat.card_congr hm.some.toEquiv]
  exact suzuki_order_not_dvd_held h

/-- A strict first Rudvalis quotient forces an actual original Suzuki quotient. -/
theorem ContainingPair.suzuki_of_first_strict_rudvalis_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hstrict : L.subgroupOf H < K₁)
    (hm : Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* Rudvalis.Model)) :
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty ((L ⧸ pCore 2 L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  apply (Selection.ModuleChoice.component_quotient_model D hn).suzuki_of_three_free
  intro h3
  exact C.impossible_of_distinct_three hchoice hmany hn hna
    (C.distinct_of_first_strict_held_or_rudvalis_quotient
      hchoice hmany hn hna hstrict (.inr hm)) h3

/-- A strict second Rudvalis quotient forces an actual original Suzuki quotient. -/
theorem ContainingPair.suzuki_of_second_strict_rudvalis_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hstrict : (L.map (MulAut.conj t).toMonoidHom).subgroupOf H < K₂)
    (hm : Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* Rudvalis.Model)) :
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty ((L ⧸ pCore 2 L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  apply (Selection.ModuleChoice.component_quotient_model D hn).suzuki_of_three_free
  intro h3
  exact C.impossible_of_distinct_three hchoice hmany hn hna
    (C.distinct_of_second_strict_held_or_rudvalis_quotient
      hchoice hmany hn hna hstrict (.inr hm)) h3

/-- The complete containing-model sieve now leaves J4, or Rudvalis above Suzuki. -/
theorem ContainingPair.exists_strict_jankoFour_or_rudvalis_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))) :
    ∃ name : SporadicName, (name = .j4 ∨ name = .ru) ∧
      ((L.subgroupOf H < K₁ ∧ Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* name.Carrier)) ∨
       ((L.map (MulAut.conj t).toMonoidHom).subgroupOf H < K₂ ∧
         Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* name.Carrier))) ∧
      (name = .ru → ∃ m : ℕ, 1 ≤ m ∧ Nonempty ((L ⧸ pCore 2 L) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) := by
  obtain ⟨name,hnm,hpair⟩ := C.exists_strict_large_sporadic_quotient hchoice hmany hn hna
  have hhe : name ≠ .he := by
    intro he
    subst name
    rcases hpair with ⟨hs,he⟩ | ⟨hs,he⟩
    · exact C.impossible_of_first_strict_held_quotient hchoice hmany hn hna hs he
    · exact C.impossible_of_second_strict_held_quotient hchoice hmany hn hna hs he
  refine ⟨name,?_,hpair,?_⟩
  · rcases hnm with he | he | he
    · exact .inl he
    · exact (hhe he).elim
    · exact .inr he
  · intro he
    subst name
    rcases hpair with ⟨hs,he⟩ | ⟨hs,he⟩
    · exact C.suzuki_of_first_strict_rudvalis_quotient hchoice hmany hn hna hs he
    · exact C.suzuki_of_second_strict_rudvalis_quotient hchoice hmany hn hna hs he

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
