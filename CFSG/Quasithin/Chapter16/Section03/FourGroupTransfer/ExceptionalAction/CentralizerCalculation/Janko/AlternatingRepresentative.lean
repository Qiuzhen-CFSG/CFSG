module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Janko.AlternatingModel

/-!
# Two-subgroups and the full A₅ fixer in the concrete J₂ carrier

The simple factor fixed in `AlternatingModel` has an element of order three
in its full pointwise automorphism fixer. In fact that fixer contains twelve
explicit distinct inner automorphisms. Thus its cardinality is not at most
four, and its elements do not all square to one.

The witness is a word in the retained degree-100 generators. Its permutation
is the product `rep2 1 * rep3 2` of two existing transversal tables. Kernel
checks establish the word identity, commutation with all sixty words of the
published A₅ embedding, and order three. Multiplication by the four central
words gives twelve distinct elements, distinguished by their images of the
points 0 and 2. Faithfulness of inner conjugation transfers these statements
to the full `MulAut` fixer without any involution assumption on its elements.

The separately named `representativeA5_two_subgroup_bound` proves that every
two-subgroup of this fixer has at most four elements and exponent at most two.
The full automorphism equivalence and normal-form coverage reduce the proof
to concrete permutations. Commutation with three displayed simple-factor words
restricts the first two transversal indices; two further point checks exhaust
the remaining candidates. Kernel checks show that each survivor either has
cube one or is one of the four retained central-factor words. A two-group
contains no nonidentity element with cube one, so it embeds in those four
words, whose squares are checked to be one. This adequate two-subgroup result
does not assert the false bound on the whole fixer.

Source context: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.5(8), 16.1.7(3f), and 16.3.5, printed pp.1172–1173 and 1178–1179.
This obstructs the proposed bound on the quotient-model fixer; it does not
refute 16.3.5, whose conclusion concerns the actual covering overgroup with
nontrivial two-core. The original embedding and carrier are unchanged.

Attribution: R. A. Wilson et al., ATLAS of Finite Group Representations,
J2G1-p100B0. Original data, attribution and source rights remain in
`Theory/SpecificGroups/LeechRelated/AtlasCarriers/source/`. The word was
found with GAP; every identity used here is checked by the Lean kernel.
-/

public section

namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Janko
open Subgroup
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
open Sporadic.LeechRelated.J2.GeneratorPair.SecondOrbitCertificate
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims
open J2Inner.NoncentralData
set_option maxRecDepth 100000
set_option Elab.async false

private def threeElement : Carrier :=
  (a * b) ^ 2 * a * b⁻¹ * (a * b⁻¹ * a * b) ^ 2 *
    (a * b⁻¹) ^ 2 * (a * b) ^ 2 * a

private def threeTable : Equiv.Perm (Fin 100) := rep2 1 * rep3 2

private theorem threeElement_inclusion : inclusion threeElement = threeTable := by
  simp only [threeElement, map_mul, map_pow, map_inv, a_inclusion, b_inclusion]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem threeTable_commutes : ∀ i : Fin 60,
    Commute threeTable (conjugatorTable (simpleIndex i)) := by
  have h : ∀ (i : Fin 60) (x : Fin 100),
      (threeTable * conjugatorTable (simpleIndex i)) x =
        (conjugatorTable (simpleIndex i) * threeTable) x := by
    apply allFin
    decide +kernel
  intro i
  exact Equiv.ext (h i)

private theorem fixes_of_commutes (g : Carrier)
    (hg : ∀ i : Fin 60, Commute g (conjugator (simpleIndex i))) :
    MulAut.conj g ∈ fixingSubgroup (MulAut Carrier) (representativeA5 : Set Carrier) := by
  apply (mem_fixingSubgroup_iff _).mpr
  intro y hy
  obtain ⟨⟨e, s⟩, hes, rfl⟩ := hy
  have he : e = 1 := hes.1
  subst e
  obtain ⟨i, rfl⟩ := simpleEquiv.surjective s
  change g * (J2Inner.a_centralizer_equiv.symm (1, simpleEquiv i)).val * g⁻¹ =
    (J2Inner.a_centralizer_equiv.symm (1, simpleEquiv i)).val
  rw [J2Inner.a_centralizer_equiv_symm_simple, (hg i).eq, mul_inv_cancel_right]

private theorem threeElement_fixes :
    MulAut.conj threeElement ∈
      fixingSubgroup (MulAut Carrier) (representativeA5 : Set Carrier) := by
  apply fixes_of_commutes
  intro i
  apply Sporadic.LeechRelated.J2.inclusion_injective
  simpa only [map_mul, threeElement_inclusion, conjugator_inclusion] using
    (threeTable_commutes i).eq

private theorem threeElement_cube : threeElement ^ 3 = 1 := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_pow, threeElement_inclusion, map_one]
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem threeElement_square_ne : threeElement ^ 2 ≠ 1 := by
  intro h
  have hp := congrArg inclusion h
  rw [map_pow, threeElement_inclusion, map_one] at hp
  exact (by decide +kernel : (threeTable ^ 2) 2 ≠ (1 : Equiv.Perm (Fin 100)) 2)
    (congrArg (fun p : Equiv.Perm (Fin 100) => p 2) hp)

private theorem order_three_in_fixer (g : Carrier)
    (hfix : MulAut.conj g ∈
      fixingSubgroup (MulAut Carrier) (representativeA5 : Set Carrier))
    (hg3 : g ^ 3 = 1) (hg2 : g ^ 2 ≠ 1) :
    ∃ x : fixingSubgroup (MulAut Carrier) (representativeA5 : Set Carrier),
      orderOf x = 3 ∧ x ^ 2 ≠ 1 := by
  let x : fixingSubgroup (MulAut Carrier) (representativeA5 : Set Carrier) :=
    ⟨MulAut.conj g, hfix⟩
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    change (MulAut.conj g) ^ 3 = 1
    rw [← map_pow, hg3, map_one]
  have hx2 : x ^ 2 ≠ 1 := by
    intro h
    have he : (MulAut.conj g) ^ 2 = 1 := congrArg Subtype.val h
    rw [← map_pow, ← map_one MulAut.conj] at he
    exact hg2 (J2Reduction.conj_injective he)
  exact ⟨x, orderOf_eq_prime hx3 (by intro h; apply hx2; simp [h]), hx2⟩

/-- The full fixer contains an element of order three whose square is not one. -/
theorem representativeA5_fixer_has_order_three :
    ∃ x : fixingSubgroup (MulAut Carrier) (representativeA5 : Set Carrier),
      orderOf x = 3 ∧ x ^ 2 ≠ 1 :=
  order_three_in_fixer threeElement threeElement_fixes threeElement_cube threeElement_square_ne

private def fourIndex : Fin 4 → Fin 240 := ![0, 1, 79, 119]

private theorem fourTable_commutes : ∀ (i : Fin 4) (j : Fin 60),
    Commute (conjugatorTable (fourIndex i)) (conjugatorTable (simpleIndex j)) := by
  have h : ∀ (i : Fin 4) (j : Fin 60) (x : Fin 100),
      (conjugatorTable (fourIndex i) * conjugatorTable (simpleIndex j)) x =
        (conjugatorTable (simpleIndex j) * conjugatorTable (fourIndex i)) x := by
    apply allFin
    decide +kernel
  intro i j
  exact Equiv.ext (h i j)

private theorem four_fixes (i : Fin 4) :
    MulAut.conj (conjugator (fourIndex i)) ∈
      fixingSubgroup (MulAut Carrier) (representativeA5 : Set Carrier) := by
  apply fixes_of_commutes
  intro j
  apply Sporadic.LeechRelated.J2.inclusion_injective
  simpa only [map_mul, conjugator_inclusion] using (fourTable_commutes i j).eq

private def twelveWord (i : Fin 4 × Fin 3) : Carrier :=
  conjugator (fourIndex i.1) * threeElement ^ i.2.val

private def twelveTable (i : Fin 4 × Fin 3) : Equiv.Perm (Fin 100) :=
  conjugatorTable (fourIndex i.1) * threeTable ^ i.2.val

private theorem twelveWord_inclusion (i : Fin 4 × Fin 3) :
    inclusion (twelveWord i) = twelveTable i := by
  simp only [twelveWord, twelveTable, map_mul, map_pow, conjugator_inclusion,
    threeElement_inclusion]

private theorem twelve_fixes (i : Fin 4 × Fin 3) :
    MulAut.conj (twelveWord i) ∈
      fixingSubgroup (MulAut Carrier) (representativeA5 : Set Carrier) := by
  rw [twelveWord, map_mul, map_pow]
  exact Subgroup.mul_mem _ (four_fixes i.1) (Subgroup.pow_mem _ threeElement_fixes _)

private theorem twelveTable_injective :
    Function.Injective (fun i : Fin 4 × Fin 3 => (twelveTable i 0, twelveTable i 2)) := by
  decide +kernel

/-- The full pointwise fixer of the retained A₅ factor has at least twelve elements. -/
theorem representativeA5_fixer_card_ge_twelve :
    12 ≤ Nat.card (fixingSubgroup (MulAut Carrier) (representativeA5 : Set Carrier)) := by
  let f : Fin 4 × Fin 3 →
      fixingSubgroup (MulAut Carrier) (representativeA5 : Set Carrier) :=
    fun i => ⟨MulAut.conj (twelveWord i), twelve_fixes i⟩
  have hf : Function.Injective f := by
    intro i j h
    have hword : twelveWord i = twelveWord j :=
      J2Reduction.conj_injective (congrArg Subtype.val h)
    have hp := congrArg inclusion hword
    rw [twelveWord_inclusion, twelveWord_inclusion] at hp
    exact twelveTable_injective (congrArg (fun p : Equiv.Perm (Fin 100) => (p 0, p 2)) hp)
  simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_le_card_of_injective f hf

/-- Both requested bounds fail for the literal full pointwise fixer. -/
theorem representativeA5_fixer_bound_obstruction :
    ¬ Nat.card (fixingSubgroup (MulAut Carrier) (representativeA5 : Set Carrier)) ≤ 4 ∧
      ¬ (∀ x : fixingSubgroup (MulAut Carrier) (representativeA5 : Set Carrier), x ^ 2 = 1) := by
  constructor
  · have := representativeA5_fixer_card_ge_twelve
    omega
  · obtain ⟨x, _, hx⟩ := representativeA5_fixer_has_order_three
    exact fun h => hx (h x)

section TwoSubgroupBound

open Sporadic.LeechRelated.J2.ExceptionalParabolics
open scoped Pointwise
set_option maxHeartbeats 1000000

private def outerTable (o : Bool) : Equiv.Perm (Fin 100) := if o then involution else 1

private theorem extension_cover (e : Extension) :
    ∃ (o : Bool) (i : Index), e.val = outerTable o * normalForm i := by
  have he : e.val ∈ (zpowers involution : Set (Equiv.Perm (Fin 100))) *
      (generated : Set (Equiv.Perm (Fin 100))) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _
      (zpowers_le.mpr involution_mem_normalizer), sup_comm]
    exact e.property
  obtain ⟨u, hu, v, hv, huv⟩ := he
  obtain ⟨i, hi⟩ := normalForm_cover (⟨v, hv⟩ : Carrier)
  have hi' : v = normalForm i := hi
  have ho : orderOf involution = 2 := by
    apply orderOf_eq_prime (by simpa only [pow_two] using involution_mul_self)
    intro h
    have := congrArg (fun p : Equiv.Perm (Fin 100) => p 1) h
    exact (by decide +kernel : involution 1 ≠ (1 : Equiv.Perm (Fin 100)) 1) this
  change u ∈ zpowers involution at hu
  rw [mem_zpowers_iff_mem_range_orderOf, ho] at hu
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hu
  have hn' : n = 0 ∨ n = 1 := by have := Finset.mem_range.mp hn; omega
  rcases hn' with rfl | rfl
  · exact ⟨false, i, by simpa only [pow_zero, one_mul, hi', outerTable, Bool.false_eq_true,
      ↓reduceIte, one_mul] using huv.symm⟩
  · exact ⟨true, i, by simpa only [pow_one, hi', outerTable, ↓reduceIte] using huv.symm⟩

private theorem action_surjective : Function.Surjective extensionAction :=
  ((Nat.bijective_iff_injective_and_card extensionAction).mpr
    ⟨extensionAction_injective, Nat.card_congr J2Reduction.fullAutomorphismEquiv.toEquiv⟩).2

private theorem simple_mem (j : Fin 60) : conjugator (simpleIndex j) ∈ representativeA5 := by
  rw [← J2Inner.a_centralizer_equiv_symm_simple]
  exact Subgroup.mem_map.mpr ⟨(1, simpleEquiv j), ⟨by simp, by simp⟩, rfl⟩

private theorem commutes_of_fixes (e : Extension)
    (he : extensionAction e ∈ fixingSubgroup (MulAut Carrier) (representativeA5 : Set Carrier))
    (j : Fin 60) : Commute e.val (conjugatorTable (simpleIndex j)) := by
  have h := (mem_fixingSubgroup_iff _).mp he _ (simple_mem j)
  have hp := congrArg inclusion h
  change e.val * inclusion (conjugator (simpleIndex j)) * e.val⁻¹ =
    inclusion (conjugator (simpleIndex j)) at hp
  rw [conjugator_inclusion] at hp
  exact (mul_inv_eq_iff_eq_mul.mp hp : _)


private def firstIndex : Fin 4 → Fin 100 := ![0, 1, 9, 11]

private def secondIndex (o : Bool) : Fin 4 → Fin 63 :=
  if o then ![51, 51, 9, 50] else ![0, 0, 15, 10]

private def candidate (o : Bool) (i : Fin 4) (k : Fin 24) (l : Fin 4) :
    Equiv.Perm (Fin 100) :=
  outerTable o * normalForm (firstIndex i, secondIndex o i, k, l)

-- The image of point 0 restricts the first transversal to four choices.
private theorem first_filter (o : Bool) : ∀ i : Fin 100,
    conjugatorTable (simpleIndex 27) (outerTable o (rep0 i 0)) = outerTable o (rep0 i 0) →
    conjugatorTable (simpleIndex 34) (outerTable o (rep0 i 0)) = outerTable o (rep0 i 0) →
    ∃ j : Fin 4, i = firstIndex j := by
  cases o <;> apply allFin <;> decide +kernel

-- The image of point 1 fixes the second transversal for each outer/inner choice.
private theorem second_filter (o : Bool) : ∀ (i : Fin 4) (j : Fin 63),
    outerTable o (rep0 (firstIndex i) (rep1 j 1)) =
      conjugatorTable (simpleIndex 14) (outerTable o (rep0 (firstIndex i) 0)) →
    j = secondIndex o i := by
  cases o <;> apply allFin <;> decide +kernel

private theorem candidate_cover (o : Bool) (i : Index)
    (hc : ∀ j : Fin 60, Commute (outerTable o * normalForm i)
      (conjugatorTable (simpleIndex j))) :
    ∃ j : Fin 4, outerTable o * normalForm i = candidate o j i.2.2.1 i.2.2.2 := by
  obtain ⟨i, j, k, l⟩ := i
  have hz (z : Fin 60) (hz : conjugatorTable (simpleIndex z) 0 = 0) :
      conjugatorTable (simpleIndex z) (outerTable o (rep0 i 0)) =
        outerTable o (rep0 i 0) := by
    have hh := congrArg (fun p : Equiv.Perm (Fin 100) => p 0) (hc z).eq
    simpa only [normalForm, Equiv.Perm.mul_apply, hz,
      FirstParabolic.OrderData.rep3_fix0, FirstParabolic.OrderData.rep2_fix0,
      FirstParabolic.OrderData.rep1_fix0] using hh.symm
  obtain ⟨t, rfl⟩ := first_filter o i (hz 27 (by decide +kernel)) (hz 34 (by decide +kernel))
  have hj : j = secondIndex o t := by
    apply second_filter o t j
    have hh := congrArg (fun p : Equiv.Perm (Fin 100) => p 0) (hc 14).eq
    have hz : conjugatorTable (simpleIndex 14) 0 = 1 := by decide +kernel
    simpa only [normalForm, Equiv.Perm.mul_apply, hz,
      FirstParabolic.OrderData.rep3_fix0, FirstParabolic.OrderData.rep2_fix0,
      FirstParabolic.OrderData.rep1_fix0, FirstParabolic.OrderData.rep3_fix1,
      FirstParabolic.OrderData.rep2_fix1] using hh
  exact ⟨t, by subst j; rfl⟩

-- These two commutation tests exhaust the 2 × 4 × 24 × 4 remaining candidates.
-- Full permutation identities, including all claimed cubes, are kernel checked.
private theorem final_filter (o : Bool) : ∀ (i : Fin 4) (k : Fin 24) (l : Fin 4),
    candidate o i k l (conjugatorTable (simpleIndex 1) 0) =
      conjugatorTable (simpleIndex 1) (candidate o i k l 0) →
    candidate o i k l (conjugatorTable (simpleIndex 1) 1) =
      conjugatorTable (simpleIndex 1) (candidate o i k l 1) →
    (∀ x : Fin 100, (candidate o i k l ^ 3) x = x) ∨
      ∃ j : Fin 4, ∀ x : Fin 100, candidate o i k l x = conjugatorTable (fourIndex j) x := by
  cases o <;> apply allFin <;> decide +kernel

private theorem permutation_cases (e : Extension)
    (he : extensionAction e ∈ fixingSubgroup (MulAut Carrier) (representativeA5 : Set Carrier)) :
    e ^ 3 = 1 ∨ ∃ j : Fin 4, e.val = conjugatorTable (fourIndex j) := by
  obtain ⟨o, i, hi⟩ := extension_cover e
  have hc (j : Fin 60) : Commute (outerTable o * normalForm i)
      (conjugatorTable (simpleIndex j)) := hi ▸ commutes_of_fixes e he j
  obtain ⟨j, hj⟩ := candidate_cover o i hc
  have hpoint (x : Fin 100) :=
    congrArg (fun p : Equiv.Perm (Fin 100) => p x) (hc 1).eq
  rw [hj] at hpoint
  rcases final_filter o j i.2.2.1 i.2.2.2 (hpoint 0) (hpoint 1) with hcube | ⟨j, hj'⟩
  · left
    apply Subtype.ext
    change e.val ^ 3 = 1
    rw [hi, hj]
    exact Equiv.ext hcube
  · exact Or.inr ⟨j, hi.trans (hj.trans (Equiv.ext hj'))⟩

private theorem fixer_cases (f : MulAut Carrier)
    (hf : f ∈ fixingSubgroup (MulAut Carrier) (representativeA5 : Set Carrier)) :
    f ^ 3 = 1 ∨ ∃ j : Fin 4, f = MulAut.conj (conjugator (fourIndex j)) := by
  obtain ⟨e, rfl⟩ := action_surjective f
  rcases permutation_cases e hf with he | ⟨j, hj⟩
  · left
    rw [← map_pow, he, map_one]
  · right
    refine ⟨j, ?_⟩
    have hj' : e = intoExtension (conjugator (fourIndex j)) := by
      apply Subtype.ext
      change e.val = inclusion (conjugator (fourIndex j))
      rw [conjugator_inclusion]
      exact hj
    rw [hj', extensionAction_inner]

private theorem four_word_square (j : Fin 4) : conjugator (fourIndex j) ^ 2 = 1 := by
  have h : ∀ (j : Fin 4) (x : Fin 100), (conjugatorTable (fourIndex j) ^ 2) x = x := by
    apply allFin
    decide +kernel
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_pow, conjugator_inclusion, map_one]
  exact Equiv.ext (h j)

private theorem four_word_zero : conjugator (fourIndex 0) = 1 := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [conjugator_inclusion, map_one]
  apply Equiv.ext
  apply allFin
  decide +kernel

/-- Every two-subgroup of the actual pointwise A₅ fixer has order at most four
and exponent at most two. The full fixer is not a two-group. -/
theorem representativeA5_two_subgroup_bound (B : Subgroup (MulAut Carrier))
    (hB : B ≤ fixingSubgroup (MulAut Carrier) (representativeA5 : Set Carrier))
    (hp : IsPGroup 2 B) : Nat.card B ≤ 4 ∧ ∀ b : B, b ^ 2 = 1 := by
  classical
  have hcover (b : B) : ∃ j : Fin 4, (b : MulAut Carrier) =
      MulAut.conj (conjugator (fourIndex j)) := by
    rcases fixer_cases b (hB b.property) with hc | h
    · have hb3 : b ^ 3 = 1 := Subtype.ext hc
      have hb1 : b = 1 := orderOf_eq_one_iff.mp
        ((hp.orderOf_coprime (by decide : Nat.Coprime 2 3) b).eq_one_of_dvd
          (orderOf_dvd_of_pow_eq_one hb3))
      exact ⟨0, by rw [hb1, four_word_zero, map_one]; rfl⟩
    · exact h
  choose index hindex using hcover
  have hinj : Function.Injective index := by
    intro x y h
    apply Subtype.ext
    rw [hindex x, hindex y, h]
  refine ⟨?_, ?_⟩
  · simpa only [Nat.card_fin] using Nat.card_le_card_of_injective index hinj
  · intro b
    apply Subtype.ext
    change (b : MulAut Carrier) ^ 2 = 1
    rw [hindex b, ← map_pow, four_word_square, map_one]

end TwoSubgroupBound

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Janko
