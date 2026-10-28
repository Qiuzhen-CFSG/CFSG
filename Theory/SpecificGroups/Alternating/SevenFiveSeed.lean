module

public import Theory.SpecificGroups.Alternating.SevenFivePlacement
public import Theory.Alternating.theorem_5_2_1_2
public import Theory.ElementaryAbelian.Join

/-!
# A five-letter seed through the four-point Klein group in A₇

The Klein four on the first four letters is Sylow in the alternating
pointwise fixer of the last two letters. A three-cycle on the complementary
triple centralizes this four-group. Together with the five-letter subgroup
it gives all star three-cycles, hence generates A₇.

Source: Aschbacher–Smith C.1.24, printed pp.130–131, the exceptional A₇
four-space seed. These are statements about the actual permutation groups.
-/

public section
open Subgroup Equiv
namespace Theory.SpecificGroups.Alternating.SevenFiveSeed
abbrev A7 := alternatingGroup (Fin 7)
private def x : A7 := ⟨swap 0 1 * swap 2 3, by change Perm.sign _ = 1; decide⟩
private def y : A7 := ⟨swap 0 2 * swap 1 3, by change Perm.sign _ = 1; decide⟩
private def entry : Fin 4 → A7 := ![1,x,y,x*y]

def four : Subgroup A7 where
  carrier := Set.range entry
  one_mem' := ⟨0,rfl⟩
  mul_mem' := by
    rintro _ _ ⟨i,rfl⟩ ⟨j,rfl⟩
    exact (by decide +kernel : ∀ i j : Fin 4, ∃ k, entry k = entry i * entry j) i j
  inv_mem' := by
    rintro _ ⟨i,rfl⟩
    exact (by decide +kernel : ∀ i : Fin 4, ∃ j, entry j = (entry i)⁻¹) i

def five : Subgroup A7 := fixingSubgroup A7 ({5,6} : Set (Fin 7))
def cubic : A7 := ⟨swap 4 5 * swap 4 6, by change Perm.sign _ = 1; decide⟩

theorem five_eq_fixing : five = fixingSubgroup A7 ({5,6} : Set (Fin 7)) := by rfl

theorem four_card : Nat.card four = 4 := by
  change Nat.card (Set.range entry) = 4
  rw [Nat.card_congr (Equiv.ofInjective entry (by decide +kernel)).symm]
  exact Nat.card_fin 4

theorem four_elementary : IsElementaryAbelian 2 four := by
  have hsq (a : four) : a ^ 2 = 1 := by
    obtain ⟨a, i, rfl⟩ := a
    exact Subtype.ext ((by decide +kernel : ∀ i : Fin 4, entry i ^ 2 = 1) i)
  have hi (a : four) : a⁻¹ = a := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using hsq a
  exact {
    toIsMulCommutative := ⟨⟨fun a b => by
      calc a*b = (a*b)⁻¹ := (hi _).symm
           _ = b⁻¹*a⁻¹ := mul_inv_rev _ _
           _ = b*a := by rw [hi,hi]⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsq }

theorem four_le_five : four ≤ five := by
  rintro _ ⟨i,rfl⟩ j
  have hj : j.val = 5 ∨ j.val = 6 := j.property
  rcases hj with hj | hj <;> change (entry i).val j.val = j.val <;> rw [hj]
  · exact (by decide +kernel : ∀ i : Fin 4, (entry i).val 5 = 5) i
  · exact (by decide +kernel : ∀ i : Fin 4, (entry i).val 6 = 6) i

noncomputable def fiveEquiv : five ≃* alternatingGroup (Fin 5) := by
  classical
  have hs : five = fixingSubgroup A7
      (({5,6} : Finset (Fin 7)) : Set (Fin 7)) := by
    simp only [five, Finset.coe_insert, Finset.coe_singleton]
  have hc : Fintype.card (↑(({5,6} : Finset (Fin 7))ᶜ)) = 5 := by decide
  exact (MulEquiv.subgroupCongr hs).trans
    ((Atlas.Families.Alternating.stabilizerComplementEquiv {5,6}).trans
      (Atlas.Families.Alternating.relabel (Fintype.equivFinOfCardEq hc)))

theorem five_card : Nat.card five = 60 := by
  rw [Nat.card_congr fiveEquiv.toEquiv,nat_card_alternatingGroup]
  norm_num [Nat.factorial]

noncomputable def fourSylow : Sylow 2 five := Sylow.ofCard (four.subgroupOf five) (by
  rw [Nat.card_congr (subgroupOfEquivOfLe four_le_five).toEquiv,four_card,five_card]
  decide +kernel)

theorem fourSylow_map : (fourSylow : Subgroup five).map five.subtype = four :=
  map_subgroupOf_eq_of_le four_le_five

theorem cubic_threeCycle : (cubic : Perm (Fin 7)).IsThreeCycle :=
  Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

theorem cubic_centralizes_four : cubic ∈ centralizer (four : Set A7) := by
  rintro _ ⟨i,rfl⟩
  exact (by decide +kernel : ∀ i : Fin 4, entry i * cubic = cubic * entry i) i

private def t : A7 := ⟨swap 0 1 * swap 5 6, by change Perm.sign _ = 1; decide⟩
private def sylowEntry : Fin 8 → A7 := ![1,x,y,x*y,t,x*t,y*t,x*y*t]
private def sylowGroup : Subgroup A7 where
  carrier := Set.range sylowEntry
  one_mem' := ⟨0,rfl⟩
  mul_mem' := by
    rintro _ _ ⟨i,rfl⟩ ⟨j,rfl⟩
    exact (by decide +kernel : ∀ i j : Fin 8, ∃ k,
      sylowEntry k = sylowEntry i * sylowEntry j) i j
  inv_mem' := by
    rintro _ ⟨i,rfl⟩
    exact (by decide +kernel : ∀ i : Fin 8, ∃ j,
      sylowEntry j = (sylowEntry i)⁻¹) i

private theorem sylowGroup_card : Nat.card sylowGroup = 8 := by
  change Nat.card (Set.range sylowEntry) = 8
  rw [Nat.card_congr (Equiv.ofInjective sylowEntry (by decide +kernel)).symm]
  exact Nat.card_fin 8

noncomputable def sylow : Sylow 2 A7 := Sylow.ofCard sylowGroup (by
  rw [sylowGroup_card,nat_card_alternatingGroup,Nat.card_fin]
  decide +kernel)

theorem four_le_sylow : four ≤ sylow := by
  rintro _ ⟨i,rfl⟩
  exact (by decide +kernel : ∀ i : Fin 4, ∃ j : Fin 8, sylowEntry j = entry i) i

theorem sylow_normalizes_five : (sylow : Subgroup A7) ≤ normalizer (five : Set A7) := by
  have hpres (i : Fin 8) (j : Fin 7) (hj : j = 5 ∨ j = 6) :
      (sylowEntry i).val j = 5 ∨ (sylowEntry i).val j = 6 :=
    (by decide +kernel : ∀ (i : Fin 8) (j : Fin 7), j = 5 ∨ j = 6 →
      (sylowEntry i).val j = 5 ∨ (sylowEntry i).val j = 6) i j hj
  have hconj (a : A7) (ha : a ∈ sylowGroup) (b : A7) (hb : b ∈ five) :
      a⁻¹*b*a ∈ five := by
    obtain ⟨i,rfl⟩ := ha
    intro j
    have hj : j.val = 5 ∨ j.val = 6 := j.property
    have hb' := hb ⟨(sylowEntry i).val j.val,hpres i j hj⟩
    change (sylowEntry i).val.symm (b.val ((sylowEntry i).val j.val)) = j.val
    change b.val ((sylowEntry i).val j.val) = (sylowEntry i).val j.val at hb'
    rw [hb',Equiv.symm_apply_apply]
  intro a ha
  rw [mem_normalizer_iff'']
  intro b
  constructor
  · exact hconj a ha b
  · intro hb
    have hh := hconj a⁻¹ (sylowGroup.inv_mem ha) (a⁻¹*b*a) hb
    simpa only [inv_inv,mul_assoc,mul_inv_cancel_left,inv_mul_cancel_right,mul_inv_cancel,mul_one] using hh

private def star (i : Fin 7) : A7 :=
  if h : i = 0 then 1 else
    ⟨swap 0 1 * swap 0 i, by
      rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap (by decide),
        Perm.sign_swap (Ne.symm h)]
      decide⟩

/-- The cubic on the three fixed letters and the five-letter group generate A₇. -/
theorem cubic_sup_five : zpowers cubic ⊔ five = ⊤ := by
  let H := zpowers cubic ⊔ five
  have hc : cubic ∈ H := (show zpowers cubic ≤ H from le_sup_left) (mem_zpowers cubic)
  have hstar (i : Fin 7) (hi : i = 2 ∨ i = 3 ∨ i = 4) : star i ∈ H := by
    apply (show five ≤ H from le_sup_right)
    intro j
    have hj : j.val = 5 ∨ j.val = 6 := j.property
    rcases hi with rfl | rfl | rfl <;> rcases hj with hj | hj <;>
      change (star _).val j.val = j.val <;> rw [hj] <;> decide
  have h4 := hstar 4 (Or.inr (Or.inr rfl))
  apply top_unique
  rw [← GLS3.Chapter5.starThreeCycles_closure_eq_top
    (a := (0 : Fin 7)) (b := 1) (by decide),closure_le]
  rintro g ⟨i,hi0,hi1,hg⟩
  have he : g = star i := by
    simp only [star, dif_neg hi0]
    exact Subtype.ext hg
  rw [he]
  fin_cases i
  · exact (hi0 rfl).elim
  · exact (hi1 rfl).elim
  · exact hstar 2 (Or.inl rfl)
  · exact hstar 3 (Or.inr (Or.inl rfl))
  · exact h4
  · have he : star 5 = cubic⁻¹ * star 4 * cubic := by decide +kernel
    change star 5 ∈ H
    rw [he]
    exact H.mul_mem (H.mul_mem (H.inv_mem hc) h4) hc
  · have he : star 6 = cubic * star 4 * cubic⁻¹ := by decide +kernel
    change star 6 ∈ H
    rw [he]
    exact H.mul_mem (H.mul_mem hc h4) (H.inv_mem hc)

theorem normalizer_sup_five : normalizer (four : Set A7) ⊔ five = ⊤ := by
  apply top_unique
  rw [← cubic_sup_five]
  exact sup_le_sup (zpowers_le.mpr (centralizer_le_normalizer _ cubic_centralizes_four)) le_rfl

/-- The five-letter subgroup genuinely moves the Klein four. -/
theorem five_not_le_normalizer : ¬ five ≤ normalizer (four : Set A7) := by
  intro h
  have ht : normalizer (four : Set A7) = ⊤ := by
    simpa only [sup_eq_left.mpr h] using normalizer_sup_five
  let : four.Normal := normalizer_eq_top_iff.mp ht
  let : IsSimpleGroup A7 := alternatingGroup.isSimpleGroup (by simp)
  rcases (inferInstance : four.Normal).eq_bot_or_eq_top with he | he
  · have hc := four_card
    rw [he,card_bot] at hc
    omega
  · have hc := four_card
    rw [he,card_top,nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial] at hc

end Theory.SpecificGroups.Alternating.SevenFiveSeed
