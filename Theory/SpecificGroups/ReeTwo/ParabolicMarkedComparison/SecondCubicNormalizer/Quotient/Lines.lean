module

public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.SecondCubicNormalizer.Quotient.Actors

/-!
# The three lines in the native cubic normalizer quotient

The twist and reflection classes and their product are exactly the three
nonidentity elements of the Klein four quotient. Their cyclic subgroups are
therefore the three distinct subgroups of order two. An actual subgroup of
order 48 containing the inner core maps to one of these lines.

Source: the native binary Ree endpoint calculation in Aschbacher–Smith
F.1.12/J.4.5.
-/

@[expose] public section
open Subgroup
namespace ReeTwo.SylowModel.CubicAction
noncomputable section

def quotientGenerator : Fin 3 → CubicNormalizerQuotient :=
  ![twistClass,inverterClass,twistClass*inverterClass]

theorem quotientGenerator_ne_one (i : Fin 3) : quotientGenerator i ≠ 1 := by
  fin_cases i
  · exact twistClass_ne_one
  · exact inverterClass_ne_one
  · intro h
    apply twistClass_ne_inverterClass
    have he := mul_eq_one_iff_eq_inv.mp h
    exact he.trans (IsKleinFour.inv_eq_self inverterClass)

theorem quotientGenerator_injective : Function.Injective quotientGenerator := by
  intro i j h
  have hti := twistClass_ne_inverterClass
  have ht := twistClass_ne_one
  have hi := inverterClass_ne_one
  fin_cases i <;> fin_cases j <;> simp_all [quotientGenerator]

theorem quotientGenerator_order (i : Fin 3) : orderOf (quotientGenerator i) = 2 :=
  orderOf_eq_prime (by simpa only [pow_two] using IsKleinFour.mul_self (quotientGenerator i))
    (quotientGenerator_ne_one i)

def quotientLine (i : Fin 3) : Subgroup CubicNormalizerQuotient := zpowers (quotientGenerator i)

theorem quotientLine_card (i : Fin 3) : Nat.card (quotientLine i) = 2 := by
  rw [quotientLine,Nat.card_zpowers,quotientGenerator_order]

theorem quotientLine_injective : Function.Injective quotientLine := by
  classical
  intro i j h
  have hm : quotientGenerator i ∈ quotientLine j := h ▸ (show quotientGenerator i ∈ quotientLine i from mem_zpowers _)
  change quotientGenerator i ∈ zpowers (quotientGenerator j) at hm
  rw [mem_zpowers_iff_mem_range_orderOf,quotientGenerator_order] at hm
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hm
  have hn2 : n < 2 := Finset.mem_range.mp hn
  interval_cases n
  · exact (quotientGenerator_ne_one i (by simpa using he.symm)).elim
  · exact quotientGenerator_injective (by simpa using he.symm)

theorem nonidentity_eq_quotientGenerator {x : CubicNormalizerQuotient} (hx : x ≠ 1) :
    ∃ i : Fin 3, x = quotientGenerator i := by
  by_cases ht : x = twistClass
  · exact ⟨0,ht⟩
  by_cases hi : x = inverterClass
  · exact ⟨1,hi⟩
  exact ⟨2,IsKleinFour.eq_mul_of_ne_all twistClass_ne_one inverterClass_ne_one
    twistClass_ne_inverterClass hx ht hi⟩

theorem quotientLine_exhaustive (L : Subgroup CubicNormalizerQuotient) (hL : Nat.card L = 2) :
    ∃ i : Fin 3, L = quotientLine i := by
  let : Nontrivial L := Finite.one_lt_card_iff_nontrivial.mp (by rw [hL]; decide)
  obtain ⟨x,hx⟩ := exists_ne (1 : L)
  have hx1 : (x : CubicNormalizerQuotient) ≠ 1 := fun h => hx (Subtype.ext h)
  obtain ⟨i,hi⟩ := nonidentity_eq_quotientGenerator hx1
  refine ⟨i,?_⟩
  symm
  apply eq_of_le_of_card_ge (zpowers_le.mpr (hi ▸ x.property))
  change Nat.card L ≤ Nat.card (quotientLine i)
  rw [hL,quotientLine_card]

theorem quotient_order_two_subgroups_card :
    Nat.card {L : Subgroup CubicNormalizerQuotient // Nat.card L = 2} = 3 := by
  let f : Fin 3 → {L : Subgroup CubicNormalizerQuotient // Nat.card L = 2} :=
    fun i => ⟨quotientLine i,quotientLine_card i⟩
  have hf : Function.Bijective f := ⟨fun i j h => quotientLine_injective (congrArg Subtype.val h),by
    rintro ⟨L,hL⟩
    obtain ⟨i,hi⟩ := quotientLine_exhaustive L hL
    exact ⟨i,Subtype.ext hi.symm⟩⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf),Nat.card_fin]

theorem order48_subgroup_quotient_line (H : Subgroup cubicNormalizer)
    (hK : innerCoreInNormalizer ≤ H) (hH : Nat.card H = 48) :
    ∃ i : Fin 3, H.map (QuotientGroup.mk' innerCoreInNormalizer) = quotientLine i := by
  apply quotientLine_exhaustive
  let q := QuotientGroup.mk' innerCoreInNormalizer
  have hk : q.ker ≤ H := by rw [QuotientGroup.ker_mk']; exact hK
  have hi : (H.map q).index = 2 := by
    rw [H.index_map_eq (f := q) (QuotientGroup.mk'_surjective _) hk]
    have hc := H.card_mul_index
    rw [hH,cubic_normalizer_card] at hc
    omega
  have hc := (H.map q).card_mul_index
  change Nat.card (H.map (QuotientGroup.mk' innerCoreInNormalizer)) * (H.map q).index =
    Nat.card CubicNormalizerQuotient at hc
  rw [hi,cubicNormalizerQuotient_card] at hc
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2) hc
end
end ReeTwo.SylowModel.CubicAction
