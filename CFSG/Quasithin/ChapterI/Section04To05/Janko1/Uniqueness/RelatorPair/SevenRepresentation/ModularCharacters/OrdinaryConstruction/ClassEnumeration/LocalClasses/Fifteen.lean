module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.ClassEnumeration.LocalClasses.PrimeClasses

/-!
# Two actual classes of order fifteen

Choose an element of order three in the distinguished involution centralizer.
Its transfer complement has order fifteen by the fixed-order centralizer theorem,
and hence is cyclic. A generator has ambient centralizer exactly that complement:
the only larger possibility has order thirty and would make the involution fix
the entire complement, contradicting its fixed subgroup of order three.

The Sylow five-normalizer has order sixty and its centralizer has order thirty.
Thus each normalizer element squares into the centralizer. Conjugation cannot
send an element of order five to its square, since applying it twice would give
fourth power equal to first power. Applying this to the cubes of a generator
and its square separates two actual ambient classes of order fifteen.

This constructs the literal `ClassBlock` consumed by the local class assembly.
The given involution-fusion premise is unnecessary for this construction.

Source: Janko, J. Algebra 3 (1966), 147–186; Gorenstein, *Finite Groups*,
§16.6, printed p.482. See `../../Source.md` for the source conventions.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.ClassEnumeration
open Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

private theorem generator_centralizer (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560) {x : G}
    (hxC : x ∈ centralizer ({h.z} : Set G)) (hx : orderOf x = 3)
    {A : Subgroup G} (a : OddCentralizerComplement h x A)
    (hA : Nat.card A = 15) {y : G} (hy : zpowers y = A) :
    centralizer ({y} : Set G) = A := by
  have hCy : centralizer ({y} : Set G) = centralizer (A : Set G) := by
    rw [← hy, zpowers_eq_closure, centralizer_closure]
  let : IsCyclic A := isCyclic_of_card_eq_fifteen hA
  have hAC : A ≤ centralizer ({y} : Set G) := hCy ▸ A.le_centralizer
  have hCC : centralizer ({y} : Set G) ≤ centralizer ({x} : Set G) := by
    rw [hCy]
    exact centralizer_le (Set.singleton_subset_iff.mpr a.x_mem)
  have h30 : Nat.card (centralizer ({x} : Set G)) = 30 := by
    simpa using (benderPrimeData_of_order h horder).centralizer_three x hx
  have hdiv := card_dvd_of_le hCC
  rw [h30] at hdiv
  have h15 := card_dvd_of_le hAC
  rw [hA] at h15
  have hcases : Nat.card (centralizer ({y} : Set G)) = 15 ∨
      Nat.card (centralizer ({y} : Set G)) = 30 := by
    have hbound := Nat.le_of_dvd (by decide : 0 < 30) hdiv
    obtain ⟨k, hk⟩ := h15
    have hp := Nat.card_pos (α := centralizer ({y} : Set G))
    omega
  rcases hcases with hc | hc
  · exact (eq_of_le_of_card_ge hAC (by rw [hA, hc])).symm
  · have he : centralizer ({y} : Set G) = centralizer ({x} : Set G) :=
      eq_of_le_of_card_ge hCC (by rw [hc, h30])
    have hz : h.z ∈ centralizer ({y} : Set G) := by
      rw [he]
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hxC).symm
    have hyz : y ∈ centralizer ({h.z} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hz).symm
    have hAZ : A ≤ centralizer ({h.z} : Set G) := by
      rw [← hy]
      exact zpowers_le.mpr hyz
    have hAx : A = zpowers x := by
      rw [← a.inf_centralizer_eq_zpowers h 3 (Or.inl rfl) hxC hx, inf_eq_left.mpr hAZ]
    have hc := congrArg (fun K : Subgroup G => Nat.card K) hAx
    rw [hA, Nat.card_zpowers, hx] at hc
    omega

private theorem exists_fifteen_generator (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560) :
    ∃ y : G, orderOf y = 15 ∧ Nat.card (centralizer ({y} : Set G)) = 15 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := centralizer ({h.z} : Set G)) 3 (by rw [h.centralizer_card]; decide)
  have hxG : orderOf (x : G) = 3 := (Subgroup.orderOf_coe x).trans hx
  obtain ⟨A, a⟩ := h.exists_oddCentralizerComplement 3 (Or.inl rfl) x x.property hxG
  have hA : Nat.card A = 15 := by
    have hc := a.centralizer_card
    rw [(benderPrimeData_of_order h horder).centralizer_three x hxG] at hc
    norm_num at hc
    omega
  let : IsCyclic A := isCyclic_of_card_eq_fifteen hA
  obtain ⟨y, hy⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic A)
  have hyG : orderOf (y : G) = 15 := (Subgroup.orderOf_coe y).trans (hy.trans hA)
  have he : zpowers (y : G) = A := eq_of_le_of_card_ge (zpowers_le.mpr y.property)
    (by rw [Nat.card_zpowers, hyG, hA])
  exact ⟨y, hyG, by rw [generator_centralizer h horder x.property hxG a hA he, hA]⟩

private theorem five_not_conj_square (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560) {a : G} (ha : orderOf a = 5) :
    ¬ IsConj a (a ^ 2) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have ha2 : orderOf (a ^ 2) = 5 := by rw [orderOf_pow, ha]; decide
  have hP : zpowers (a ^ 2) = zpowers a :=
    eq_of_le_of_card_ge (zpowers_le.mpr (npow_mem_zpowers a 2))
      (by rw [Nat.card_zpowers, Nat.card_zpowers, ha, ha2])
  let P : Sylow 5 G := Sylow.ofCard (zpowers a) (by
    rw [Nat.card_zpowers, ha, horder]
    decide +kernel)
  have hN : Nat.card (normalizer (zpowers a : Set G)) = 60 :=
    sylow_five_normalizer_card h horder P
  have hC : centralizer (zpowers a : Set G) = centralizer ({a} : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hc : Nat.card (centralizer (zpowers a : Set G)) = 30 := by
    rw [hC]
    simpa using (benderPrimeData_of_order h horder).centralizer_five a ha
  have hi : ((centralizer (zpowers a : Set G)).subgroupOf
      (normalizer (zpowers a : Set G))).index = 2 := by
    have he := ((centralizer (zpowers a : Set G)).subgroupOf
      (normalizer (zpowers a : Set G))).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe
      (centralizer_le_normalizer (zpowers a : Set G))).toEquiv, hc, hN] at he
    omega
  intro hconj
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hgN : g ∈ normalizer (zpowers a : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change zpowers (g * a * g⁻¹) = zpowers a
    rw [hg, hP]
  have hgC : g ^ 2 ∈ centralizer ({a} : Set G) := by
    rw [← hC]
    exact sq_mem_of_index_two hi (⟨g, hgN⟩ : normalizer (zpowers a : Set G))
  have he : a ^ 4 = a := by
    calc
      a ^ 4 = (a ^ 2) ^ 2 := pow_mul a 2 2
      _ = (MulAut.conj g) ((MulAut.conj g) a) := by
        rw [show (MulAut.conj g) a = a ^ 2 from hg, map_pow,
          show (MulAut.conj g) a = a ^ 2 from hg]
      _ = (g ^ 2) * a * (g ^ 2)⁻¹ := by
        simp only [MulAut.conj_apply, pow_two, mul_inv_rev, mul_assoc]
      _ = a := mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hgC)
  have he' : a ^ 4 = a ^ 1 := by simpa using he
  rw [pow_inj_mod, ha] at he'
  norm_num at he'

/-- Two actual order-fifteen classes, each with centralizer order fifteen. -/
public theorem fifteen_classes_nonempty (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560) : Nonempty (ClassBlock G 15 15 2) := by
  obtain ⟨y, hy, hc⟩ := exists_fifteen_generator h horder
  have hy2 : orderOf (y ^ 2) = 15 := by rw [orderOf_pow, hy]; decide
  have hP : zpowers (y ^ 2) = zpowers y :=
    eq_of_le_of_card_ge (zpowers_le.mpr (npow_mem_zpowers y 2))
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hy, hy2])
  have hc2 : Nat.card (centralizer ({y ^ 2} : Set G)) = 15 := by
    have he : centralizer ({y ^ 2} : Set G) = centralizer ({y} : Set G) := by
      rw [← centralizer_closure, ← zpowers_eq_closure, hP,
        zpowers_eq_closure, centralizer_closure]
    rw [he, hc]
  have hn : ConjClasses.mk y ≠ ConjClasses.mk (y ^ 2) := by
    intro he
    have he' := IsConj.pow 3 (ConjClasses.mk_eq_mk_iff_isConj.mp he)
    have horder5 : orderOf (y ^ 3) = 5 := by rw [orderOf_pow, hy]; decide
    apply five_not_conj_square h horder horder5
    simpa only [← pow_mul, show 2 * 3 = 3 * 2 from rfl] using he'
  refine ⟨⟨![y, y ^ 2], ?_, ?_, ?_⟩⟩
  · intro i
    fin_cases i <;> simp [hy, hy2]
  · intro i
    fin_cases i <;> simp [hc, hc2]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.ClassEnumeration
