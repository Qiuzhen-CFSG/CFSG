module
public import ABG.Recognition.ThreeMathieuCharacterCount
public import ABG.Recognition.ThreeMathieuEvenClasses
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.ClassEquation
public import Theory.GroupTheory.OddNormalizerInversion

/-!
# Odd-order classes in Wong's order-7920 branch

The eleven-centralizer is odd, and its automizer has order dividing ten.
The Sylow congruence therefore forces the eleven-normalizer to have order
55. Inversion cannot be induced by this odd-order normalizer. Together with
the five even classes and Cauchy's theorem, the ten-class count then exhausts
the conjugacy classes.

Source: Wong (1964), Theorem 6(a), p.107,
DOI 10.1017/S1446788700022771.
-/

open BenderGlauberman
open scoped BigOperators
namespace ABG
noncomputable section
variable {G : Type*} [Group G] [Finite G]

/-- Sylow eleven-subgroups in the order-7920 branch have prime order. -/
public theorem mathieu_sylow_eleven_card (hG : Nat.card G = 7920) (P : Sylow 11 G) :
    Nat.card P = 11 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  rw [Sylow.card_eq_multiplicity, hG]
  decide +kernel

/-- Sylow five-subgroups in the order-7920 branch have prime order. -/
public theorem mathieu_sylow_five_card (hG : Nat.card G = 7920) (P : Sylow 5 G) :
    Nat.card P = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [Sylow.card_eq_multiplicity, hG]
  decide +kernel

variable (c : ThreeGlobalDegreeData G) [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)

include c S hS in
/-- An element whose order does not divide 48 has odd centralizer. -/
public theorem ThreeGlobalDegreeData.odd_centralizer_card_of_not_dvd_48
    (x : G) (hx : ¬ orderOf x ∣ 48) :
    Odd (Nat.card (Subgroup.centralizer ({x} : Set G))) := by
  apply Nat.not_even_iff_odd.mp
  intro he
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card'
    (G := Subgroup.centralizer ({x} : Set G)) 2 (even_iff_two_dvd.mp he)
  have htG : orderOf (t : G) = 2 := (Subgroup.orderOf_coe t).trans ht
  have hxt : x ∈ Subgroup.centralizer ({(t : G)} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp t.property).symm
  have hd := orderOf_dvd_natCard (⟨x, hxt⟩ : Subgroup.centralizer ({(t : G)} : Set G))
  rw [← Subgroup.orderOf_coe, c.even_centralizer_card S hS t (htG ▸ dvd_rfl), htG] at hd
  norm_num at hd
  exact hx hd

set_option maxRecDepth 20000 in
include c S hS in
/-- The normalizer of a Sylow eleven-subgroup has order 55. -/
public theorem ThreeGlobalDegreeData.mathieu_sylow_eleven_normalizer_card
    (hG : Nat.card G = 7920) (P : Sylow 11 G) :
    Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) = 55 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hP := mathieu_sylow_eleven_card hG P
  let : IsCyclic P := isCyclic_of_prime_card hP
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 11 (by rw [hP])
  have hxG : orderOf (x : G) = 11 := (Subgroup.orderOf_coe x).trans hx
  have hodd : Odd (Nat.card (Subgroup.centralizer ((P : Subgroup G) : Set G))) := by
    apply Odd.of_dvd_nat (c.odd_centralizer_card_of_not_dvd_48 S hS (x : G) (by
      rw [hxG]; norm_num))
    exact Subgroup.card_dvd_of_le (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr x.property))
  have hAut : Nat.card (MulAut P) = 10 := by
    rw [IsCyclic.card_mulAut, hP]
    decide
  let f := (P : Subgroup G).normalizerMonoidHom
  have hrange : Nat.card f.range ∣ 10 := hAut ▸ f.range.card_subgroup_dvd_card
  have hker : Odd (Nat.card f.ker) := by
    rwa [Subgroup.normalizerMonoidHom_ker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Subgroup.centralizer_le_normalizer ((P : Subgroup G) : Set G))).toEquiv]
  have hprod := f.ker.card_mul_index
  rw [Subgroup.index_ker] at hprod
  have hfour : ¬ 4 ∣ Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) := by
    intro hd
    have hd' : 4 ∣ Nat.card f.range := by
      apply (hker.coprime_two_left.pow_left 2).dvd_of_dvd_mul_left
      simpa only [hprod, show 2 ^ 2 = 4 from rfl] using hd
    have := hd'.trans hrange
    norm_num at this
  have hd : Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) ∣ 7920 :=
    hG ▸ (Subgroup.normalizer ((P : Subgroup G) : Set G)).card_subgroup_dvd_card
  have hm := card_sylow_modEq_one 11 G
  have hind := Nat.eq_div_of_mul_eq_left (Nat.card_pos (α := Subgroup.normalizer ((P : Subgroup G) : Set G))).ne'
    ((Subgroup.normalizer ((P : Subgroup G) : Set G)).index_mul_card.trans hG)
  rw [P.card_eq_index_normalizer] at hm
  change (Subgroup.normalizer ((P : Subgroup G) : Set G)).index ≡ 1 [MOD 11] at hm
  rw [hind] at hm
  have hm' : (7920 / Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G))) % 11 = 1 := hm
  have hnum : ∀ n ∈ Nat.divisors 7920, ¬ 4 ∣ n → 7920 / n % 11 = 1 → n = 55 := by
    decide
  exact hnum _ (Nat.mem_divisors.mpr ⟨hd, by decide⟩) hfour hm'

include c S hS in
/-- The two inverse classes of order eleven are distinct. -/
public theorem ThreeGlobalDegreeData.mathieu_eleven_not_isConj_inv
    (hG : Nat.card G = 7920) (x : G) (hx : orderOf x = 11) :
    ¬ IsConj x x⁻¹ := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hp : IsPGroup 11 (Subgroup.zpowers x) := IsPGroup.of_card (n := 1) (by
    simpa only [Nat.card_zpowers, pow_one] using hx)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have heq : Subgroup.zpowers x = (P : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hP (by rw [mathieu_sylow_eleven_card hG, Nat.card_zpowers, hx])
  apply Subgroup.not_isConj_inv_of_odd_normalizer x
  · rw [heq, c.mathieu_sylow_eleven_normalizer_card S hS hG P]
    decide
  · intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hx] at hd
    norm_num at hd

omit [Finite G] [IsSimpleGroup G] in
private theorem conj_order_eq {x y : G} (h : IsConj x y) : orderOf x = orderOf y := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact (MulAut.conj g).orderOf_eq x |>.symm

include c S hS in
/-- Ten explicit representatives exhaust the conjugacy classes. Their orders
are 1,2,4,6,8,8,3,5,11,11. -/
public theorem ThreeGlobalDegreeData.exists_mathieu_class_representatives
    (hG : Nat.card G = 7920) :
    ∃ a b z : G, orderOf a = 3 ∧ orderOf b = 5 ∧ orderOf z = 11 ∧
      Function.Bijective (fun i : Fin 10 => ConjClasses.mk
        (![1, (c.evenRepresentative 0 : G), (c.evenRepresentative 1 : G),
          (c.evenRepresentative 2 : G), (c.evenRepresentative 3 : G),
          (c.evenRepresentative 4 : G), a, b, z, z⁻¹] i)) := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  let : Fintype (ConjClasses G) := Fintype.ofFinite _
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := G) 3 (by rw [hG]; norm_num)
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := G) 5 (by rw [hG]; norm_num)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := G) 11 (by rw [hG]; norm_num)
  let r : Fin 10 → G := ![1, (c.evenRepresentative 0 : G), (c.evenRepresentative 1 : G),
    (c.evenRepresentative 2 : G), (c.evenRepresentative 3 : G),
    (c.evenRepresentative 4 : G), a, b, z, z⁻¹]
  have hr (i : Fin 10) : orderOf (r i) = ![1,2,4,6,8,8,3,5,11,11] i := by
    fin_cases i <;> simp [r, c.evenRepresentative_order, ha, hb, hz]
  have hi : Function.Injective (fun i => ConjClasses.mk (r i)) := by
    intro i j hij
    have hc := ConjClasses.mk_eq_mk_iff_isConj.mp hij
    have ho := conj_order_eq hc
    rw [hr i, hr j] at ho
    fin_cases i <;> fin_cases j <;> norm_num at ho <;> try rfl
    · exact absurd (c.evenRepresentative_not_fused 3 4 hc) (by decide)
    · exact absurd (c.evenRepresentative_not_fused 4 3 hc) (by decide)
    · exact (c.mathieu_eleven_not_isConj_inv S hS hG z hz hc).elim
    · exact (c.mathieu_eleven_not_isConj_inv S hS hG z hz hc.symm).elim
  refine ⟨a, b, z, ha, hb, hz, (Fintype.bijective_iff_injective_and_card _).mpr ⟨hi, ?_⟩⟩
  rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, c.mathieu_class_count hG]

include c S hS in
/-- The complete element-order spectrum in the order-7920 branch. -/
public theorem ThreeGlobalDegreeData.mathieu_order_exhaustion
    (hG : Nat.card G = 7920) (x : G) :
    orderOf x ∈ ({1,2,3,4,5,6,8,11} : Finset ℕ) := by
  obtain ⟨a, b, z, ha, hb, hz, hr⟩ := c.exists_mathieu_class_representatives S hS hG
  obtain ⟨i, hi⟩ := hr.surjective (ConjClasses.mk x)
  have ho := conj_order_eq (ConjClasses.mk_eq_mk_iff_isConj.mp hi)
  fin_cases i <;> simp [c.evenRepresentative_order, ha, hb, hz] at ho <;> simp [← ho]

include c S hS in
/-- There is one class each of orders three and five, and two of order eleven. -/
public theorem ThreeGlobalDegreeData.mathieu_odd_class_counts
    (hG : Nat.card G = 7920) :
    HasElementConjugacyClassCount G 3 1 ∧ HasElementConjugacyClassCount G 5 1 ∧
      HasElementConjugacyClassCount G 11 2 := by
  obtain ⟨a, b, z, ha, hb, hz, hr⟩ := c.exists_mathieu_class_representatives S hS hG
  let r : Fin 10 → G := ![1, (c.evenRepresentative 0 : G), (c.evenRepresentative 1 : G),
    (c.evenRepresentative 2 : G), (c.evenRepresentative 3 : G),
    (c.evenRepresentative 4 : G), a, b, z, z⁻¹]
  have hcov (x : G) : ∃ i, IsConj x (r i) := by
    obtain ⟨i, hi⟩ := hr.surjective (ConjClasses.mk x)
    exact ⟨i, (ConjClasses.mk_eq_mk_iff_isConj.mp hi).symm⟩
  have h3 (x : G) (hx : orderOf x = 3) : IsConj x a := by
    obtain ⟨i, hi⟩ := hcov x
    have ho := conj_order_eq hi
    rw [hx] at ho
    fin_cases i <;> simp [r, c.evenRepresentative_order, ha, hb, hz] at ho
    exact hi
  have h5 (x : G) (hx : orderOf x = 5) : IsConj x b := by
    obtain ⟨i, hi⟩ := hcov x
    have ho := conj_order_eq hi
    rw [hx] at ho
    fin_cases i <;> simp [r, c.evenRepresentative_order, ha, hb, hz] at ho
    exact hi
  have h11 (x : G) (hx : orderOf x = 11) : IsConj x z ∨ IsConj x z⁻¹ := by
    obtain ⟨i, hi⟩ := hcov x
    have ho := conj_order_eq hi
    rw [hx] at ho
    fin_cases i <;> simp [r, c.evenRepresentative_order, ha, hb, hz] at ho
    · exact Or.inl hi
    · exact Or.inr hi
  refine ⟨⟨fun _ => a, fun _ => ha, fun _ _ _ => Subsingleton.elim _ _,
    fun x hx => ⟨0, h3 x hx⟩⟩,
    ⟨fun _ => b, fun _ => hb, fun _ _ _ => Subsingleton.elim _ _,
      fun x hx => ⟨0, h5 x hx⟩⟩,
    ⟨![z,z⁻¹], ?_, ?_, ?_⟩⟩
  · intro i
    fin_cases i <;> simp [hz]
  · intro i j hij
    have hn := c.mathieu_eleven_not_isConj_inv S hS hG z hz
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hn hij).elim
    · exact (hn hij.symm).elim
    · rfl
  · intro x hx
    rcases h11 x hx with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩

include c S hS in
private theorem centralizer_prime_exclusion (hG : Nat.card G = 7920)
    (x : G) (p : ℕ) [Fact p.Prime] (hc : (orderOf x).Coprime p)
    (he : orderOf x * p ∉ ({1,2,3,4,5,6,8,11} : Finset ℕ)) :
    ¬ p ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  intro hd
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card'
    (G := Subgroup.centralizer ({x} : Set G)) p hd
  have hyG : orderOf (y : G) = p := (Subgroup.orderOf_coe y).trans hy
  have hcomm : Commute x (y : G) :=
    (Subgroup.mem_centralizer_singleton_iff.mp y.property).symm
  have ho : orderOf (x * (y : G)) = orderOf x * p := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (hyG ▸ hc), hyG]
  exact he (ho ▸ c.mathieu_order_exhaustion S hS hG (x * (y : G)))

set_option maxRecDepth 20000 in
include c S hS in
private theorem mathieu_prime_centralizer_card (hG : Nat.card G = 7920)
    (x : G) (m : ℕ) (hm : m = 5 ∨ m = 11) (hx : orderOf x = m) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) = m := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  let C := Subgroup.centralizer ({x} : Set G)
  have hd : Nat.card C ∣ 7920 := hG ▸ C.card_subgroup_dvd_card
  have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hmC : m ∣ Nat.card C := by
    have h := orderOf_dvd_natCard (⟨x, hxC⟩ : C)
    rwa [← Subgroup.orderOf_coe, hx] at h
  have h2 : ¬ 2 ∣ Nat.card C := centralizer_prime_exclusion c S hS hG x 2
    (by rcases hm with rfl | rfl <;> rw [hx] <;> decide)
    (by rcases hm with rfl | rfl <;> rw [hx] <;> decide)
  have h3 : ¬ 3 ∣ Nat.card C := centralizer_prime_exclusion c S hS hG x 3
    (by rcases hm with rfl | rfl <;> rw [hx] <;> decide)
    (by rcases hm with rfl | rfl <;> rw [hx] <;> decide)
  rcases hm with rfl | rfl
  · have h11 : ¬ 11 ∣ Nat.card C := centralizer_prime_exclusion c S hS hG x 11
      (by rw [hx]; decide) (by rw [hx]; decide)
    have hnum : ∀ n ∈ Nat.divisors 7920,
        5 ∣ n → ¬ 2 ∣ n → ¬ 3 ∣ n → ¬ 11 ∣ n → n = 5 := by decide
    exact hnum _ (Nat.mem_divisors.mpr ⟨hd, by decide⟩) hmC h2 h3 h11
  · have h5 : ¬ 5 ∣ Nat.card C := centralizer_prime_exclusion c S hS hG x 5
      (by rw [hx]; decide) (by rw [hx]; decide)
    have hnum : ∀ n ∈ Nat.divisors 7920,
        11 ∣ n → ¬ 2 ∣ n → ¬ 3 ∣ n → ¬ 5 ∣ n → n = 11 := by decide
    exact hnum _ (Nat.mem_divisors.mpr ⟨hd, by decide⟩) hmC h2 h3 h5

include c S hS in
/-- An element of order five has centralizer order five. -/
public theorem ThreeGlobalDegreeData.mathieu_five_centralizer_card
    (hG : Nat.card G = 7920) (x : G) (hx : orderOf x = 5) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) = 5 :=
  mathieu_prime_centralizer_card c S hS hG x 5 (Or.inl rfl) hx

include c S hS in
/-- An element of order eleven has centralizer order eleven. -/
public theorem ThreeGlobalDegreeData.mathieu_eleven_centralizer_card
    (hG : Nat.card G = 7920) (x : G) (hx : orderOf x = 11) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) = 11 :=
  mathieu_prime_centralizer_card c S hS hG x 11 (Or.inr rfl) hx

omit [Finite G] [IsSimpleGroup G] in
private theorem isConj_of_class_count_one {m : ℕ} (h : HasElementConjugacyClassCount G m 1)
    (x y : G) (hx : orderOf x = m) (hy : orderOf y = m) : IsConj x y := by
  obtain ⟨r, _, _, hcov⟩ := h
  obtain ⟨i, hi⟩ := hcov x hx
  obtain ⟨j, hj⟩ := hcov y hy
  exact hi.trans ((Subsingleton.elim i j) ▸ hj.symm)

omit [IsSimpleGroup G] in
private theorem class_size_mul_centralizer (x : G) :
    Nat.card (ConjClasses.mk x).carrier * Nat.card (Subgroup.centralizer ({x} : Set G)) =
      Nat.card G := by
  have he : Nat.card {y : G // y * x = x * y} =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun _ => Subgroup.mem_centralizer_singleton_iff.symm)
  rw [← he]
  exact class_card_mul_centralizer_card x

include c S hS in
/-- The remaining class-equation term gives centralizer order eighteen for
an element of order three. -/
public theorem ThreeGlobalDegreeData.mathieu_three_centralizer_card
    (hG : Nat.card G = 7920) (x : G) (hx : orderOf x = 3) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) = 18 := by
  classical
  let : Fintype (ConjClasses G) := Fintype.ofFinite _
  obtain ⟨a, b, z, ha, hb, hz, hr⟩ := c.exists_mathieu_class_representatives S hS hG
  let r : Fin 10 → G := ![1, (c.evenRepresentative 0 : G), (c.evenRepresentative 1 : G),
    (c.evenRepresentative 2 : G), (c.evenRepresentative 3 : G),
    (c.evenRepresentative 4 : G), a, b, z, z⁻¹]
  have hsum : ∑ i : Fin 10, Nat.card (ConjClasses.mk (r i)).carrier = 7920 := by
    have h := Group.sum_card_conj_classes_eq_card G
    rw [finsum_eq_sum_of_fintype] at h
    change ∑ d : ConjClasses G, Nat.card d.carrier = Nat.card G at h
    rw [← hG, ← h]
    exact Fintype.sum_equiv (Equiv.ofBijective (fun i => ConjClasses.mk (r i)) hr)
      _ _ (fun _ => rfl)
  have hsize (y : G) (n : ℕ) (hn : Nat.card (Subgroup.centralizer ({y} : Set G)) = n)
      (hne : n ≠ 0) : Nat.card (ConjClasses.mk y).carrier = 7920 / n := by
    apply Nat.eq_div_of_mul_eq_left hne
    rw [← hn, class_size_mul_centralizer, hG]
  have hone : Nat.card (ConjClasses.mk (1 : G)).carrier = 1 := by
    have he : (ConjClasses.mk (1 : G)).carrier = {1} := by
      ext y
      change IsConj 1 y ↔ y = 1
      exact isConj_one_right
    rw [he]
    simp
  have heven (i : Fin 5) : Nat.card (ConjClasses.mk (c.evenRepresentative i : G)).carrier =
      ![165,990,1320,990,990] i := by
    rw [hsize _ _ (c.evenRepresentative_centralizer_card i) (by fin_cases i <;> decide)]
    fin_cases i <;> rfl
  have hbsize := hsize b 5 (c.mathieu_five_centralizer_card S hS hG b hb) (by decide)
  have hzsize := hsize z 11 (c.mathieu_eleven_centralizer_card S hS hG z hz) (by decide)
  have hzisize := hsize z⁻¹ 11 (c.mathieu_eleven_centralizer_card S hS hG z⁻¹
    (by simpa using hz)) (by decide)
  simp only [r, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, add_zero] at hsum
  rw [hone, heven 0, heven 1, heven 2, heven 3, heven 4, hbsize, hzsize, hzisize] at hsum
  have hasize : Nat.card (ConjClasses.mk a).carrier = 440 := by
    change 1 + (165 + (990 + (1320 + (990 + (990 + (Nat.card (ConjClasses.mk a).carrier + (1584 + (720 + (720))))))))) = 7920 at hsum
    omega
  have hxa := isConj_of_class_count_one (c.mathieu_odd_class_counts S hS hG).1 x a hx ha
  have hxc := class_size_mul_centralizer x
  rw [ConjClasses.mk_eq_mk_iff_isConj.mpr hxa, hasize, hG] at hxc
  omega

include c S hS in
/-- A Sylow five-subgroup is its own centralizer. -/
public theorem ThreeGlobalDegreeData.mathieu_sylow_five_self_centralizing
    (hG : Nat.card G = 7920) (P : Sylow 5 G) :
    Subgroup.centralizer ((P : Subgroup G) : Set G) = (P : Subgroup G) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hP := mathieu_sylow_five_card hG P
  let : IsCyclic P := isCyclic_of_prime_card hP
  have hle : (P : Subgroup G) ≤ Subgroup.centralizer ((P : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 5 (by rw [hP])
  have hxG : orderOf (x : G) = 5 := (Subgroup.orderOf_coe x).trans hx
  apply (Subgroup.eq_of_le_of_card_ge hle _).symm
  calc
    _ ≤ Nat.card (Subgroup.centralizer ({(x : G)} : Set G)) :=
      Subgroup.card_le_of_le (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr x.property))
    _ = 5 := c.mathieu_five_centralizer_card S hS hG x hxG
    _ = _ := hP.symm

include c S hS in
/-- Any two nonidentity elements of a Sylow five-subgroup are conjugate in G. -/
public theorem ThreeGlobalDegreeData.mathieu_sylow_five_nonidentity_isConj
    (hG : Nat.card G = 7920) (P : Sylow 5 G) (x y : P) (hx : x ≠ 1) (hy : y ≠ 1) :
    IsConj (x : G) (y : G) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have ho (z : P) (hz : z ≠ 1) : orderOf (z : G) = 5 := by
    rw [Subgroup.orderOf_coe]
    apply orderOf_eq_prime _ hz
    have hc : Nat.card P = 5 := mathieu_sylow_five_card hG P
    have hp := pow_card_eq_one' (x := z)
    change z ^ Nat.card P = 1 at hp
    rw [hc] at hp
    exact hp
  exact isConj_of_class_count_one (c.mathieu_odd_class_counts S hS hG).2.1
    x y (ho x hx) (ho y hy)

include c S hS in
/-- Conjugacy of the four generators realizes all four automorphisms of a
Sylow five-subgroup, so its normalizer has order twenty. -/
public theorem ThreeGlobalDegreeData.mathieu_sylow_five_normalizer_card
    (hG : Nat.card G = 7920) (P : Sylow 5 G) :
    Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G)) = 20 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hP := mathieu_sylow_five_card hG P
  let : IsCyclic P := isCyclic_of_prime_card hP
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 5 (by rw [hP])
  have hxne : x ≠ 1 := by intro h; simp [h] at hx
  have hgen (y : P) (hy : orderOf y = 5) : Subgroup.zpowers (y : G) = (P : Subgroup G) := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr y.property)
    rw [hP, Nat.card_zpowers, Subgroup.orderOf_coe, hy]
  let f := (P : Subgroup G).normalizerMonoidHom
  have hsurj : Function.Surjective f := by
    intro φ
    have hφne : φ x ≠ 1 := by simpa using hxne
    obtain ⟨g, hg⟩ := isConj_iff.mp
      (c.mathieu_sylow_five_nonidentity_isConj S hS hG P x (φ x) hxne hφne)
    have hgn : g ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← hgen x hx, MonoidHom.map_zpowers]
      change Subgroup.zpowers (g * (x : G) * g⁻¹) = Subgroup.zpowers (x : G)
      rw [hg, hgen (φ x) ((φ.orderOf_eq x).trans hx), hgen x hx]
    refine ⟨⟨g, hgn⟩, ?_⟩
    have he : f ⟨g, hgn⟩ x = φ x := Subtype.ext hg
    apply MulEquiv.ext
    intro y
    obtain ⟨k, rfl⟩ := mem_zpowers_of_prime_card hP hxne (g' := y)
    simp only [map_zpow, he]
  have hker : Nat.card f.ker = 5 := by
    rw [Subgroup.normalizerMonoidHom_ker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Subgroup.centralizer_le_normalizer ((P : Subgroup G) : Set G))).toEquiv,
      c.mathieu_sylow_five_self_centralizing S hS hG P, hP]
  have hrange : Nat.card f.range = 4 := by
    rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, IsCyclic.card_mulAut, hP]
    decide
  have hprod := f.ker.card_mul_index
  rw [Subgroup.index_ker, hker, hrange] at hprod
  exact hprod.symm

end
end ABG
