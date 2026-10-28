module

public import ABG.Recognition.ThreeLinearClassCensus
public import Theory.GroupTheory.PGroup.OrderTwentySeven
public import Mathlib.GroupTheory.Exponent

/-!
# The two remaining classes in Wong's linear branch

The two remaining class sizes sum to 728. Each divides 5616/3, since its
representatives have nontrivial three-power order. These two facts already
force the sizes 104 and 624, and hence centralizer orders 54 and 9.
The transported GL₂(3) unipotent belongs to the first class: its centralizer
contains the distinguished involution. Elements of order divisible by nine
have odd centralizers, so they can only belong to the second class.
If that class had order nine, counting cubes would give six cube roots of
each order-three element in the ambient group. A nonabelian Sylow subgroup
of order 27 would supply nine roots, a contradiction. Thus both remaining
classes have order three and every Sylow-three subgroup has exponent three.

Source: W. J. Wong, “On finite groups whose 2-Sylow subgroups have cyclic
subgroups of index 2” (1964), Appendix (b), pp.108–109,
DOI 10.1017/S1446788700022771.
-/

namespace ABG.ThreeGlobalDegreeData
open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

variable {G : Type*} [Group G] [Finite G] (c : ThreeGlobalDegreeData G)

/-- The actual GL₂(3) unipotent, transported into the distinguished centralizer. -/
public def linearUnipotent : Subgroup.centralizer ({c.involution} : Set G) :=
  (threeCentralizerEquiv c.involution c.centralizerEquiv).symm
    (Matrix.GeneralLinearGroup.threeClassRepr 3)

/-- The transported unipotent agrees with the specified matrix representative. -/
public theorem linearUnipotent_eq : c.linearUnipotent =
    (threeCentralizerEquiv c.involution c.centralizerEquiv).symm
      (Matrix.GeneralLinearGroup.threeClassRepr 3) := by rfl

public theorem linearUnipotent_order : orderOf (c.linearUnipotent : G) = 3 := by
  exact threeCentralizer_class_representative_order c.involution c.centralizerEquiv 3

variable [IsSimpleGroup G] (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (hG : Nat.card G = 5616)

include c S hS hG

private theorem remaining_class_card_dvd (k : ConjClasses G)
    (hk : k ∈ c.remainingThreeClasses) : Nat.card k.carrier ∣ 1872 := by
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective k
  have ho := c.remainingThreeClasses_order S hS hG x hk
  have h3 : 3 ∣ orderOf x := by rcases ho with h | h | h <;> simp [h]
  have hd := (Subgroup.centralizer ({x} : Set G)).orderOf_dvd_natCard
    (Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl x).eq)
  obtain ⟨d, hd⟩ := h3.trans hd
  have hp := ConjClasses.nat_card_carrier_mul_card_centralizer x
  rw [hG, hd] at hp
  exact ⟨d, by nlinarith [hp]⟩

/-- Class-size arithmetic determines the two possibilities before excluding nine. -/
public theorem linear_remaining_class_card (k : ConjClasses G)
    (hk : k ∈ c.remainingThreeClasses) :
    Nat.card k.carrier = 104 ∨ Nat.card k.carrier = 624 := by
  classical
  obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp (c.card_remainingThreeClasses S hS hG)
  have hs := c.sum_remainingThreeClasses_card S hS hG
  rw [he, Finset.sum_pair hab] at hs
  have ha := remaining_class_card_dvd c S hS hG a (by rw [he]; simp)
  have hb := remaining_class_card_dvd c S hS hG b (by rw [he]; simp)
  have hnum : ∀ a ∈ Nat.divisors 1872, ∀ b ∈ Nat.divisors 1872,
      a + b = 728 → a = 104 ∨ a = 624 := by
    set_option maxRecDepth 10000 in decide
  rw [he, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl
  · exact hnum _ (Nat.mem_divisors.mpr ⟨ha, by decide⟩)
      _ (Nat.mem_divisors.mpr ⟨hb, by decide⟩) hs
  · exact hnum _ (Nat.mem_divisors.mpr ⟨hb, by decide⟩)
      _ (Nat.mem_divisors.mpr ⟨ha, by decide⟩) (by omega)

/-- Centralizer orders of all nonidentity three-elements. -/
public theorem linear_three_centralizer_options (x : G)
    (hx : orderOf x = 3 ∨ orderOf x = 9 ∨ orderOf x = 27) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) = 54 ∨
      Nat.card (Subgroup.centralizer ({x} : Set G)) = 9 := by
  have hs := c.linear_remaining_class_card S hS hG (ConjClasses.mk x)
    ((c.mk_mem_remainingThreeClasses_iff_order S hS hG x).mpr hx)
  have hp := ConjClasses.nat_card_carrier_mul_card_centralizer x
  rw [hG] at hp
  rcases hs with hs | hs <;> rw [hs] at hp <;> omega

omit hG in
/-- An element whose order is divisible by nine cannot centralize an involution. -/
public theorem linear_nine_dvd_centralizer_odd (x : G) (hx : 9 ∣ orderOf x) :
    ¬ 2 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  intro he
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card'
    (G := Subgroup.centralizer ({x} : Set G)) 2 he
  have htG : orderOf (t : G) = 2 := (Subgroup.orderOf_coe t).trans ht
  have hm : x ∈ Subgroup.centralizer ({(t : G)} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp t.property).symm
  have hd := (Subgroup.centralizer ({(t : G)} : Set G)).orderOf_dvd_natCard hm
  have hc := c.even_centralizer_card S hS (t : G) (by rw [htG])
  simp only [htG, ↓reduceIte] at hc
  rw [hc] at hd
  have := hx.trans hd
  norm_num at this

/-- Order 27 is already excluded by the centralizer possibilities. -/
public theorem linear_no_order_twenty_seven (x : G) : orderOf x ≠ 27 := by
  intro hx
  have ho := c.linear_nine_dvd_centralizer_odd S hS x (by rw [hx]; decide)
  have hc := c.linear_three_centralizer_options S hS hG x (Or.inr (Or.inr hx))
  have hd := (Subgroup.centralizer ({x} : Set G)).orderOf_dvd_natCard
    (Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl x).eq)
  rcases hc with hc | hc
  · exact ho (by rw [hc]; decide)
  · rw [hx, hc] at hd
    norm_num at hd

/-- The unipotent belongs to the class with centralizer order 54. -/
public theorem linearUnipotent_centralizer_card :
    Nat.card (Subgroup.centralizer ({(c.linearUnipotent : G)} : Set G)) = 54 := by
  have hc := c.linear_three_centralizer_options S hS hG (c.linearUnipotent : G)
    (Or.inl c.linearUnipotent_order)
  have hm : c.involution ∈ Subgroup.centralizer ({(c.linearUnipotent : G)} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp c.linearUnipotent.property).symm
  have hd := (Subgroup.centralizer ({(c.linearUnipotent : G)} : Set G)).orderOf_dvd_natCard hm
  rw [c.order_involution] at hd
  rcases hc with hc | hc
  · exact hc
  · rw [hc] at hd
    norm_num at hd

public theorem linearUnipotent_class_card :
    Nat.card (ConjClasses.mk (c.linearUnipotent : G)).carrier = 104 := by
  have hp := ConjClasses.nat_card_carrier_mul_card_centralizer (c.linearUnipotent : G)
  rw [c.linearUnipotent_centralizer_card S hS hG, hG] at hp
  omega

/-- The second remaining class has an actual representative, of order three
or nine. Its centralizer has order nine. -/
public theorem linear_remaining_representative :
    ∃ b : G, (orderOf b = 3 ∨ orderOf b = 9) ∧
      ¬ IsConj (c.linearUnipotent : G) b ∧
      c.remainingThreeClasses = {ConjClasses.mk (c.linearUnipotent : G), ConjClasses.mk b} ∧
      Nat.card (ConjClasses.mk b).carrier = 624 ∧
      Nat.card (Subgroup.centralizer ({b} : Set G)) = 9 := by
  classical
  let u := ConjClasses.mk (c.linearUnipotent : G)
  have hu : u ∈ c.remainingThreeClasses :=
    (c.mk_mem_remainingThreeClasses_iff_order S hS hG _).mpr (Or.inl c.linearUnipotent_order)
  have hecard : (c.remainingThreeClasses.erase u).card = 1 := by
    rw [Finset.card_erase_of_mem hu, c.card_remainingThreeClasses S hS hG]
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hecard
  have he : c.remainingThreeClasses = {u, k} := by
    rw [← Finset.insert_erase hu, hk]
  have hne : u ≠ k := by
    have : k ∈ c.remainingThreeClasses.erase u := by rw [hk]; simp
    exact (Finset.mem_erase.mp this).1.symm
  obtain ⟨b, rfl⟩ := ConjClasses.mk_surjective k
  have hb := c.remainingThreeClasses_order S hS hG b (by rw [he]; simp)
  have hb27 := c.linear_no_order_twenty_seven S hS hG b
  have hs := c.sum_remainingThreeClasses_card S hS hG
  rw [he, Finset.sum_pair hne] at hs
  have hu104 : Nat.card u.carrier = 104 := c.linearUnipotent_class_card S hS hG
  have hb624 : Nat.card (ConjClasses.mk b).carrier = 624 := by omega
  have hp := ConjClasses.nat_card_carrier_mul_card_centralizer b
  rw [hb624, hG] at hp
  exact ⟨b, by omega, fun h => hne (ConjClasses.mk_eq_mk_iff_isConj.mpr h),
    he, hb624, by omega⟩

/-- Among the remaining classes, the class of the transported unipotent is
exactly the class with centralizer order 54. -/
public theorem linear_isConj_unipotent_iff (x : G)
    (hx : orderOf x = 3 ∨ orderOf x = 9 ∨ orderOf x = 27) :
    IsConj (c.linearUnipotent : G) x ↔
      Nat.card (Subgroup.centralizer ({x} : Set G)) = 54 := by
  classical
  obtain ⟨b, _, _, he, hb, _⟩ := c.linear_remaining_representative S hS hG
  have hm := (c.mk_mem_remainingThreeClasses_iff_order S hS hG x).mpr hx
  rw [he, Finset.mem_insert, Finset.mem_singleton] at hm
  have hp := ConjClasses.nat_card_carrier_mul_card_centralizer x
  rw [hG] at hp
  constructor
  · intro h
    have hc := ConjClasses.mk_eq_mk_iff_isConj.mpr h
    rw [← hc, c.linearUnipotent_class_card S hS hG] at hp
    omega
  · intro hc
    rcases hm with hm | hm
    · exact ConjClasses.mk_eq_mk_iff_isConj.mp hm.symm
    · rw [hm, hb, hc] at hp
      omega

/-- Every Sylow-three subgroup is nonabelian, even before excluding order nine. -/
public theorem linear_sylow_three_nonabelian (P : Sylow 3 G) :
    ¬ IsMulCommutative P := by
  intro hP
  obtain ⟨b, hb, _, _, _, hc⟩ := c.linear_remaining_representative S hS hG
  have hbpow : IsPGroup 3 (Subgroup.zpowers b) := by
    rcases hb with hb | hb
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb]; norm_num)
    · exact IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hb]; norm_num)
  obtain ⟨Q, hQ⟩ := hbpow.exists_le_sylow
  have hmul (x y : Q) : x * y = y * x := by
    apply (P.equiv Q).symm.injective
    simp only [map_mul]
    exact isMulCommutative_iff.mp hP _ _
  have hbQ : b ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers b)
  have hle : (Q : Subgroup G) ≤ Subgroup.centralizer ({b} : Set G) := by
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hmul (⟨x, hx⟩ : Q) (⟨b, hbQ⟩ : Q)))
  have hd := Subgroup.card_dvd_of_le hle
  rw [threeLinear_sylow_three_card hG Q, hc] at hd
  norm_num at hd

omit c S hS hG [IsSimpleGroup G] [Finite G] in
private theorem conj_order_eq {x y : G} (h : ConjClasses.mk x = ConjClasses.mk y) :
    orderOf x = orderOf y := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp h)
  rw [← hg]
  exact ((MulAut.conj g).orderOf_eq x).symm

/-- A hypothetical element of order nine has centralizer order nine. -/
public theorem linear_order_nine_centralizer_card (a : G) (ha : orderOf a = 9) :
    Nat.card (Subgroup.centralizer ({a} : Set G)) = 9 := by
  have hc := c.linear_three_centralizer_options S hS hG a (Or.inr (Or.inl ha))
  have ho := c.linear_nine_dvd_centralizer_odd S hS a (by rw [ha])
  rcases hc with hc | hc
  · exact (ho (by rw [hc]; decide)).elim
  · exact hc

/-- If order nine occurs, each of orders three and nine has just one class. -/
public theorem linear_nine_class_census (a : G) (ha : orderOf a = 9) :
    ConjClasses.ofOrder G 3 = {ConjClasses.mk (c.linearUnipotent : G)} ∧
      ConjClasses.ofOrder G 9 = {ConjClasses.mk a} := by
  classical
  obtain ⟨b, _, _, he, _, _⟩ := c.linear_remaining_representative S hS hG
  have haMem := (c.mk_mem_remainingThreeClasses_iff_order S hS hG a).mpr
    (Or.inr (Or.inl ha))
  rw [he, Finset.mem_insert, Finset.mem_singleton] at haMem
  have hab : ConjClasses.mk a = ConjClasses.mk b := by
    rcases haMem with h | h
    · have ho := conj_order_eq h
      rw [ha, c.linearUnipotent_order] at ho
      omega
    · exact h
  have hb : orderOf b = 9 := (conj_order_eq hab).symm.trans ha
  constructor
  · ext k
    obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective k
    rw [ConjClasses.mk_mem_ofOrder, Finset.mem_singleton]
    constructor
    · intro hx
      have hm := (c.mk_mem_remainingThreeClasses_iff_order S hS hG x).mpr (Or.inl hx)
      rw [he, Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | hm
      · exact hm
      · have ho := conj_order_eq hm
        omega
    · intro hx
      exact (conj_order_eq hx).trans c.linearUnipotent_order
  · ext k
    obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective k
    rw [ConjClasses.mk_mem_ofOrder, Finset.mem_singleton]
    constructor
    · intro hx
      have hm := (c.mk_mem_remainingThreeClasses_iff_order S hS hG x).mpr
        (Or.inr (Or.inl hx))
      rw [he, Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | hm
      · have ho := conj_order_eq hm
        rw [hx, c.linearUnipotent_order] at ho
        omega
      · exact hm.trans hab.symm
    · intro hx
      exact (conj_order_eq hx).trans ha

/-- Under the order-nine hypothesis, there are 104 elements of order three
and 624 elements of order nine. -/
public theorem linear_nine_element_counts (a : G) (ha : orderOf a = 9) :
    Nat.card {x : G // orderOf x = 3} = 104 ∧
      Nat.card {x : G // orderOf x = 9} = 624 := by
  classical
  obtain ⟨h3, h9⟩ := c.linear_nine_class_census S hS hG a ha
  have hp := ConjClasses.nat_card_carrier_mul_card_centralizer a
  rw [c.linear_order_nine_centralizer_card S hS hG a ha, hG] at hp
  rw [← ConjClasses.sum_card_ofOrder 3, ← ConjClasses.sum_card_ofOrder 9, h3, h9,
    Finset.sum_singleton, Finset.sum_singleton, c.linearUnipotent_class_card S hS hG]
  exact ⟨rfl, by omega⟩

omit c S hS hG [IsSimpleGroup G] in
private theorem cube_order_nine {x z : G} (hz : orderOf z = 3) (hx : x ^ 3 = z) :
    orderOf x = 9 := by
  have hp : x ^ 9 = 1 := by
    calc
      x ^ 9 = (x ^ 3) ^ 3 := by rw [← pow_mul]
      _ = 1 := by rw [hx, ← hz]; exact pow_orderOf_eq_one z
  have hd := orderOf_dvd_of_pow_eq_one hp
  have hm : orderOf x ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  have hdiv : Nat.divisors 9 = {1,3,9} := by decide
  rw [hdiv] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  have ho : orderOf (x ^ 3) = 3 := hx ▸ hz
  rw [orderOf_pow] at ho
  rcases hm with hm | hm | hm
  · norm_num [hm] at ho
  · norm_num [hm] at ho
  · exact hm

/-- Counting the cube map gives exactly six roots of each order-three
element, if order nine occurs. This is the global half of Wong's contradiction. -/
public theorem linear_cube_fiber_card_of_order_nine (a : G) (ha : orderOf a = 9)
    (z : G) (hz : orderOf z = 3) : Nat.card {x : G // x ^ 3 = z} = 6 := by
  classical
  obtain ⟨h3, h9⟩ := c.linear_nine_element_counts S hS hG a ha
  have hc := (c.linear_nine_class_census S hS hG a ha).1
  have heq (y : G) (hy : orderOf y = 3) :
      Nat.card {x : G // x ^ 3 = y} = Nat.card {x : G // x ^ 3 = z} := by
    have hclass (w : G) (hw : orderOf w = 3) :
        ConjClasses.mk w = ConjClasses.mk (c.linearUnipotent : G) := by
      have hm := (ConjClasses.mk_mem_ofOrder 3 w).mpr hw
      rw [hc, Finset.mem_singleton] at hm
      exact hm
    obtain ⟨g, hg⟩ := isConj_iff.mp
      (ConjClasses.mk_eq_mk_iff_isConj.mp ((hclass y hy).trans (hclass z hz).symm))
    let e := MulAut.conj g
    have heg : e y = z := hg
    apply Nat.card_congr
    apply Equiv.subtypeEquiv e.toEquiv
    intro x
    change x ^ 3 = y ↔ e x ^ 3 = z
    rw [← map_pow, ← heg]
    exact e.injective.eq_iff.symm
  let f : {x : G // orderOf x = 9} → {y : G // orderOf y = 3} := fun x =>
    ⟨x.val ^ 3, by rw [orderOf_pow, x.property]; norm_num⟩
  have hf (y : {y : G // orderOf y = 3}) :
      Nat.card {x // f x = y} = Nat.card {x : G // x ^ 3 = z} := by
    calc
      Nat.card {x // f x = y} = Nat.card {x : G // x ^ 3 = y.val} := by
        apply Nat.card_congr
        exact
          { toFun := fun x => ⟨x.val.val, congrArg Subtype.val x.property⟩
            invFun := fun x => ⟨⟨x.val, cube_order_nine y.property x.property⟩,
              Subtype.ext x.property⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
      _ = Nat.card {x : G // x ^ 3 = z} := heq y.val y.property
  have hs := Nat.card_congr (Equiv.sigmaFiberEquiv f)
  rw [Nat.card_sigma] at hs
  simp only [hf, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, h3, h9] at hs
  omega

/-- The global six-root count contradicts the nine roots inside a Sylow subgroup. -/
public theorem linear_no_order_nine (a : G) : orderOf a ≠ 9 := by
  intro ha
  have hp : IsPGroup 3 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, ha]; norm_num)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  let b : (P : Subgroup G) := ⟨a, hP (Subgroup.mem_zpowers a)⟩
  have hb : orderOf b = 9 := (Subgroup.orderOf_coe b).symm.trans ha
  have hlocal := OrderTwentySeven.cube_fiber_card_of_order_nine
    (threeLinear_sylow_three_card hG P) (c.linear_sylow_three_nonabelian S hS hG P) b hb
  have hcube : orderOf (a ^ 3) = 3 := by rw [orderOf_pow, ha]; norm_num
  have hglobal := c.linear_cube_fiber_card_of_order_nine S hS hG a ha (a ^ 3) hcube
  let f : {x : (P : Subgroup G) // x ^ 3 = b ^ 3} → {x : G // x ^ 3 = a ^ 3} :=
    fun x => ⟨x.val.val, congrArg Subtype.val x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z => z.val) h))
  have hle := Nat.card_le_card_of_injective f hf
  rw [hlocal, hglobal] at hle
  omega

/-- The second remaining class consists of elements of order three. -/
public theorem linear_order_three_representative :
    ∃ b : G, orderOf b = 3 ∧
      ¬ IsConj (c.linearUnipotent : G) b ∧
      c.remainingThreeClasses = {ConjClasses.mk (c.linearUnipotent : G), ConjClasses.mk b} ∧
      Nat.card (ConjClasses.mk b).carrier = 624 ∧
      Nat.card (Subgroup.centralizer ({b} : Set G)) = 9 := by
  obtain ⟨b, hb, hne, he, hcard, hc⟩ := c.linear_remaining_representative S hS hG
  exact ⟨b, hb.resolve_right (c.linear_no_order_nine S hS hG b), hne, he, hcard, hc⟩

/-- The two remaining classes are precisely the order-three classes. -/
public theorem remainingThreeClasses_eq_ofOrder_three :
    c.remainingThreeClasses = ConjClasses.ofOrder G 3 := by
  ext k
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective k
  rw [c.mk_mem_remainingThreeClasses_iff_order S hS hG, ConjClasses.mk_mem_ofOrder]
  simp [c.linear_no_order_nine S hS hG x, c.linear_no_order_twenty_seven S hS hG x]

/-- The full order-three census, with the size-104 representative fixed by GL₂(3). -/
public theorem linear_order_three_class_census :
    ∃ b : G, orderOf b = 3 ∧
      ¬ IsConj (c.linearUnipotent : G) b ∧
      ConjClasses.ofOrder G 3 =
        {ConjClasses.mk (c.linearUnipotent : G), ConjClasses.mk b} ∧
      Nat.card (ConjClasses.mk (c.linearUnipotent : G)).carrier = 104 ∧
      Nat.card (Subgroup.centralizer ({(c.linearUnipotent : G)} : Set G)) = 54 ∧
      Nat.card (ConjClasses.mk b).carrier = 624 ∧
      Nat.card (Subgroup.centralizer ({b} : Set G)) = 9 := by
  obtain ⟨b, hb, hne, he, hcard, hc⟩ := c.linear_order_three_representative S hS hG
  rw [c.remainingThreeClasses_eq_ofOrder_three S hS hG] at he
  exact ⟨b, hb, hne, he, c.linearUnipotent_class_card S hS hG,
    c.linearUnipotent_centralizer_card S hS hG, hcard, hc⟩

/-- All element orders in the linear branch. -/
public theorem linear_element_order_coverage (x : G) :
    orderOf x ∈ ({1, 2, 3, 4, 6, 8, 13} : Finset ℕ) := by
  by_cases hx : x = 1
  · simp [hx]
  by_cases he : 2 ∣ orderOf x
  · have ho := c.sixth_even_order_values S hS x he
    rcases ho with ⟨ho, _⟩ | ⟨ho, _⟩ | ⟨ho, _⟩ | ⟨ho, _⟩ <;> simp [ho]
  by_cases h13 : orderOf x = 13
  · simp [h13]
  have hm := (c.mk_mem_remainingThreeClasses_iff S hS x).mpr ⟨⟨hx, he⟩, h13⟩
  rw [c.remainingThreeClasses_eq_ofOrder_three S hS hG,
    ConjClasses.mk_mem_ofOrder] at hm
  simp [hm]

/-- Every element of a Sylow-three subgroup has cube one. -/
public theorem linear_sylow_three_cube (P : Sylow 3 G) (x : (P : Subgroup G)) :
    x ^ 3 = 1 := by
  have hd : orderOf (x : G) ∣ 27 := by
    simpa only [Subgroup.orderOf_coe, threeLinear_sylow_three_card hG P] using
      orderOf_dvd_natCard x
  have ho := c.linear_element_order_coverage S hS hG (x : G)
  simp only [Finset.mem_insert, Finset.mem_singleton] at ho
  have horder : orderOf (x : G) = 1 ∨ orderOf (x : G) = 3 := by
    rcases ho with h | h | h | h | h | h | h <;> simp_all
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [← Subgroup.orderOf_coe]
  rcases horder with h | h <;> simp [h]

/-- Every Sylow-three subgroup has exponent exactly three. -/
public theorem linear_sylow_three_exponent (P : Sylow 3 G) : Monoid.exponent P = 3 := by
  apply Nat.dvd_antisymm
  · exact Monoid.exponent_dvd_of_forall_pow_eq_one (c.linear_sylow_three_cube S hS hG P)
  · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 3
      (by rw [threeLinear_sylow_three_card hG P]; decide)
    simpa only [hx] using Monoid.order_dvd_exponent x

end
end ABG.ThreeGlobalDegreeData
