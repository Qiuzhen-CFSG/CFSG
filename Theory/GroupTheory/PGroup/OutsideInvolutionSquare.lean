module

public import Theory.GroupTheory.PGroup.RankTwoNormalFour
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators
public import Theory.GroupTheory.PGroup.ClassTwoCyclicCenter
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Tactic.Group

/-!
# Outside involutions and the cyclic four-center of an order-sixteen core

An involution outside an index-two subgroup must move any different core
four-group when the ambient normal four is unique. If it inverts a central
square root and swaps involutions x and y with (xy)² equal to that square,
then xyr is an involution fixed by the outside involution. It generates a
centralizing four with the central involution, contradicting elementary rank
two. The calculation uses actual conjugation identities. In a core of order
sixteen with cyclic center of order four, the central quotient is elementary
of order four. Noncommuting involutions therefore multiply to a square root
of the unique central involution. Applying the calculation shows that the
outside involution fixes the cyclic center; index two makes that center central
in the entire group.

Source: the outside-core argument in Janko–Thompson, Math. Z. 113 (1970),
Lemma 4.1, printed p.393. These lemmas are intrinsic finite-group statements.
-/

namespace Subgroup
open Subgroup

/-- Swapped involutions and an inverted square root force an elementary eight. -/
public theorem false_of_inverting_root_of_swapped_involutions {P : Type*} [Group P] [Finite P]
    (hrank : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A < 8)
    (H : Subgroup P) (z r x y t : P)
    (hz : orderOf z = 2) (hzc : z ∈ center P)
    (hr : r ∈ H) (hxH : x ∈ H) (hyH : y ∈ H) (htH : t ∉ H)
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (ht : t ^ 2 = 1)
    (hrx : Commute r x) (hry : Commute r y)
    (hrz : r ^ 2 = z) (hxy : (x * y) ^ 2 = z)
    (htx : t * x * t⁻¹ = y) (hty : t * y * t⁻¹ = x)
    (htr : t * r * t⁻¹ = r⁻¹) : False := by
  let w := x * y * r
  have hz2 : z ^ 2 = 1 := by simpa only [hz] using pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by intro h; simp [h] at hz
  have hw2 : w ^ 2 = 1 := by
    rw [(hrx.mul_right hry).symm.mul_pow, hxy, hrz, ← pow_two, hz2]
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hx)
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hy)
  have hwt : Commute t w := by
    have he : t * w * t⁻¹ = w⁻¹ := by
      calc
        _ = (t * x * t⁻¹) * (t * y * t⁻¹) * (t * r * t⁻¹) := by dsimp [w]; group
        _ = y * x * r⁻¹ := by rw [htx, hty, htr]
        _ = (x * y * r)⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, hxinv, hyinv,
            (hry.mul_right hrx).symm.inv_right.eq]
    have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hw2)
    rw [hwi] at he
    exact (mul_inv_eq_iff_eq_mul.mp he)
  have hxn : ¬ Commute x w := by
    intro hw
    have hc : Commute x (x * y) := by
      have hh := hw.mul_right hrx.symm.inv_right
      simpa only [w, mul_inv_cancel_right] using hh
    have hcomm : Commute x y :=
      mul_left_cancel (by simpa only [mul_assoc] using hc.eq)
    apply hz1
    rw [← hxy, hcomm.mul_pow, hx, hy, one_mul]
  have hw1 : w ≠ 1 := fun h => hxn (h ▸ Commute.one_right x)
  have hwz : z ≠ w := fun h => hxn (h ▸ (mem_center_iff.mp hzc x))
  let F := closure ({z, w} : Set P)
  let : IsKleinFour F := isKleinFour_closure_pair_of_orderOf z w hz
    (orderOf_eq_prime hw2 hw1) hwz (mem_center_iff.mp hzc w).symm
  let : IsElementaryAbelian 2 F :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  have hFH : F ≤ H := by
    apply (closure_le _).mpr
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · rw [← hrz]; exact H.pow_mem hr 2
    · have : a = w := Set.mem_singleton_iff.mp ha
      rw [this]
      exact H.mul_mem (H.mul_mem hxH hyH) hr
  have htF : t ∈ centralizer (F : Set P) := by
    apply (le_centralizer_iff.mp ?_) (mem_zpowers t)
    apply (closure_le _).mpr
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact center_le_centralizer _ hzc
    · have : a = w := Set.mem_singleton_iff.mp ha
      rw [this]
      intro b hb
      obtain ⟨n, rfl⟩ := hb
      exact (hwt.zpow_left n).eq
  exact htH (hFH (mem_four_of_square_eq_one_of_elementary_card_lt_eight hrank F
    (IsKleinFour.card_four (G := F)) ht htF))

/-- A core four different from the unique ambient normal four is moved by an outside element. -/
public theorem not_commute_conj_of_unique_normal_four {P : Type*} [Group P] [Finite P]
    (hrank : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A < 8)
    (H E : Subgroup P) (hindex : H.index = 2)
    (hunique : ∀ F : Subgroup P, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = E)
    (z x t : P) (hzE : z ∈ E) (hz : orderOf z = 2) (hzc : z ∈ center P)
    (hx : x ^ 2 = 1) (hxE : x ∉ E) (htH : t ∉ H)
    (hnorm : H ≤ normalizer (closure ({z, x} : Set P) : Set P)) :
    ¬ Commute x (t * x * t⁻¹) := by
  intro hcomm
  let F := closure ({z, x} : Set P)
  have hx1 : x ≠ 1 := fun h => hxE (h ▸ E.one_mem)
  have hzx : z ≠ x := fun h => hxE (h ▸ hzE)
  let : IsKleinFour F := isKleinFour_closure_pair_of_orderOf z x hz
    (orderOf_eq_prime hx hx1) hzx (mem_center_iff.mp hzc x).symm
  let : IsElementaryAbelian 2 F :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by simp }
  have hyF : t * x * t⁻¹ ∈ F := by
    apply mem_four_of_square_eq_one_of_elementary_card_lt_eight hrank F
      (IsKleinFour.card_four (G := F))
    · have hh := congrArg (MulAut.conj t) hx
      simpa only [map_pow, map_one, MulAut.conj_apply] using hh
    · apply (le_centralizer_iff.mp ?_) (mem_zpowers (t * x * t⁻¹))
      apply (closure_le _).mpr
      intro a ha
      rcases Set.mem_insert_iff.mp ha with rfl | ha
      · exact center_le_centralizer _ hzc
      · have : a = x := Set.mem_singleton_iff.mp ha
        rw [this]
        intro b hb
        obtain ⟨n, rfl⟩ := hb
        exact (hcomm.zpow_right n).symm.eq
  have htN : t ∈ normalizer (F : Set P) := by
    rw [mem_normalizer_iff_map_conj_eq]
    apply eq_of_le_of_card_ge
    · apply map_le_iff_le_comap.mpr
      apply (closure_le _).mpr
      intro a ha
      change t * a * t⁻¹ ∈ F
      rcases Set.mem_insert_iff.mp ha with rfl | ha
      · rw [(show Commute t _ from mem_center_iff.mp hzc t).mul_inv_cancel]
        exact subset_closure (by simp)
      · have : a = x := Set.mem_singleton_iff.mp ha
        rw [this]
        exact hyF
    · rw [card_map_of_injective (MulAut.conj t).injective]
  have hFn : F.Normal := by
    apply normalizer_eq_top_iff.mp
    apply eq_top_iff.mpr
    intro g _
    by_cases hg : g ∈ H
    · exact hnorm hg
    · have hgt : g * t ∈ H := (mul_mem_iff_of_index_two hindex).mpr (by simp [hg, htH])
      have hh := (normalizer (F : Set P)).mul_mem (hnorm hgt)
        ((normalizer (F : Set P)).inv_mem htN)
      simpa only [mul_inv_cancel_right] using hh
  have hFE : F = E := hunique F hFn inferInstance (IsKleinFour.card_four (G := F))
  exact hxE (hFE ▸ subset_closure (by simp : x ∈ ({z, x} : Set P)))

open scoped commutatorElement

private theorem pair_square {Q : Type*} [Group Q] [Finite Q] [IsCyclic (center Q)]
    (hcard : Nat.card Q = 16) (hZ : Nat.card (center Q) = 4)
    (z : Q) (hz : orderOf z = 2) (hzc : z ∈ center Q)
    (x y : Q) (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hxy : ¬ Commute x y) :
    (x * y) ^ 2 = z := by
  have hq : Nat.card (Q ⧸ center Q) = 2 ^ 2 := by
    have hh := (center Q).card_mul_index
    rw [hZ, hcard, index_eq_card] at hh
    omega
  have hnc : ¬ IsCyclic (Q ⧸ center Q) := by
    intro hc
    let := hc
    let : IsMulCommutative Q := isMulCommutative_of_isCyclic_quotient_center_self Q
    have hh : center Q = ⊤ := center_eq_top
    rw [hh, Nat.card_congr Subgroup.topEquiv.toEquiv, hcard] at hZ
    omega
  have hquot : IsElementaryAbelian 2 (Q ⧸ center Q) :=
    { toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq hq
      exponent_dvd_p := by rw [(not_isCyclic_iff_exponent_eq_prime Nat.prime_two hq).mp hnc] }
  have hcZ : ⁅x, y⁆ ∈ center Q := hquot.commutator_le_center_of_central_quotient
    (commutator_mem_commutator (mem_top x) (mem_top y))
  have hc2 := hquot.commutatorElement_sq_eq_one_of_central_quotient x y
  have hc1 : ⁅x, y⁆ ≠ 1 := fun h => hxy (commutatorElement_eq_one_iff_commute.mp h)
  have hc : ⁅x, y⁆ = z := congrArg Subtype.val
    (IsCyclic.eq_of_orderOf_eq_two (x := (⟨⁅x, y⁆, hcZ⟩ : center Q))
      (y := ⟨z, hzc⟩) (by simpa using orderOf_eq_prime hc2 hc1) (by simpa using hz))
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hx)
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hy)
  simpa only [commutatorElement_def, hxi, hyi, pow_two, mul_assoc] using hc

private theorem root_exists {Q : Type*} [Group Q] [Finite Q] [IsCyclic (center Q)]
    (hZ : Nat.card (center Q) = 4) (z : Q) (hz : orderOf z = 2) (hzc : z ∈ center Q) :
    ∃ r : Q, r ∈ center Q ∧ orderOf r = 4 ∧ r ^ 2 = z := by
  obtain ⟨r, hr⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := center Q)
  rw [hZ] at hr
  refine ⟨r, r.property, (Subgroup.orderOf_coe r).trans hr, ?_⟩
  have hr2 : orderOf (r ^ 2) = 2 := by rw [orderOf_pow, hr]; norm_num
  exact congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two (x := r ^ 2)
    (y := ⟨z, hzc⟩) hr2 (by simpa using hz))

private theorem root_conj_cases {P : Type*} [Group P] [Finite P]
    (H : Subgroup P) [H.Normal] (hZ : Nat.card (center H) = 4)
    (r : H) (hrc : r ∈ center H) (hr : orderOf r = 4) (t : P) :
    t * (r : P) * t⁻¹ = r ∨ t * (r : P) * t⁻¹ = (r : P)⁻¹ := by
  classical
  let R : center H := ⟨r, hrc⟩
  let a := centerCongr (MulAut.conjNormal t : MulAut H)
  have hR : orderOf R = 4 := (Subgroup.orderOf_coe R).symm.trans hr
  have hg : zpowers R = ⊤ := (zpowers R).eq_top_of_card_eq (by rw [Nat.card_zpowers, hR, hZ])
  have ha : a R ∈ zpowers R := hg ▸ mem_top _
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp ha)
  have hn4 : n < 4 := by simpa only [Finset.mem_range, hR] using hn
  have har : orderOf (a R) = 4 := (a.orderOf_eq R).trans hR
  have hp : R ^ 3 = R⁻¹ := eq_inv_of_mul_eq_one_left (by
    rw [← pow_succ]
    simpa only [hR] using pow_orderOf_eq_one R)
  have hc : a R = R ∨ a R = R⁻¹ := by
    interval_cases n
    · simp only [pow_zero] at he
      rw [← he, orderOf_one] at har
      omega
    · exact Or.inl (by simpa only [pow_one] using he.symm)
    · rw [← he, orderOf_pow, hR] at har
      norm_num at har
    · exact Or.inr (he.symm.trans hp)
  rcases hc with hc | hc
  · left
    exact congrArg (fun q : center H => ((q : H) : P)) hc
  · right
    exact congrArg (fun q : center H => ((q : H) : P)) hc

private theorem exists_noncommuting_conjugate {P : Type*} [Group P] [Finite P]
    (hrank : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A < 8)
    (H E F : Subgroup P) [IsElementaryAbelian 2 F]
    (hindex : H.index = 2) (hE : Nat.card E = 4) (hF : Nat.card F = 4)
    (hFH : F ≤ H) (hnorm : H ≤ normalizer (F : Set P)) (hFE : F ≠ E)
    (hunique : ∀ U : Subgroup P, U.Normal → IsElementaryAbelian 2 U → Nat.card U = 4 → U = E)
    (z t : P) (hzE : z ∈ E) (hz : orderOf z = 2) (hzc : z ∈ center P)
    (htH : t ∉ H) :
    ∃ x : P, x ∈ H ∧ x ^ 2 = 1 ∧ ¬ Commute x (t * x * t⁻¹) := by
  have hnot : ¬ F ≤ E := fun h => hFE (eq_of_le_of_card_ge h (by omega))
  obtain ⟨x, hxF, hxE⟩ := SetLike.not_le_iff_exists.mp hnot
  have hx2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := F) x hxF
  have hz2 : z ^ 2 = 1 := by simpa only [hz] using pow_orderOf_eq_one z
  have hzF := mem_four_of_square_eq_one_of_elementary_card_lt_eight hrank F hF hz2
    (center_le_centralizer _ hzc)
  have hx1 : x ≠ 1 := fun h => hxE (h ▸ E.one_mem)
  have hzx : z ≠ x := fun h => hxE (h ▸ hzE)
  let : IsKleinFour (closure ({z, x} : Set P)) := isKleinFour_closure_pair_of_orderOf z x hz
    (orderOf_eq_prime hx2 hx1) hzx (mem_center_iff.mp hzc x).symm
  have heq : closure ({z, x} : Set P) = F := by
    apply eq_of_le_of_card_ge
    · apply (closure_le _).mpr
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl <;> assumption
    · rw [hF, IsKleinFour.card_four (G := closure ({z, x} : Set P))]
  exact ⟨x, hFH hxF, hx2,
    not_commute_conj_of_unique_normal_four hrank H E hindex hunique z x t hzE hz hzc
      hx2 hxE htH (heq.symm ▸ hnorm)⟩

/-- An outside involution forces a central square root when an order-sixteen
core with cyclic four-center has a second core-normal elementary four. -/
public theorem exists_central_square_of_order_sixteen_core {P : Type*} [Group P] [Finite P]
    (hrank : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A < 8)
    (H E F : Subgroup P) [H.Normal] [IsCyclic (center H)] [IsElementaryAbelian 2 F]
    (hcard : Nat.card H = 16) (hcenter : Nat.card (center H) = 4)
    (hindex : H.index = 2) (hE : Nat.card E = 4) (hF : Nat.card F = 4)
    (hEH : E ≤ H) (hFH : F ≤ H) (hnorm : H ≤ normalizer (F : Set P)) (hFE : F ≠ E)
    (hunique : ∀ U : Subgroup P, U.Normal → IsElementaryAbelian 2 U → Nat.card U = 4 → U = E)
    (z t : P) (hzE : z ∈ E) (hz : orderOf z = 2) (hzc : z ∈ center P)
    (ht : t ^ 2 = 1) (htH : t ∉ H) :
    ∃ r : P, r ∈ center P ∧ r ^ 2 = z := by
  let Z : H := ⟨z, hEH hzE⟩
  have hZc : Z ∈ center H := mem_center_iff.mpr (fun h => Subtype.ext (mem_center_iff.mp hzc h))
  have hZo : orderOf Z = 2 := (Subgroup.orderOf_coe Z).symm.trans hz
  obtain ⟨r, hrc, hro, hrz⟩ := root_exists hcenter Z hZo hZc
  obtain ⟨x, hxH, hx2, hxmove⟩ := exists_noncommuting_conjugate hrank H E F hindex hE hF
    hFH hnorm hFE hunique z t hzE hz hzc htH
  let y := t * x * t⁻¹
  have hyH : y ∈ H := (inferInstance : H.Normal).conj_mem x hxH t
  have hy2 : y ^ 2 = 1 := by
    have hh := congrArg (MulAut.conj t) hx2
    simpa only [map_pow, map_one, MulAut.conj_apply] using hh
  have hxy : (x * y) ^ 2 = z := congrArg Subtype.val
    (pair_square hcard hcenter Z hZo hZc ⟨x, hxH⟩ ⟨y, hyH⟩
      (Subtype.ext hx2) (Subtype.ext hy2) (fun h => hxmove (congrArg Subtype.val h)))
  have hty : t * y * t⁻¹ = x := by
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ht)
    have htt : t * t = 1 := by simpa [pow_two] using ht
    dsimp [y]
    rw [hti]
    calc
      t * (t * x * t) * t = (t * t) * x * (t * t) := by group
      _ = x := by rw [htt]; simp
  have hfix : t * (r : P) * t⁻¹ = r := by
    rcases root_conj_cases H hcenter r hrc hro t with h | h
    · exact h
    · exact (false_of_inverting_root_of_swapped_involutions hrank H z r x y t hz hzc
        r.property hxH hyH htH hx2 hy2 ht
        (congrArg Subtype.val (mem_center_iff.mp hrc ⟨x, hxH⟩).symm)
        (congrArg Subtype.val (mem_center_iff.mp hrc ⟨y, hyH⟩).symm)
        (congrArg Subtype.val hrz) hxy rfl hty h).elim
  have htC : t ∈ centralizer ({(r : P)} : Set P) :=
    mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfix)
  have hHC : H ≤ centralizer ({(r : P)} : Set P) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp hrc ⟨a, ha⟩))
  refine ⟨r, mem_center_iff.mpr ?_, congrArg Subtype.val hrz⟩
  intro g
  have hgC : g ∈ centralizer ({(r : P)} : Set P) := by
    by_cases hg : g ∈ H
    · exact hHC hg
    · have hgt : g * t ∈ H := (mul_mem_iff_of_index_two hindex).mpr (by simp [hg, htH])
      have hh := (centralizer ({(r : P)} : Set P)).mul_mem (hHC hgt)
        ((centralizer ({(r : P)} : Set P)).inv_mem htC)
      simpa only [mul_inv_cancel_right] using hh
  exact (mem_centralizer_singleton_iff.mp hgC)

end Subgroup
