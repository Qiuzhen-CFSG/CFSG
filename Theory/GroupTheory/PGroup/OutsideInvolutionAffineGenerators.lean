module

public import Theory.GroupTheory.PGroup.OutsideInvolutionSquare

/-!
# Generators in the outside extension of a core of order sixteen

Only elementary subgroups inside the core are bounded here. A core-normal
four different from the unique ambient normal four is moved by an outside
involution. Its moved generator and a central fourth root give the explicit
relations for the affine extension when the central involution has no square
root in the ambient center.

Source: Janko–Thompson (1970), Lemma 4.1, printed p.393. The local
commutator and cyclic-center calculations adapt OutsideInvolutionSquare;
the rank hypothesis is restricted to the core before using it.
-/

namespace Subgroup
open scoped commutatorElement

private theorem mem_four_of_core_rank {P : Type*} [Group P] [Finite P]
    (H F : Subgroup P)
    (hrank : ∀ U : Subgroup H, IsElementaryAbelian 2 U → Nat.card U < 8)
    [IsElementaryAbelian 2 F] (hF : Nat.card F = 4) (hFH : F ≤ H)
    (x : P) (hxH : x ∈ H) (hx : x ^ 2 = 1)
    (hxc : x ∈ centralizer (F : Set P)) : x ∈ F := by
  let : IsElementaryAbelian 2 (F.subgroupOf H) := IsElementaryAbelian.subgroupOf hFH
  have hcard : Nat.card (F.subgroupOf H) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hFH).toEquiv).trans hF
  exact mem_four_of_square_eq_one_of_elementary_card_lt_eight hrank
    (F.subgroupOf H) hcard (x := ⟨x, hxH⟩) (Subtype.ext hx) (by
      intro y hy
      exact Subtype.ext (hxc y hy))

private theorem not_commute_conj_of_unique_normal_four_core {P : Type*} [Group P] [Finite P]
    (H E : Subgroup P) [H.Normal]
    (hrank : ∀ A : Subgroup H, IsElementaryAbelian 2 A → Nat.card A < 8) (hindex : H.index = 2)
    (hunique : ∀ F : Subgroup P, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = E)
    (z x t : P) (hzE : z ∈ E) (hz : orderOf z = 2) (hzc : z ∈ center P)
    (hx : x ^ 2 = 1) (hxH : x ∈ H) (hzH : z ∈ H) (hxE : x ∉ E) (htH : t ∉ H)
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
    apply mem_four_of_core_rank H F hrank
      (IsKleinFour.card_four (G := F))
      ((closure_le _).mpr (by rintro a (rfl | rfl) <;> assumption))
      _ ((inferInstance : H.Normal).conj_mem x hxH t)
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
    (H E F : Subgroup P) [H.Normal]
    (hrank : ∀ A : Subgroup H, IsElementaryAbelian 2 A → Nat.card A < 8) [IsElementaryAbelian 2 F]
    (hindex : H.index = 2) (hE : Nat.card E = 4) (hF : Nat.card F = 4)
    (hFH : F ≤ H) (hnorm : H ≤ normalizer (F : Set P)) (hFE : F ≠ E)
    (hunique : ∀ U : Subgroup P, U.Normal → IsElementaryAbelian 2 U → Nat.card U = 4 → U = E)
    (z t : P) (hzH : z ∈ H) (hzE : z ∈ E) (hz : orderOf z = 2) (hzc : z ∈ center P)
    (htH : t ∉ H) :
    ∃ x : P, x ∈ H ∧ x ^ 2 = 1 ∧ ¬ Commute x (t * x * t⁻¹) := by
  have hnot : ¬ F ≤ E := fun h => hFE (eq_of_le_of_card_ge h (by omega))
  obtain ⟨x, hxF, hxE⟩ := SetLike.not_le_iff_exists.mp hnot
  have hx2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := F) x hxF
  have hz2 : z ^ 2 = 1 := by simpa only [hz] using pow_orderOf_eq_one z
  have hzF := mem_four_of_core_rank H F hrank hF hFH z hzH hz2
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
    not_commute_conj_of_unique_normal_four_core H E hrank hindex hunique z x t hzE hz hzc
      hx2 (hFH hxF) hzH hxE htH (heq.symm ▸ hnorm)⟩


/-- An outside involution and the failure of a central square root supply
explicit affine generators. The only rank bound is inside the core. -/
public theorem exists_affine_generators_of_order_sixteen_core
    {P : Type*} [Group P] [Finite P]
    (H E F : Subgroup P) [H.Normal] [IsCyclic (center H)] [IsElementaryAbelian 2 F]
    (hrank : ∀ U : Subgroup H, IsElementaryAbelian 2 U → Nat.card U < 8)
    (hcard : Nat.card H = 16) (hcenter : Nat.card (center H) = 4)
    (hindex : H.index = 2) (hE : Nat.card E = 4) (hF : Nat.card F = 4)
    (hEH : E ≤ H) (hFH : F ≤ H) (hnorm : H ≤ normalizer (F : Set P)) (hFE : F ≠ E)
    (hunique : ∀ U : Subgroup P, U.Normal → IsElementaryAbelian 2 U → Nat.card U = 4 → U = E)
    (z t : P) (hzE : z ∈ E) (hz : orderOf z = 2) (hzc : z ∈ center P)
    (ht : t ^ 2 = 1) (htH : t ∉ H)
    (hnoroot : ¬ ∃ r : P, r ∈ center P ∧ r ^ 2 = z) :
    ∃ r x : P, orderOf r = 4 ∧ r ^ 2 = z ∧ x ^ 2 = 1 ∧
      Commute r x ∧ t * r * t⁻¹ = r⁻¹ ∧ (x * t) ^ 4 = z := by
  let Z : H := ⟨z, hEH hzE⟩
  have hZc : Z ∈ center H := mem_center_iff.mpr
    (fun h => Subtype.ext (mem_center_iff.mp hzc h))
  have hZo : orderOf Z = 2 := (Subgroup.orderOf_coe Z).symm.trans hz
  obtain ⟨r, hrc, hro, hrz⟩ := root_exists hcenter Z hZo hZc
  obtain ⟨x, hxH, hx2, hxmove⟩ := exists_noncommuting_conjugate H E F hrank hindex hE hF
    hFH hnorm hFE hunique z t (hEH hzE) hzE hz hzc htH
  let y := t * x * t⁻¹
  have hyH : y ∈ H := (inferInstance : H.Normal).conj_mem x hxH t
  have hy2 : y ^ 2 = 1 := by
    have hh := congrArg (MulAut.conj t) hx2
    simpa only [map_pow, map_one, MulAut.conj_apply] using hh
  have hxy : (x * y) ^ 2 = z := congrArg Subtype.val
    (pair_square hcard hcenter Z hZo hZc ⟨x, hxH⟩ ⟨y, hyH⟩
      (Subtype.ext hx2) (Subtype.ext hy2) (fun h => hxmove (congrArg Subtype.val h)))
  have hinvert : t * (r : P) * t⁻¹ = (r : P)⁻¹ := by
    rcases root_conj_cases H hcenter r hrc hro t with h | h
    · exfalso
      apply hnoroot
      refine ⟨r, mem_center_iff.mpr ?_, congrArg Subtype.val hrz⟩
      intro g
      have htC : t ∈ centralizer ({(r : P)} : Set P) :=
        mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h)
      have hHC : H ≤ centralizer ({(r : P)} : Set P) := by
        intro a ha
        exact mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_center_iff.mp hrc ⟨a, ha⟩))
      apply mem_centralizer_singleton_iff.mp
      by_cases hg : g ∈ H
      · exact hHC hg
      · have hgt : g * t ∈ H := (mul_mem_iff_of_index_two hindex).mpr (by simp [hg, htH])
        simpa only [mul_inv_cancel_right] using
          (centralizer ({(r : P)} : Set P)).mul_mem (hHC hgt)
            ((centralizer ({(r : P)} : Set P)).inv_mem htC)
    · exact h
  refine ⟨r, x, (Subgroup.orderOf_coe r).trans hro, congrArg Subtype.val hrz, hx2,
    congrArg Subtype.val (mem_center_iff.mp hrc ⟨x, hxH⟩).symm, hinvert, ?_⟩
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ht)
  have hsq : (x * t) ^ 2 = x * y := by dsimp [y]; rw [hti, pow_two]; group
  rw [show 4 = 2 * 2 from rfl, pow_mul, hsq, hxy]

end Subgroup
