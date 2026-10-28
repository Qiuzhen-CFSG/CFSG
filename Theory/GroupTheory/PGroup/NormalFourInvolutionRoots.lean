module

public import Theory.GroupTheory.PGroup.NormalEightAbelianReduction
public import Theory.GroupTheory.PGroup.NormalAbelian
public import Theory.GroupTheory.PGroup.RankTwoNormalFour

/-!
# Fixed roots for involutions moving a normal four

Let a finite two-group have a normal elementary four, central omega of order
two, an elementary subgroup of order at least eight, and no normal elementary
eight. An involution moving the four fixes a square root of its central
involution.

Extend the four to a self-centralizing normal abelian subgroup. Its omega is
the four, and its order exceeds four. Choose an element of order four. If its
square is moved, its norm under the involution is the desired fixed root.
Otherwise its square is the central involution; its conjugation difference
lies in the fixed line of the four and can be canceled by a member of the four.

Source: Janko--Thompson, Math. Z. 113 (1970), section 6, printed p.395,
refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf.
-/

open Subgroup
open scoped IsMulCommutative

private theorem fixed_root
    {D : Type*} [Group D] [Finite D] [IsMulCommutative D]
    (hO : Nat.card (omega₁ D (p := 2)) = 4)
    (f : MulAut D) (hff : ∀ d, f (f d) = d)
    (z e : D) (hzO : z ∈ omega₁ D (p := 2)) (hz1 : z ≠ 1)
    (hfz : f z = z) (heO : e ∈ omega₁ D (p := 2)) (hfe : f e ≠ e)
    (a : D) (ha : orderOf a = 4) :
    ∃ x : D, x ^ 2 = z ∧ f x = x := by
  classical
  let : CommGroup D := IsMulCommutative.instCommGroup
  let O := omega₁ D (p := 2)
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative D
  let : Nontrivial O := Finite.one_lt_card_iff_nontrivial.mp (by change 1 < Nat.card (omega₁ D (p := 2)); omega)
  let : IsKleinFour O := ⟨hO, IsElementaryAbelian.exponent_eq_prime⟩
  let : Fintype O := Fintype.ofFinite O
  let zO : O := ⟨z, hzO⟩
  let eO : O := ⟨e, heO⟩
  have he1 : e ≠ 1 := by intro h; simp [h] at hfe
  have hez : e ≠ z := by intro h; exact hfe (h ▸ hfz)
  have hzO1 : zO ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have heO1 : eO ≠ 1 := fun h => he1 (congrArg Subtype.val h)
  have hze : zO ≠ eO := fun h => hez (congrArg Subtype.val h).symm
  have hlist (u : D) (hu : u ∈ O) : u = z * e ∨ u = z ∨ u = e ∨ u = 1 := by
    have h : (⟨u, hu⟩ : O) ∈ ({zO * eO, zO, eO, 1} : Finset O) := by
      rw [IsKleinFour.eq_finset_univ hzO1 heO1 hze]
      exact Finset.mem_univ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
    · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))
  have hz2 : z ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) z hzO
  have he2 : e ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) e heO
  have hfeO : f e ∈ O :=
    characteristic_iff_le_comap.mp (omega₁_characteristic D) f heO
  have hswap : f e = z * e := by
    rcases hlist (f e) hfeO with h | h | h | h
    · exact h
    · exact (hez (f.injective (h.trans hfz.symm))).elim
    · exact (hfe h).elim
    · exact (he1 (f.injective (h.trans f.map_one.symm))).elim
  have hfixed (u : D) (hu : u ∈ O) (hf : f u = u) : u = 1 ∨ u = z := by
    rcases hlist u hu with rfl | rfl | rfl | rfl
    · have h : z * (z * e) = z * e := by simpa only [map_mul, hfz, hswap] using hf
      have hzeq := mul_left_cancel h
      exact (hz1 (mul_right_cancel (show z * e = 1 * e by simpa using hzeq))).elim
    · exact Or.inr rfl
    · exact (hfe hf).elim
    · exact Or.inl rfl
  have hnorm (u : D) (hu : u ∈ O) (hf : f u ≠ u) : u * f u = z := by
    rcases hlist u hu with h | h | h | h
    · rw [h]
      simp only [map_mul, hfz, hswap]
      calc
        z * e * (z * (z * e)) = z * (e ^ 2) * (z ^ 2) := by simp only [pow_two]; ac_rfl
        _ = z := by rw [he2, hz2]; simp
    · exact (hf (h ▸ hfz)).elim
    · rw [h, hswap]
      calc
        e * (z * e) = z * e ^ 2 := by simp only [pow_two]; ac_rfl
        _ = z := by rw [he2]; simp
    · exact (hf (h ▸ f.map_one)).elim
  have ha2 : (a ^ 2) ^ 2 = 1 := by
    rw [← pow_mul]
    simpa [ha] using pow_orderOf_eq_one a
  have ha21 : a ^ 2 ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    norm_num [ha] at hd
  have ha2O : a ^ 2 ∈ O := subset_closure (by simpa using ha2)
  by_cases hfa2 : f (a ^ 2) = a ^ 2
  · have ha2z : a ^ 2 = z := (hfixed _ ha2O hfa2).resolve_left ha21
    let d := f a * a⁻¹
    have hd2 : d ^ 2 = 1 := by
      dsimp [d]
      rw [mul_pow, ← map_pow, ha2z, hfz, inv_pow, ha2z]
      simp
    have hdO : d ∈ O := subset_closure (by simpa using hd2)
    have hfd : f d = d := by
      have hi : d⁻¹ = d := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hd2)
      calc
        f d = d⁻¹ := by simp [d, hff, mul_comm]
        _ = d := hi
    rcases hfixed d hdO hfd with hd1 | hdz
    · refine ⟨a, ha2z, ?_⟩
      exact mul_inv_eq_one.mp hd1
    · refine ⟨a * e, ?_, ?_⟩
      · rw [mul_pow, ha2z, he2, mul_one]
      · have hfa : f a = z * a := mul_inv_eq_iff_eq_mul.mp hdz
        rw [map_mul, hfa, hswap]
        calc
          z * a * (z * e) = a * e * z ^ 2 := by simp only [pow_two]; ac_rfl
          _ = a * e := by rw [hz2]; simp
  · refine ⟨a * f a, ?_, ?_⟩
    · rw [mul_pow, ← map_pow]
      exact hnorm _ ha2O hfa2
    · simp [map_mul, hff, mul_comm]

/-- An involution moving a normal four fixes a square root of its central involution. -/
public theorem IsPGroup.exists_commuting_square_root_of_noncentral_action_on_normal_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ B : Subgroup P, B.Normal ∧ IsElementaryAbelian 2 B ∧ 8 ≤ Nat.card B)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (A : Subgroup P) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (z t : P) (hzC : z ∈ center P) (hzW : z ∈ W) (hz : orderOf z = 2)
    (ht : orderOf t = 2) (htC : t ∉ centralizer (W : Set P)) :
    ∃ x : P, x ^ 2 = z ∧ Commute x t := by
  classical
  obtain ⟨D, hWD, hDn, hDa, _, hDC⟩ :=
    exists_normal_abelian_selfCentralizing_containing hP W inferInstance inferInstance
  let : D.Normal := hDn
  let : IsMulCommutative D := hDa
  let O := omega₁ D (p := 2)
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative D
  have hWO : W ≤ O.map D.subtype := by
    intro w hw
    exact mem_map.mpr ⟨⟨w, hWD hw⟩, subset_closure (by
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) w hw), rfl⟩
  have hOcard : Nat.card O = 4 := by
    have hle := hP.card_omega_one_normal_abelian_le_four_of_no_normal_eight hno D
    have hge := card_le_of_le hWO
    rw [hW, card_map_of_injective D.subtype_injective] at hge
    change 4 ≤ Nat.card (omega₁ D (p := 2)) at hge
    change Nat.card (omega₁ D (p := 2)) = 4
    omega
  have hDlarge : 4 < Nat.card D := by
    by_contra! hsmall
    have hDW : D = W := (eq_of_le_of_card_ge hWD (by omega)).symm
    have hCsmall : Nat.card (centralizer (W : Set P)) ≤ 4 := by
      have h := card_le_of_le hDC
      rw [hDW, hW] at h
      exact h
    have hindex := centralizer_index_le_two_of_normal_four hP W hW
    have hc := (centralizer (W : Set P)).card_mul_index
    have hPsmall : Nat.card P ≤ 8 := by nlinarith
    have hAtop : A = ⊤ := A.eq_top_of_card_eq (by
      have hle := A.card_le_card_group
      omega)
    let : IsMulCommutative (⊤ : Subgroup P) := hAtop ▸ inferInstanceAs (IsMulCommutative A)
    have hcomm : IsMulCommutative P := isMulCommutative_iff.mpr (fun x y =>
      congrArg Subtype.val (mul_comm (⟨x, mem_top x⟩ : (⊤ : Subgroup P)) ⟨y, mem_top y⟩))
    let : IsMulCommutative P := hcomm
    exact four_not_le_center_of_card_omega_one_center_eq_two hZ W hW
      (fun w _ => mem_center_iff.mpr (fun p => mul_comm p w))
  obtain ⟨a, ha2⟩ : ∃ a : D, a ^ 2 ≠ 1 := by
    by_contra! h
    have htop : O = ⊤ := top_unique (fun a _ => subset_closure (by simpa using h a))
    have hcard : Nat.card O = Nat.card D := by rw [htop, Nat.card_congr Subgroup.topEquiv.toEquiv]
    omega
  obtain ⟨n, hn⟩ := (hP.to_subgroup D).exists_orderOf_eq_pow a
  have hn2 : 2 ≤ n := by
    by_contra! h
    interval_cases n
    · exact ha2 (by have ha1 : a = 1 := orderOf_eq_one_iff.mp (by simpa using hn); simp [ha1])
    · exact ha2 (by simpa [hn] using pow_orderOf_eq_one a)
  have hdiv : 4 ∣ orderOf a := by rw [hn]; exact Nat.pow_dvd_pow 2 hn2
  let b := a ^ (orderOf a / 4)
  have hb : orderOf b = 4 := orderOf_pow_orderOf_div (orderOf_pos a).ne' hdiv
  let f : MulAut D := MulAut.conjNormal t
  have ht2 : t ^ 2 = 1 := by simpa [ht] using pow_orderOf_eq_one t
  have hff : ∀ d : D, f (f d) = d := by
    intro d
    have hf : f * f = 1 := by
      change (MulAut.conjNormal : P →* MulAut D) t * MulAut.conjNormal t = 1
      rw [← map_mul, ← pow_two, ht2, map_one]
    exact congrArg (fun k : MulAut D => k d) hf
  let zD : D := ⟨z, hWD hzW⟩
  have hzO : zD ∈ O := subset_closure (by
    apply Subtype.ext
    simpa [zD, hz] using pow_orderOf_eq_one z)
  have hz1 : zD ≠ 1 := by
    intro h
    have hz1 : z = 1 := congrArg Subtype.val h
    simp [hz1] at hz
  have hfz : f zD = zD := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (mem_center_iff.mp hzC t)
  obtain ⟨e, heW, hte⟩ : ∃ e : P, e ∈ W ∧ e * t ≠ t * e := by
    by_contra! h
    exact htC (fun e he => h e he)
  let eD : D := ⟨e, hWD heW⟩
  have heO : eD ∈ O := by
    obtain ⟨u, hu, heq⟩ := mem_map.mp (hWO heW)
    exact (Subtype.ext heq : u = eD) ▸ hu
  have hfe : f eD ≠ eD := by
    intro h
    exact hte (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val h)).symm
  obtain ⟨x, hx, hfx⟩ := fixed_root hOcard f hff zD eD hzO hz1 hfz heO hfe b hb
  refine ⟨x, congrArg Subtype.val hx, ?_⟩
  exact (show Commute t (x : P) from mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hfx)).symm

