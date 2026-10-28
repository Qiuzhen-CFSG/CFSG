module

public import Theory.GroupTheory.PGroup.UniqueInvolution
public import Theory.GroupTheory.PGroup.RankOneInvolution
public import Theory.GroupTheory.PGroup.NormalFour
public import Theory.GroupTheory.QuaternionPresentation
public import Theory.Frattini.PGroup

/-!
# Finite two-groups with a unique involution

A finite two-group with a unique involution is cyclic or generalized quaternion.
The proof follows Huppert, *Endliche Gruppen I*, III.7.5–III.8.2:
the Frattini subgroup is cyclic, a maximal normal abelian subgroup containing it
has index two, and conjugation outside that subgroup is inversion. The resulting
relations give Mathlib's generalized quaternion group.

The arithmetic and Frattini arguments are extracted from
`BenderSuzuki/External/Huppert/IV/Basic.lean`; this module depends only on Theory
and Mathlib. Quaternion presentation recognition and the abelian unique-involution
case use their existing Theory interfaces.
-/

open scoped Pointwise

universe u

namespace IsPGroup

private theorem huppert_I_14_9_conj_inverts_of_cyclic_index_two
    {G : Type u} [Group G] [Finite G] {k : ℕ} [NeZero k]
    (A : Subgroup G) [A.Normal] (a b : G)
    (hA_eq : Subgroup.zpowers a = A)
    (hA_index : A.index = 2)
    (ha_order : orderOf a = 2 * k)
    (hb_not_mem : b ∉ A)
    (hunique_order_two : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x = y)
    (hnot_cyclic : ¬ IsCyclic G)
    (hcard : Nat.card G = 4 * k)
    (hGp : IsPGroup 2 G) :
    ∀ z : ℤ, a ^ z * b = b * a ^ (-z) := by
  have hcoverA : ∀ g : G, g ∈ A ∨ b⁻¹ * g ∈ A := by
    intro g
    by_cases hgA : g ∈ A
    · exact Or.inl hgA
    · have hiff := A.mul_mem_iff_of_index_two (by simpa using hA_index) (a := b⁻¹) (b := g)
      have hb_inv_not : b⁻¹ ∉ A := by
        intro hb_inv
        exact hb_not_mem (by simpa using A.inv_mem hb_inv)
      exact Or.inr (hiff.mpr (Iff.intro (fun hb => False.elim (hb_inv_not hb)) (fun hg => False.elim (hgA hg))))
  have hcover : ∀ g : G, ∃ i : ZMod (2 * k),
      g = a ^ (i.val : ℤ) ∨ g = b * a ^ (i.val : ℤ) := by
    intro g
    rcases hcoverA g with hgA | hbgA
    · rw [← hA_eq] at hgA
      rcases Subgroup.mem_zpowers_iff.mp hgA with ⟨z, hz⟩
      refine ⟨(z : ZMod (2 * k)), Or.inl ?_⟩
      calc
        g = a ^ z := hz.symm
        _ = a ^ (((z : ZMod (2 * k)).val : ℕ) : ℤ) := by
          apply (zpow_eq_zpow_iff_modEq (x := a)).2
          simpa [ha_order] using
            (ZMod.intCast_eq_intCast_iff z (((z : ZMod (2 * k)).val : ℕ) : ℤ) (2 * k)).mp (by simp)
    · rw [← hA_eq] at hbgA
      rcases Subgroup.mem_zpowers_iff.mp hbgA with ⟨z, hz⟩
      refine ⟨(z : ZMod (2 * k)), Or.inr ?_⟩
      calc
        g = b * (b⁻¹ * g) := by group
        _ = b * a ^ z := by rw [hz]
        _ = b * a ^ (((z : ZMod (2 * k)).val : ℕ) : ℤ) := by
          congr 1
          apply (zpow_eq_zpow_iff_modEq (x := a)).2
          simpa [ha_order] using
            (ZMod.intCast_eq_intCast_iff z (((z : ZMod (2 * k)).val : ℕ) : ℤ) (2 * k)).mp (by simp)
  have hb_sq_mem : b * b ∈ A := by
    simpa [pow_two] using A.sq_mem_of_index_two hA_index b
  have hb_sq_in_zpowers : b * b ∈ Subgroup.zpowers a := by
    simpa [hA_eq] using hb_sq_mem
  have ha_k_order_two : orderOf (a ^ (k : ℤ)) = 2 := by
    have hkpos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
    have hnat : orderOf (a ^ k) = 2 := by
      rw [orderOf_pow, ha_order]
      rw [Nat.gcd_mul_left_left]
      rw [Nat.mul_comm 2 k]
      exact Nat.mul_div_right 2 hkpos
    simpa [zpow_natCast] using hnat
  have hA_card : Nat.card A = 2 * k := by
    have hmul : Nat.card A * A.index = Nat.card G := A.card_mul_index
    have hmul' : Nat.card A * 2 = 4 * k := by
      simpa [hA_index, hcard] using hmul
    have htarget : (2 * k) * 2 = 4 * k := by ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) (hmul'.trans htarget.symm)
  have ha_k_mem_A : a ^ (k : ℤ) ∈ A := by
    rw [← hA_eq]
    exact Subgroup.zpow_mem_zpowers a (k : ℤ)
  have houtside_sq_ne_one : ∀ x : G, x ∉ A → x * x ≠ 1 := by
    intro x hxA hsq
    have hx_ne_one : x ≠ 1 := by
      intro hx
      exact hxA (by simp [hx])
    have hx_order : orderOf x = 2 := by
      have hpow : x ^ 2 = 1 := by simpa [pow_two] using hsq
      have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hpow
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact False.elim (hx_ne_one (orderOf_eq_one_iff.mp h))
      · exact h
    have hx_eq_ak := hunique_order_two x (a ^ (k : ℤ)) hx_order ha_k_order_two
    exact hxA (by simpa [hx_eq_ak] using ha_k_mem_A)
  have hright_not_mem_A : ∀ z : ℤ, a ^ z * b ∉ A := by
    intro z hzA
    have haz : a ^ z ∈ A := by
      rw [← hA_eq]
      exact Subgroup.zpow_mem_zpowers a z
    have hbA : b ∈ A := by
      have hmul : (a ^ z)⁻¹ * (a ^ z * b) ∈ A := A.mul_mem (A.inv_mem haz) hzA
      simpa [mul_assoc] using hmul
    exact hb_not_mem hbA
  have hright_sq_ne_one : ∀ z : ℤ, (a ^ z * b) * (a ^ z * b) ≠ 1 := by
    intro z
    exact houtside_sq_ne_one (a ^ z * b) (hright_not_mem_A z)
  have hb_sq_ne_one : b * b ≠ 1 := by
    simpa using hright_sq_ne_one 0
  have ha_mem_A : a ∈ A := by
    rw [← hA_eq]
    exact Subgroup.mem_zpowers a
  have hbab_mem_A : b * a * b⁻¹ ∈ A := by
    exact (inferInstance : A.Normal).conj_mem a ha_mem_A b
  obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp (by
    simpa [hA_eq] using hbab_mem_A : b * a * b⁻¹ ∈ Subgroup.zpowers a)
  obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp hb_sq_in_zpowers
  have hconj_a_zpow : ∀ z : ℤ, b * a ^ z * b⁻¹ = a ^ (r * z) := by
    intro z
    calc
      b * a ^ z * b⁻¹ = (b * a * b⁻¹) ^ z := (conj_zpow (a := b) (b := a) (i := z)).symm
      _ = (a ^ r) ^ z := by rw [hr]
      _ = a ^ (r * z) := by rw [zpow_mul]
  have hr_square_one : a ^ (r * r) = a := by
    calc
      a ^ (r * r) = b * a ^ r * b⁻¹ := (hconj_a_zpow r).symm
      _ = b * (b * a * b⁻¹) * b⁻¹ := by rw [hr]
      _ = (b * b) * a * (b * b)⁻¹ := by group
      _ = a := by
        rw [← hs]
        group
  have hs_fixed_by_r : a ^ (r * s) = a ^ s := by
    calc
      a ^ (r * s) = b * a ^ s * b⁻¹ := (hconj_a_zpow s).symm
      _ = b * (b * b) * b⁻¹ := by rw [hs]
      _ = b * b := by group
      _ = a ^ s := hs.symm
  have hAp : IsPGroup 2 A := hGp.to_subgroup A
  obtain ⟨M, hA_card_pow⟩ := hAp.exists_card_eq
  have ha_order_pow : orderOf a = 2 ^ M := by
    calc
      orderOf a = 2 * k := ha_order
      _ = Nat.card A := hA_card.symm
      _ = 2 ^ M := hA_card_pow
  have hright_square_formula : ∀ z : ℤ,
      (a ^ z * b) * (a ^ z * b) = a ^ ((1 + r) * z + s) := by
    intro z
    calc
      (a ^ z * b) * (a ^ z * b) =
          a ^ z * (b * a ^ z * b⁻¹) * (b * b) := by group
      _ = a ^ z * a ^ (r * z) * a ^ s := by rw [hconj_a_zpow z, ← hs]
      _ = a ^ (z + r * z) * a ^ s := by rw [← zpow_add]
      _ = a ^ ((1 + r) * z + s) := by
        rw [← zpow_add]
        ring_nf
  have hright_square_mod_ne_zero :
      ∀ z : ℤ, ¬ (((1 + r) * z + s) ≡ 0 [ZMOD (orderOf a : ℤ)]) := by
    intro z hz
    exact hright_sq_ne_one z (by
      rw [hright_square_formula z]
      have hpow0 : a ^ ((1 + r) * z + s) = a ^ (0 : ℤ) :=
        (zpow_eq_zpow_iff_modEq (x := a)).2 (by simpa using hz)
      simpa using hpow0)
  have hr_square_mod : r * r ≡ 1 [ZMOD (orderOf a : ℤ)] := by
    exact (zpow_eq_zpow_iff_modEq (x := a)).1 (by simpa using hr_square_one)
  have hs_fixed_mod : r * s ≡ s [ZMOD (orderOf a : ℤ)] := by
    exact (zpow_eq_zpow_iff_modEq (x := a)).1 hs_fixed_by_r
  have hflip_mod : r ≡ -1 [ZMOD (orderOf a : ℤ)] := by
    have horder_pow_int : (orderOf a : ℤ) = (2 : ℤ) ^ M := by
      exact_mod_cast ha_order_pow
    have hbad :
        ¬ ∃ z : ℤ, ((1 + r) * z + s) ≡ 0 [ZMOD ((2 : ℤ) ^ M)] := by
      rintro ⟨z, hz⟩
      exact hright_square_mod_ne_zero z (by
        simpa [horder_pow_int] using hz)
    by_contra hr_not_flip
    suffices hcycle : IsCyclic G from hnot_cyclic hcycle
    have hnonflip_forces_cyclic :
        (¬ r ≡ -1 [ZMOD (orderOf a : ℤ)]) → IsCyclic G := by
      intro hr_not_flip'
      have hcore :
          IsCyclic G ∨
            ∃ z : ℤ, ((1 + r) * z + s) ≡ 0 [ZMOD ((2 : ℤ) ^ M)] := by
        have hcentralizes_zpowers_of_r_one :
            r ≡ 1 [ZMOD (orderOf a : ℤ)] →
              ∀ z : ℤ, b * a ^ z * b⁻¹ = a ^ z := by
          intro hr_one z
          calc
            b * a ^ z * b⁻¹ = a ^ (r * z) := hconj_a_zpow z
            _ = a ^ ((1 : ℤ) * z) := by
              apply (zpow_eq_zpow_iff_modEq (x := a)).2
              exact hr_one.mul_right z
            _ = a ^ z := by ring_nf
        have hcyclic_of_zpowers_le_b :
            Subgroup.zpowers a ≤ Subgroup.zpowers b → IsCyclic G := by
          intro hA_le_b
          have htop : Subgroup.zpowers b = ⊤ := by
            apply le_antisymm le_top
            intro g hg
            rcases hcover g with ⟨i, hgi | hgi⟩
            · rw [hgi]
              exact hA_le_b (Subgroup.zpow_mem_zpowers a (i.val : ℤ))
            · rw [hgi]
              exact Subgroup.mul_mem _ (Subgroup.mem_zpowers b)
                (hA_le_b (Subgroup.zpow_mem_zpowers a (i.val : ℤ)))
          exact (isCyclic_iff_exists_zpowers_eq_top).2 ⟨b, htop⟩
        have hcyclic_of_a_mem_zpowers_b :
            a ∈ Subgroup.zpowers b → IsCyclic G := by
          intro ha_b
          exact hcyclic_of_zpowers_le_b (Subgroup.zpowers_le_of_mem ha_b)
        have ha_mem_zpowers_b_of_a_mem_zpowers_as :
            a ∈ Subgroup.zpowers (a ^ s) → a ∈ Subgroup.zpowers b := by
          intro ha_mem_as
          rcases Subgroup.mem_zpowers_iff.mp ha_mem_as with ⟨t, ht⟩
          rw [← ht]
          have hb2 : b * b ∈ Subgroup.zpowers b := by
            exact Subgroup.mul_mem _ (Subgroup.mem_zpowers b) (Subgroup.mem_zpowers b)
          have has_mem : a ^ s ∈ Subgroup.zpowers b := by
            simpa [hs] using hb2
          exact Subgroup.zpow_mem _ has_mem t
        have hcyclic_of_r_one :
            r ≡ 1 [ZMOD (orderOf a : ℤ)] → IsCyclic G := by
          intro hr_one
          have hs_unit_mod_order : s.gcd (orderOf a : ℤ) = 1 := by
            by_contra hs_not_unit
            have hsol_two : ∃ z : ℤ,
                (2 * z + s) ≡ 0 [ZMOD ((2 : ℤ) ^ M)] := by
              have hM_pos : 0 < M := by
                by_contra hM_not
                have hM0 : M = 0 := Nat.eq_zero_of_not_pos hM_not
                have horder_one : orderOf a = 1 := by
                  simp [ha_order_pow, hM0]
                have hk_zero : k = 0 := by omega
                exact (NeZero.ne k) hk_zero
              have hs_even : Even s := by
                by_contra hs_odd
                have hs_odd' : Odd s := Int.not_even_iff_odd.mp hs_odd
                have hs_nat_odd : Odd s.natAbs := hs_odd'.natAbs
                have hs_nat_coprime : Nat.Coprime s.natAbs (2 ^ M) := by
                  exact (Nat.prime_two.coprime_pow_of_not_dvd (m := M))
                    (by
                      intro htwo
                      exact Nat.not_even_iff_odd.mpr hs_nat_odd (even_iff_two_dvd.mpr htwo))
                have hs_gcd_one_nat : Nat.gcd s.natAbs (2 ^ M) = 1 :=
                  hs_nat_coprime.gcd_eq_one
                have hs_gcd_one : s.gcd (orderOf a : ℤ) = 1 := by
                  rw [horder_pow_int]
                  exact_mod_cast hs_gcd_one_nat
                exact hs_not_unit hs_gcd_one
              refine ⟨-(s / 2), ?_⟩
              have hcalc : 2 * (-(s / 2)) + s = 0 := by
                have hs2 : 2 * (s / 2) = s := Int.two_mul_ediv_two_of_even hs_even
                omega
              rw [hcalc]
            rcases hsol_two with ⟨z, hz⟩
            exact hbad ⟨z, by
              have hcoeff : (1 + r) * z + s ≡ 2 * z + s [ZMOD ((2 : ℤ) ^ M)] := by
                have hr_one_pow : r ≡ 1 [ZMOD ((2 : ℤ) ^ M)] := by
                  simpa [horder_pow_int] using hr_one
                exact (hr_one_pow.add_left 1).mul_right z |>.add_right s
              exact hcoeff.trans hz⟩
          have ha_mem_as : a ∈ Subgroup.zpowers (a ^ s) := by
            exact (mem_zpowers_zpow_iff (g := a) (k := s)).2 (by
              simpa using hs_unit_mod_order)
          exact hcyclic_of_a_mem_zpowers_b
            (ha_mem_zpowers_b_of_a_mem_zpowers_as ha_mem_as)
        have hlinear_solution_of_nontrivial_root (hM_ge_three : 3 ≤ M) :
            (r ≡ 1 + (2 : ℤ) ^ (M - 1) [ZMOD ((2 : ℤ) ^ M)] ∨
                r ≡ -1 + (2 : ℤ) ^ (M - 1) [ZMOD ((2 : ℤ) ^ M)]) →
              ∃ z : ℤ, ((1 + r) * z + s) ≡ 0 [ZMOD ((2 : ℤ) ^ M)] := by
          intro hr_mid
          have hlinear_of_gcd_dvd :
              ((1 + r).gcd ((2 : ℤ) ^ M) : ℤ) ∣ s →
                ∃ z : ℤ, ((1 + r) * z + s) ≡ 0 [ZMOD ((2 : ℤ) ^ M)] := by
            intro hdiv
            rcases hdiv with ⟨t, ht⟩
            refine ⟨-(Int.gcdA (1 + r) ((2 : ℤ) ^ M)) * t, ?_⟩
            rw [Int.modEq_zero_iff_dvd]
            refine ⟨Int.gcdB (1 + r) ((2 : ℤ) ^ M) * t, ?_⟩
            have hbez : (((1 + r).gcd ((2 : ℤ) ^ M) : ℕ) : ℤ) =
                (1 + r) * Int.gcdA (1 + r) ((2 : ℤ) ^ M) +
                  ((2 : ℤ) ^ M) * Int.gcdB (1 + r) ((2 : ℤ) ^ M) :=
              Int.gcd_eq_gcd_ab (1 + r) ((2 : ℤ) ^ M)
            calc
              (1 + r) * (-(Int.gcdA (1 + r) ((2 : ℤ) ^ M)) * t) + s =
                  -((1 + r) * Int.gcdA (1 + r) ((2 : ℤ) ^ M) * t) + s := by ring
              _ = -((1 + r) * Int.gcdA (1 + r) ((2 : ℤ) ^ M) * t) +
                    (((1 + r).gcd ((2 : ℤ) ^ M) : ℕ) : ℤ) * t := by rw [ht]
              _ = ((2 : ℤ) ^ M) * (Int.gcdB (1 + r) ((2 : ℤ) ^ M) * t) := by
                rw [hbez]
                ring
          have hs_fixed_pow : r * s ≡ s [ZMOD ((2 : ℤ) ^ M)] := by
            simpa [horder_pow_int] using hs_fixed_mod
          have hsub_fixed : (r - 1) * s ≡ 0 [ZMOD ((2 : ℤ) ^ M)] := by
            have hdiff : r * s - s ≡ s - s [ZMOD ((2 : ℤ) ^ M)] := hs_fixed_pow.sub Int.ModEq.rfl
            simpa [sub_mul, one_mul] using hdiff
          apply hlinear_of_gcd_dvd
          rcases hr_mid with hr_mid_pos | hr_mid_neg
          · have hs_even : (2 : ℤ) ∣ s := by
              have hM_pos : 0 < M := by
                by_contra hM_not
                have hM0 : M = 0 := Nat.eq_zero_of_not_pos hM_not
                have horder_one : orderOf a = 1 := by
                  simp [ha_order_pow, hM0]
                have hk_zero : k = 0 := by omega
                exact (NeZero.ne k) hk_zero
              have hpow_sub_ne_zero : ((2 : ℤ) ^ (M - 1)) ≠ 0 := by
                exact pow_ne_zero _ (by norm_num : (2 : ℤ) ≠ 0)
              have hsub_coeff : r - 1 ≡ (2 : ℤ) ^ (M - 1) [ZMOD ((2 : ℤ) ^ M)] := by
                have h := hr_mid_pos.sub (Int.ModEq.refl (1 : ℤ))
                convert h using 1
                ring
              have hpow_s_zero : ((2 : ℤ) ^ (M - 1)) * s ≡ 0 [ZMOD ((2 : ℤ) ^ M)] := by
                exact (hsub_coeff.mul_right s).symm.trans hsub_fixed
              have hdiv_pow : (2 : ℤ) ^ M ∣ ((2 : ℤ) ^ (M - 1)) * s := by
                exact Int.modEq_zero_iff_dvd.mp hpow_s_zero
              have hM_eq : M = (M - 1) + 1 := by omega
              have hdiv_pow' : (2 : ℤ) ^ (M - 1) * 2 ∣ (2 : ℤ) ^ (M - 1) * s := by
                rw [hM_eq, pow_succ] at hdiv_pow
                simpa [mul_assoc, mul_comm, mul_left_comm] using hdiv_pow
              exact (mul_dvd_mul_iff_left hpow_sub_ne_zero).mp hdiv_pow'
            have hdiv : ((1 + r).gcd ((2 : ℤ) ^ M) : ℤ) ∣ 2 := by
              let g : ℤ := ((1 + r).gcd ((2 : ℤ) ^ M) : ℤ)
              change g ∣ (2 : ℤ)
              have hg_left : g ∣ 1 + r := by
                dsimp [g]
                exact Int.gcd_dvd_left (1 + r) ((2 : ℤ) ^ M)
              have hg_right : g ∣ (2 : ℤ) ^ M := by
                dsimp [g]
                exact Int.gcd_dvd_right (1 + r) ((2 : ℤ) ^ M)
              have hcoeff :
                  1 + r ≡ 2 + (2 : ℤ) ^ (M - 1) [ZMOD ((2 : ℤ) ^ M)] := by
                have h := hr_mid_pos.add_left (1 : ℤ)
                convert h using 1
                ring
              have hdiff_dvd :
                  (2 : ℤ) ^ M ∣
                    (1 + r) - (2 + (2 : ℤ) ^ (M - 1)) := by
                apply Int.modEq_zero_iff_dvd.mp
                have h := hcoeff.sub (Int.ModEq.refl (2 + (2 : ℤ) ^ (M - 1)))
                simpa using h
              have hg_diff :
                  g ∣ (1 + r) - (2 + (2 : ℤ) ^ (M - 1)) :=
                hg_right.trans hdiff_dvd
              have hg_coeff : g ∣ 2 + (2 : ℤ) ^ (M - 1) := by
                have hsub :
                    g ∣ (1 + r) - ((1 + r) - (2 + (2 : ℤ) ^ (M - 1))) :=
                  dvd_sub hg_left hg_diff
                convert hsub using 1
                ring
              have hM1 : M - 1 = (M - 2) + 1 := by omega
              have hc_eq :
                  2 + (2 : ℤ) ^ (M - 1) =
                    2 * (1 + (2 : ℤ) ^ (M - 2)) := by
                rw [hM1, pow_succ]
                ring
              have hp_mul :
                  (2 : ℤ) ^ M * (2 : ℤ) ^ (M - 3) =
                    2 * ((2 : ℤ) ^ (M - 2)) ^ 2 := by
                calc
                  (2 : ℤ) ^ M * (2 : ℤ) ^ (M - 3)
                      = (2 : ℤ) ^ (M + (M - 3)) := by rw [← pow_add]
                  _ = (2 : ℤ) ^ (((M - 2) + (M - 2)) + 1) := by
                    congr 1
                    omega
                  _ = (2 : ℤ) ^ ((M - 2) + (M - 2)) * 2 := by
                    rw [pow_succ]
                  _ = ((2 : ℤ) ^ (M - 2) * (2 : ℤ) ^ (M - 2)) * 2 := by
                    rw [pow_add]
                  _ = 2 * ((2 : ℤ) ^ (M - 2)) ^ 2 := by
                    ring
              have hcomb :
                  (2 + (2 : ℤ) ^ (M - 1)) * (1 - (2 : ℤ) ^ (M - 2)) +
                      (2 : ℤ) ^ M * (2 : ℤ) ^ (M - 3) = 2 := by
                rw [hc_eq, hp_mul]
                ring
              have hg_comb :
                  g ∣
                    (2 + (2 : ℤ) ^ (M - 1)) * (1 - (2 : ℤ) ^ (M - 2)) +
                      (2 : ℤ) ^ M * (2 : ℤ) ^ (M - 3) := by
                exact dvd_add
                  (dvd_mul_of_dvd_left hg_coeff _)
                  (dvd_mul_of_dvd_left hg_right _)
              simpa [hcomb] using hg_comb
            exact hdiv.trans hs_even
          · have hpow_dvd_s : (2 : ℤ) ^ (M - 1) ∣ s := by
              have htwo_ne_zero : (2 : ℤ) ≠ 0 := by norm_num
              have hsub_coeff :
                  r - 1 ≡ (2 : ℤ) ^ (M - 1) - 2 [ZMOD ((2 : ℤ) ^ M)] := by
                have h := hr_mid_neg.sub (Int.ModEq.refl (1 : ℤ))
                convert h using 1
                ring
              have hcoeff_s_zero :
                  ((2 : ℤ) ^ (M - 1) - 2) * s ≡ 0 [ZMOD ((2 : ℤ) ^ M)] := by
                exact (hsub_coeff.mul_right s).symm.trans hsub_fixed
              have hdiv_pow :
                  (2 : ℤ) ^ M ∣ (((2 : ℤ) ^ (M - 1) - 2) * s) := by
                exact Int.modEq_zero_iff_dvd.mp hcoeff_s_zero
              have hcoeff_eq :
                  (2 : ℤ) ^ (M - 1) - 2 =
                    2 * ((2 : ℤ) ^ (M - 2) - 1) := by
                have hM1 : M - 1 = (M - 2) + 1 := by omega
                rw [hM1, pow_succ]
                ring
              have hpow_eq :
                  (2 : ℤ) ^ M = 2 * (2 : ℤ) ^ (M - 1) := by
                have hM : M = (M - 1) + 1 := by omega
                rw [hM, pow_succ]
                simp [mul_comm]
              have hdiv_cancel :
                  (2 : ℤ) ^ (M - 1) ∣ ((2 : ℤ) ^ (M - 2) - 1) * s := by
                have hdiv' :
                    2 * (2 : ℤ) ^ (M - 1) ∣
                      2 * (((2 : ℤ) ^ (M - 2) - 1) * s) := by
                  simpa [hpow_eq, hcoeff_eq, mul_assoc, mul_comm, mul_left_comm] using hdiv_pow
                exact (mul_dvd_mul_iff_left htwo_ne_zero).mp hdiv'
              rcases hdiv_cancel with ⟨t, ht⟩
              have hpow_mul :
                  (2 : ℤ) ^ (M - 1) * (2 : ℤ) ^ (M - 3) =
                    ((2 : ℤ) ^ (M - 2)) ^ 2 := by
                calc
                  (2 : ℤ) ^ (M - 1) * (2 : ℤ) ^ (M - 3)
                      = (2 : ℤ) ^ ((M - 1) + (M - 3)) := by rw [← pow_add]
                  _ = (2 : ℤ) ^ ((M - 2) + (M - 2)) := by
                    congr 1
                    omega
                  _ = (2 : ℤ) ^ (M - 2) * (2 : ℤ) ^ (M - 2) := by rw [pow_add]
                  _ = ((2 : ℤ) ^ (M - 2)) ^ 2 := by ring
              have hbez :
                  ((2 : ℤ) ^ (M - 2) - 1) * (-((2 : ℤ) ^ (M - 2) + 1)) +
                    (2 : ℤ) ^ (M - 1) * (2 : ℤ) ^ (M - 3) = 1 := by
                rw [hpow_mul]
                ring
              refine ⟨t * (-((2 : ℤ) ^ (M - 2) + 1)) + (2 : ℤ) ^ (M - 3) * s, ?_⟩
              calc
                s = 1 * s := by ring
                _ = (((2 : ℤ) ^ (M - 2) - 1) * (-((2 : ℤ) ^ (M - 2) + 1)) +
                      (2 : ℤ) ^ (M - 1) * (2 : ℤ) ^ (M - 3)) * s := by
                  rw [hbez]
                _ = (((2 : ℤ) ^ (M - 2) - 1) * s) *
                        (-((2 : ℤ) ^ (M - 2) + 1)) +
                      (2 : ℤ) ^ (M - 1) * ((2 : ℤ) ^ (M - 3) * s) := by
                  ring
                _ = ((2 : ℤ) ^ (M - 1) * t) *
                        (-((2 : ℤ) ^ (M - 2) + 1)) +
                      (2 : ℤ) ^ (M - 1) * ((2 : ℤ) ^ (M - 3) * s) := by
                  rw [ht]
                _ = (2 : ℤ) ^ (M - 1) *
                    (t * (-((2 : ℤ) ^ (M - 2) + 1)) + (2 : ℤ) ^ (M - 3) * s) := by
                  ring
            have hdiv : ((1 + r).gcd ((2 : ℤ) ^ M) : ℤ) ∣ (2 : ℤ) ^ (M - 1) := by
              let g : ℤ := ((1 + r).gcd ((2 : ℤ) ^ M) : ℤ)
              change g ∣ (2 : ℤ) ^ (M - 1)
              have hg_left : g ∣ 1 + r := by
                dsimp [g]
                exact Int.gcd_dvd_left (1 + r) ((2 : ℤ) ^ M)
              have hg_right : g ∣ (2 : ℤ) ^ M := by
                dsimp [g]
                exact Int.gcd_dvd_right (1 + r) ((2 : ℤ) ^ M)
              have hcoeff :
                  1 + r ≡ (2 : ℤ) ^ (M - 1) [ZMOD ((2 : ℤ) ^ M)] := by
                have h := hr_mid_neg.add_left (1 : ℤ)
                convert h using 1
                ring
              have hdiff_dvd :
                  (2 : ℤ) ^ M ∣ (1 + r) - (2 : ℤ) ^ (M - 1) := by
                apply Int.modEq_zero_iff_dvd.mp
                have h := hcoeff.sub (Int.ModEq.refl ((2 : ℤ) ^ (M - 1)))
                simpa using h
              have hg_diff :
                  g ∣ (1 + r) - (2 : ℤ) ^ (M - 1) :=
                hg_right.trans hdiff_dvd
              have hsub :
                  g ∣ (1 + r) - ((1 + r) - (2 : ℤ) ^ (M - 1)) :=
                dvd_sub hg_left hg_diff
              convert hsub using 1
              ring
            exact hdiv.trans hpow_dvd_s
        have hroot_split :
            r ≡ 1 [ZMOD (orderOf a : ℤ)] ∨
              r ≡ -1 [ZMOD (orderOf a : ℤ)] ∨
                (3 ≤ M ∧
                  (r ≡ 1 + (2 : ℤ) ^ (M - 1) [ZMOD ((2 : ℤ) ^ M)] ∨
                    r ≡ -1 + (2 : ℤ) ^ (M - 1) [ZMOD ((2 : ℤ) ^ M)])) := by
          have hmodEq_of_dvd_sub {m x y : ℤ} (h : m ∣ x - y) :
              x ≡ y [ZMOD m] := by
            have hz : x - y ≡ 0 [ZMOD m] := Int.modEq_zero_iff_dvd.mpr h
            have h' := hz.add_right y
            convert h' using 1 <;> ring
          have hpow_dvd_consec :
              ∀ {n : ℕ} {x : ℤ}, (2 : ℤ) ^ n ∣ x * (x + 1) →
                (2 : ℤ) ^ n ∣ x ∨ (2 : ℤ) ^ n ∣ x + 1 := by
            intro n x hx
            have hprime2 : Prime (2 : ℤ) := by exact Int.prime_two
            by_cases hx2 : (2 : ℤ) ∣ x
            · left
              have hnot : ¬ (2 : ℤ) ∣ x + 1 := by
                intro hx1
                have htwo_one : (2 : ℤ) ∣ 1 := by
                  have h := dvd_sub hx1 hx2
                  simpa only [add_sub_cancel_left] using h
                norm_num at htwo_one
              have hcop2 : IsCoprime (2 : ℤ) (x + 1) :=
                (hprime2.coprime_iff_not_dvd).mpr hnot
              exact hcop2.pow_left.dvd_of_dvd_mul_right hx
            · right
              have hcop2 : IsCoprime (2 : ℤ) x :=
                (hprime2.coprime_iff_not_dvd).mpr hx2
              exact hcop2.pow_left.dvd_of_dvd_mul_left hx
          have hr_square_pow : r * r ≡ 1 [ZMOD ((2 : ℤ) ^ M)] := by
            simpa [horder_pow_int] using hr_square_mod
          have hsq_dvd : (2 : ℤ) ^ M ∣ r * r - 1 := by
            apply Int.modEq_zero_iff_dvd.mp
            have h := hr_square_pow.sub (Int.ModEq.refl (1 : ℤ))
            simpa using h
          have hprod_dvd : (2 : ℤ) ^ M ∣ (r - 1) * (r + 1) := by
            convert hsq_dvd using 1
            ring
          by_cases hM0 : M = 0
          · left
            subst M
            rw [horder_pow_int]
            norm_num [Int.ModEq]
          have hM_pos : 0 < M := Nat.pos_of_ne_zero hM0
          have htwo_dvd_pow : (2 : ℤ) ∣ (2 : ℤ) ^ M := by
            have hM_eq : M = (M - 1) + 1 := by omega
            rw [hM_eq, pow_succ]
            exact dvd_mul_left _ _
          have htwo_dvd_sq : (2 : ℤ) ∣ r * r - 1 :=
            htwo_dvd_pow.trans hsq_dvd
          have hodd_r : Odd r := by
            rcases Int.even_or_odd r with hr_even | hr_odd
            · have htwo_rr : (2 : ℤ) ∣ r * r := dvd_mul_of_dvd_left (by rw[← even_iff_two_dvd]; exact hr_even) r
              have htwo_one : (2 : ℤ) ∣ 1 := by
                have h := dvd_sub htwo_rr htwo_dvd_sq
                simpa only [sub_sub_cancel] using h
              norm_num at htwo_one
            · exact hr_odd
          rcases hodd_r with ⟨t, ht⟩
          by_cases hM_ge_three : 3 ≤ M
          · have hM_eq2 : M = (M - 2) + 2 := by omega
            have hpow_rewrite :
                (2 : ℤ) ^ M = 4 * (2 : ℤ) ^ (M - 2) := by
              rw [hM_eq2, pow_add]
              norm_num [pow_two]
              ring
            have hprod_rewrite :
                (r - 1) * (r + 1) = 4 * (t * (t + 1)) := by
              rw [ht]
              ring
            have htprod_dvd : (2 : ℤ) ^ (M - 2) ∣ t * (t + 1) := by
              have h4 :
                  4 * (2 : ℤ) ^ (M - 2) ∣ 4 * (t * (t + 1)) := by
                simpa [hpow_rewrite, hprod_rewrite] using hprod_dvd
              exact (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp h4
            have hM_eq1 : M = (M - 1) + 1 := by omega
            have hpowM :
                (2 : ℤ) ^ M = (2 : ℤ) ^ (M - 1) * 2 := by
              rw [hM_eq1, pow_succ]
              simp
            have hlift_minus :
                (2 : ℤ) ^ (M - 1) ∣ r - 1 →
                  r ≡ 1 [ZMOD ((2 : ℤ) ^ M)] ∨
                  r ≡ 1 + (2 : ℤ) ^ (M - 1) [ZMOD ((2 : ℤ) ^ M)] := by
              intro hp
              rcases hp with ⟨q, hq⟩
              rcases Int.even_or_odd q with ⟨u, hu⟩ | ⟨u, hu⟩
              · left
                apply hmodEq_of_dvd_sub
                refine ⟨u, ?_⟩
                calc
                  r - 1 = (2 : ℤ) ^ (M - 1) * q := hq
                  _ = (2 : ℤ) ^ (M - 1) * (2 * u) := by rw [hu]; ring
                  _ = (2 : ℤ) ^ M * u := by rw [hpowM]; ring
              · right
                apply hmodEq_of_dvd_sub
                refine ⟨u, ?_⟩
                calc
                  r - (1 + (2 : ℤ) ^ (M - 1))
                      = (r - 1) - (2 : ℤ) ^ (M - 1) := by ring
                  _ = (2 : ℤ) ^ (M - 1) * q - (2 : ℤ) ^ (M - 1) := by rw [hq]
                  _ = (2 : ℤ) ^ (M - 1) * (2 * u + 1) -
                        (2 : ℤ) ^ (M - 1) := by rw [hu]
                  _ = (2 : ℤ) ^ M * u := by rw [hpowM]; ring

            have hlift_plus :
                (2 : ℤ) ^ (M - 1) ∣ r + 1 →
                  r ≡ -1 [ZMOD ((2 : ℤ) ^ M)] ∨
                  r ≡ -1 + (2 : ℤ) ^ (M - 1) [ZMOD ((2 : ℤ) ^ M)] := by
              intro hp
              rcases hp with ⟨q, hq⟩
              rcases Int.even_or_odd q with ⟨u, hu⟩ | ⟨u, hu⟩
              · left
                apply hmodEq_of_dvd_sub
                refine ⟨u, ?_⟩
                calc
                  r - (-1 : ℤ) = r + 1 := by ring
                  _ = (2 : ℤ) ^ (M - 1) * q := hq
                  _ = (2 : ℤ) ^ (M - 1) * (2 * u) := by rw [hu]; ring
                  _ = (2 : ℤ) ^ M * u := by rw [hpowM]; ring
              · right
                apply hmodEq_of_dvd_sub
                refine ⟨u, ?_⟩
                calc
                  r - (-1 + (2 : ℤ) ^ (M - 1))
                      = (r + 1) - (2 : ℤ) ^ (M - 1) := by ring
                  _ = (2 : ℤ) ^ (M - 1) * q - (2 : ℤ) ^ (M - 1) := by rw [hq]
                  _ = (2 : ℤ) ^ (M - 1) * (2 * u + 1) -
                        (2 : ℤ) ^ (M - 1) := by rw [hu]
                  _ = (2 : ℤ) ^ M * u := by rw [hpowM]; ring
            rcases hpow_dvd_consec htprod_dvd with ht_dvd | ht1_dvd
            · have hp : (2 : ℤ) ^ (M - 1) ∣ r - 1 := by
                have hM1 : M - 1 = (M - 2) + 1 := by omega
                have hmul : (2 : ℤ) * (2 : ℤ) ^ (M - 2) ∣ 2 * t :=
                  mul_dvd_mul_left (2 : ℤ) ht_dvd
                rw [ht]
                simpa [hM1, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hmul
              rcases hlift_minus hp with h1 | hmid
              · left
                simpa [horder_pow_int] using h1
              · right
                right
                exact ⟨hM_ge_three, Or.inl hmid⟩
            · have hp : (2 : ℤ) ^ (M - 1) ∣ r + 1 := by
                have hM1 : M - 1 = (M - 2) + 1 := by omega
                have hmul :
                    (2 : ℤ) * (2 : ℤ) ^ (M - 2) ∣ 2 * (t + 1) :=
                  mul_dvd_mul_left (2 : ℤ) ht1_dvd
                rw [ht, show 2 * t + 1 + 1 = 2 * (t + 1) by ring]
                simpa [hM1, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hmul
              rcases hlift_plus hp with hneg | hmid
              · right
                left
                simpa [horder_pow_int] using hneg
              · right
                right
                exact ⟨hM_ge_three, Or.inr hmid⟩
          · have hM_le_two : M ≤ 2 := by omega
            interval_cases M
            · -- M = 1
              left
              rw [horder_pow_int]
              norm_num
              apply hmodEq_of_dvd_sub
              refine ⟨t, ?_⟩
              rw [ht]
              ring
            · -- M = 2
              rcases Int.even_or_odd t with ⟨u, hu⟩ | ⟨u, hu⟩
              · left
                rw [horder_pow_int]
                norm_num
                apply hmodEq_of_dvd_sub
                refine ⟨u, ?_⟩
                rw [ht, hu]
                ring
              · right
                left
                rw [horder_pow_int]
                norm_num
                apply hmodEq_of_dvd_sub
                refine ⟨u + 1, ?_⟩
                rw [ht, hu]
                ring
        rcases hroot_split with hr_one | hr_neg | hmid
        · exact Or.inl (hcyclic_of_r_one hr_one)
        · exact False.elim (hr_not_flip' hr_neg)
        · rcases hmid with ⟨hM_ge_three, hr_mid_pos | hr_mid_neg⟩
          · exact Or.inr (hlinear_solution_of_nontrivial_root hM_ge_three (Or.inl hr_mid_pos))
          · exact Or.inr (hlinear_solution_of_nontrivial_root hM_ge_three (Or.inr hr_mid_neg))
      rcases hcore with hcycle | hex
      · exact hcycle
      · exact False.elim (hbad hex)
    exact hnonflip_forces_cyclic hr_not_flip
  have hconj_a_inv_zpow : ∀ z : ℤ, b * a ^ z * b⁻¹ = a ^ (-z) := by
    intro z
    calc
      b * a ^ z * b⁻¹ = a ^ (r * z) := hconj_a_zpow z
      _ = a ^ ((-1 : ℤ) * z) := by
        apply (zpow_eq_zpow_iff_modEq (x := a)).2
        exact hflip_mod.mul_right z
      _ = a ^ (-z) := by ring_nf
  have hconj : ∀ z : ℤ, a ^ z * b = b * a ^ (-z) := by
    intro z
    have hz : b * a ^ (-z) * b⁻¹ = a ^ z := by
      simpa using hconj_a_inv_zpow (-z)
    calc
      a ^ z * b = (b * a ^ (-z) * b⁻¹) * b := by rw [hz]
      _ = b * a ^ (-z) := by group
  exact hconj

private theorem huppert_III_7_6b_isCyclic_of_isMulCommutative_unique_order_two
    {G : Type u} [Group G] [Finite G] (hGp : IsPGroup 2 G)
    (hunique : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x = y)
    (A : Subgroup G) (hAcomm : IsMulCommutative A) : IsCyclic A := by
  let : IsMulCommutative A := hAcomm
  by_cases hA : A = ⊥
  · subst A
    infer_instance
  · exact (hGp.to_subgroup A).isCyclic_of_unique_involution_of_isMulCommutative
      (hGp.existsUnique_involution_subgroup hunique A hA)

private theorem huppert_III_7_5b_abelian_branch
    {G : Type u} [Group G] [Finite G] (hGp : IsPGroup 2 G) (N : Subgroup G)
    (hNnorm : N.Normal) (hNcomm : IsMulCommutative N) (hN_noncyclic : ¬ IsCyclic N) :
    ∃ K : Subgroup G, K.Normal ∧ K ≤ N ∧ Nat.card K = 2 ^ 2 ∧ IsElementaryAbelian 2 K := by
  let : N.Normal := hNnorm
  let : IsMulCommutative N := hNcomm
  obtain ⟨K, hKn, hKN, hKe, hKcard⟩ :=
    hGp.exists_normal_four_of_normal_abelian_not_cyclic N hN_noncyclic
  exact ⟨K, hKn, hKN, by simpa using hKcard, hKe⟩

private theorem commutative_of_cyclic_central_quotient
    {G : Type*} [Group G] (hcyc : IsCyclic (G ⧸ Subgroup.center G)) :
    IsMulCommutative G := by
  let : IsCyclic (G ⧸ Subgroup.center G) := hcyc
  exact (QuotientGroup.mk' (Subgroup.center G)).isMulCommutative_of_isCyclic_of_ker_le_center
    (by simp [QuotientGroup.ker_mk'])

private theorem huppert_III_7_5b_cyclic_quotient_branch
    {G : Type u} [Group G] [Finite G]
    (hGp : IsPGroup 2 G) (N Z : Subgroup G)
    (hNnorm : N.Normal) (hN_noncyclic : ¬ IsCyclic N)
    (hZnorm : Z.Normal) (hZ_le_center : Z ≤ Subgroup.center G)
    (hNbar_cyclic : IsCyclic (N.map (QuotientGroup.mk' Z))) :
    ∃ K : Subgroup G, K.Normal ∧ K ≤ N ∧ Nat.card K = 2 ^ 2 ∧ IsElementaryAbelian 2 K := by
  classical
  have : Z.Normal := hZnorm
  let q : G →* G ⧸ Z := QuotientGroup.mk' Z
  let Nbar : Subgroup (G ⧸ Z) := N.map q
  let qN : N →* Nbar := q.subgroupMap N
  have hqN_surj : Function.Surjective qN := MonoidHom.subgroupMap_surjective q N
  have hqN_range_cyclic : IsCyclic qN.range := by
    let : IsCyclic Nbar := by simpa [Nbar, q] using hNbar_cyclic
    exact Subgroup.isCyclic_of_le le_top
  have hquot_ker_cyclic : IsCyclic (N ⧸ qN.ker) :=
    (MulEquiv.isCyclic (QuotientGroup.quotientKerEquivRange qN)).2 hqN_range_cyclic
  have hker_le_centerN : qN.ker ≤ Subgroup.center N := by
    intro z hz
    have hzq : q ((z : N) : G) = 1 := by
      have hzqN : qN z = 1 := MonoidHom.mem_ker.mp hz
      exact congrArg Subtype.val hzqN
    have hzZ : ((z : N) : G) ∈ Z :=
      (QuotientGroup.eq_one_iff (N := Z) (x := ((z : N) : G))).1 (by simpa [q] using hzq)
    have hzcenter : ((z : N) : G) ∈ Subgroup.center G := hZ_le_center hzZ
    rw [Subgroup.mem_center_iff]
    intro n
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp hzcenter) (n : G)
  let π : N ⧸ qN.ker →* N ⧸ Subgroup.center N :=
    QuotientGroup.map qN.ker (Subgroup.center N) (MonoidHom.id N) (by simpa using hker_le_centerN)
  have hπ_surj : Function.Surjective π := by
    intro y
    refine Quotient.inductionOn' y ?_
    intro n
    exact ⟨(QuotientGroup.mk' qN.ker n), rfl⟩
  have hcenter_quot_cyclic : IsCyclic (N ⧸ Subgroup.center N) := by
    let : IsCyclic (N ⧸ qN.ker) := hquot_ker_cyclic
    exact isCyclic_of_surjective π hπ_surj
  have hNcomm : IsMulCommutative N := commutative_of_cyclic_central_quotient (G := N) hcenter_quot_cyclic
  exact huppert_III_7_5b_abelian_branch (G := G) hGp N hNnorm hNcomm hN_noncyclic
/-- In a finite `p`-group, a subgroup of prime index is maximal and normal. -/
private theorem huppert_III_7_5b_covby_top_of_index_eq_prime
    {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [Finite G]
    (h : IsPGroup p G) {H : Subgroup G} (h_idx : H.index = p) :
    CovBy H ⊤ ∧ H.Normal := by
  have hp : p.Prime := Fact.out
  have (a b : Prop) : a ∧ b ↔ a ∧ (a → b) := by tauto
  rw [this]
  constructor
  · refine ⟨Ne.lt_top (fun htop => ?_), fun K hHK hKtop => ?_⟩
    · have hp_one : p = 1 := by
        simpa [htop] using h_idx.symm
      exact hp.ne_one hp_one
    · have hrel := Subgroup.relIndex_mul_index hHK.le
      have hprime : (H.relIndex K * K.index).Prime := by rwa [hrel, h_idx]
      rcases Nat.prime_mul_iff.mp hprime with ⟨_, hindex_one⟩ | ⟨_, hrel_one⟩
      · rw [Subgroup.index_eq_one] at hindex_one
        simp [hindex_one] at hKtop
      · rw [Subgroup.relIndex_eq_one] at hrel_one
        exact hHK.not_ge hrel_one
  · intro hmax
    simp only [covBy_top_iff] at hmax
    have hnil : Group.IsNilpotent G := IsPGroup.isNilpotent (p := p) h
    exact Subgroup.NormalizerCondition.normal_of_coatom H
      (Group.normalizerCondition_of_isNilpotent (G := G)) hmax

/-- In a finite `2`-group, any subgroup whose index divides `2` contains the Frattini subgroup. -/
private theorem huppert_III_7_5b_frattini_le_of_index_dvd_two
    {G : Type u} [Group G] [Finite G] (hGp : IsPGroup 2 G)
    {H : Subgroup G} (hidx : H.index ∣ 2) :
    frattini G ≤ H := by
  have hidx_ne_zero : H.index ≠ 0 := by
    intro hzero
    simp [hzero] at hidx
  have hidx_cases : H.index = 1 ∨ H.index = 2 := by
    have hle : H.index ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hidx
    omega
  rcases hidx_cases with hidx_one | hidx_two
  · have htop : H = ⊤ := (Subgroup.index_eq_one).1 hidx_one
    intro x hx
    simp [htop]
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcov :=
      huppert_III_7_5b_covby_top_of_index_eq_prime (p := 2) (G := G) hGp hidx_two
    exact frattini_le_coatom (by simpa [covBy_top_iff] using hcov.1)
/-- The final order-eight branch in Huppert III.7.5(b).  This is the point where
Huppert uses the Frattini condition: a noncommutative lifted subgroup of order
`8` cannot force every normal subgroup of order `4` to be cyclic. -/
private theorem huppert_III_7_5b_noncomm_order_eight_branch
    {G : Type u} [Group G] [Finite G]
    (hGp : IsPGroup 2 G) (M N : Subgroup G)
    (hMnorm : M.Normal) (hM_le_N : M ≤ N) (hM_le_phi : M ≤ frattini G)
    (hMcard : Nat.card M = 2 ^ 3) (hMnoncomm : ¬ IsMulCommutative M) :
    ∃ K : Subgroup G, K.Normal ∧ K ≤ N ∧ Nat.card K = 2 ^ 2 ∧ IsElementaryAbelian 2 K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 G) := ⟨hGp⟩
  obtain ⟨L, hL_normal, hL_le_M, hL_card⟩ :=
    exists_normal_subgroup_card_pow_of_normal (G := G) (p := 2)
      (N := M) hMnorm hMcard 2 (by norm_num : 2 ≤ 3)
  by_cases hL_elem : IsElementaryAbelian 2 L
  · exact ⟨L, hL_normal, hL_le_M.trans hM_le_N, hL_card, hL_elem⟩
  · have hL_comm : IsMulCommutative L :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (G := L) hL_card
    have hL_cyclic : IsCyclic L := by
      by_contra hL_not_cyclic
      have hL_exp : Monoid.exponent L = 2 :=
        (not_isCyclic_iff_exponent_eq_prime (p := 2) Nat.prime_two hL_card).1
          hL_not_cyclic
      have hL_elem' : IsElementaryAbelian 2 L :=
        { toIsMulCommutative := hL_comm
          exponent_dvd_p := by simp [hL_exp] }
      exact hL_elem hL_elem'
    let : L.Normal := hL_normal
    let : IsCyclic L := hL_cyclic
    let φ : G →* MulAut L := MulAut.conjNormal (H := L)
    have hAutL_card : Nat.card (MulAut L) = 2 := by
      rw [IsCyclic.card_mulAut, hL_card,
        Nat.totient_prime_pow Nat.prime_two (by norm_num : 0 < 2)]
      norm_num
    have hker_index_dvd_two : φ.ker.index ∣ 2 := by
      rw [Subgroup.index_ker]
      simpa [hAutL_card] using (Subgroup.card_subgroup_dvd_card φ.range)
    have hPhi_le_ker : frattini G ≤ φ.ker :=
      huppert_III_7_5b_frattini_le_of_index_dvd_two (G := G) hGp hker_index_dvd_two
    have hM_le_ker : M ≤ φ.ker := hM_le_phi.trans hPhi_le_ker
    let LM : Subgroup M := L.subgroupOf M
    have hLM_le_center : LM ≤ Subgroup.center M := by
      intro l hl
      rw [Subgroup.mem_center_iff]
      intro m
      apply Subtype.ext
      have hlL : ((l : M) : G) ∈ L := by
        simpa [LM, Subgroup.mem_subgroupOf] using hl
      have hmker : (m : G) ∈ φ.ker := hM_le_ker m.property
      have hfix :
          MulAut.conjNormal (H := L) (m : G) ⟨((l : M) : G), hlL⟩ =
            ⟨((l : M) : G), hlL⟩ := by
        have hφm : φ (m : G) = 1 := MonoidHom.mem_ker.mp hmker
        simp [φ, hφm]
      have hconj : (m : G) * ((l : M) : G) * (m : G)⁻¹ = ((l : M) : G) := by
        simpa [MulAut.conjNormal_apply, MulAut.conj_apply] using congrArg Subtype.val hfix
      have hcommG : (m : G) * ((l : M) : G) = ((l : M) : G) * (m : G) := by
        calc
          (m : G) * ((l : M) : G) =
              ((m : G) * ((l : M) : G) * (m : G)⁻¹) * (m : G) := by
                simp [mul_assoc]
          _ = ((l : M) : G) * (m : G) := by rw [hconj]
      simpa using hcommG
    have : LM.Normal := by
      simpa [LM] using (inferInstance : (L.subgroupOf M).Normal)
    have hLM_card_eq : Nat.card LM = Nat.card L := by
      simpa [LM] using Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL_le_M).toEquiv
    have hLM_card : Nat.card LM = 2 ^ 2 := hLM_card_eq.trans hL_card
    have hM_quot_LM_card : Nat.card (M ⧸ LM) = 2 := by
      have hmul := (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := LM)).symm
      rw [hLM_card, hMcard] at hmul
      have hmul' : Nat.card (M ⧸ LM) * (2 ^ 2) = 2 * (2 ^ 2) := by
        norm_num at hmul ⊢
        exact hmul
      exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2 ^ 2) hmul'
    have hM_quot_LM_cyclic : IsCyclic (M ⧸ LM) :=
      isCyclic_of_prime_card (α := M ⧸ LM) (p := 2) (by simpa using hM_quot_LM_card)
    let π : M ⧸ LM →* M ⧸ Subgroup.center M :=
      QuotientGroup.map LM (Subgroup.center M) (MonoidHom.id M) (by simpa using hLM_le_center)
    have hπ_surj : Function.Surjective π := by
      intro y
      refine Quotient.inductionOn' y ?_
      intro m
      exact ⟨QuotientGroup.mk' LM m, rfl⟩
    have hcenter_quot_cyclic : IsCyclic (M ⧸ Subgroup.center M) := by
      let : IsCyclic (M ⧸ LM) := hM_quot_LM_cyclic
      exact isCyclic_of_surjective π hπ_surj
    have hM_comm : IsMulCommutative M := commutative_of_cyclic_central_quotient (G := M) hcenter_quot_cyclic
    exact False.elim (hMnoncomm hM_comm)

/-- Huppert III.7.5(b), for a normal noncyclic subgroup contained in the Frattini subgroup. -/
private theorem huppert_III_7_5b_exists_normal_elementaryAbelian_order_four_of_noncyclic_frattini_aux
    {G : Type u} [Group G] [Finite G]
    (hGp : IsPGroup 2 G) (N : Subgroup G)
    (hNnorm : N.Normal) (hN_le_phi : N ≤ frattini G)
    (hN_noncyclic : ¬ IsCyclic N) :
    ∃ K : Subgroup G, K.Normal ∧ K ≤ N ∧ Nat.card K = 2 ^ 2 ∧ IsElementaryAbelian 2 K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let rec aux {S : Type u} [Group S] [Finite S] [Fact (IsPGroup 2 S)]
      (N : Subgroup S) (hNnorm : N.Normal) (hN_le_phi : N ≤ frattini S)
      (hN_noncyclic : ¬ IsCyclic N) :
      ∃ K : Subgroup S, K.Normal ∧ K ≤ N ∧ Nat.card K = 2 ^ 2 ∧ IsElementaryAbelian 2 K := by
    have hSp : IsPGroup 2 S := Fact.out
    let : N.Normal := hNnorm
    have hN_nontrivial : Nontrivial N := Nontrivial.of_not_isCyclic hN_noncyclic
    obtain ⟨Z, hZ_normal, hZ_le_N, hZ_card, hZ_le_center⟩ :=
      exists_central_subgroup_card_eq_prime_in_normal
        (G := S) (p := 2) N hN_nontrivial
    let : Z.Normal := hZ_normal
    let q : S →* S ⧸ Z := QuotientGroup.mk' Z
    let Nbar : Subgroup (S ⧸ Z) := N.map q
    have hNbar_normal : Nbar.Normal := by
      simpa [Nbar, q] using (QuotientGroup.map_normal Z N)
    let : Nbar.Normal := hNbar_normal
    have hNbar_le_phi : Nbar ≤ frattini (S ⧸ Z) := by
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨n, hnN, rfl⟩
      have hphi_le_comap : frattini S ≤ (frattini (S ⧸ Z)).comap q :=
        frattini_le_comap_frattini_of_surjective (G := S) (H := S ⧸ Z) (φ := q)
          (QuotientGroup.mk'_surjective Z)
      exact hphi_le_comap (hN_le_phi hnN)
    by_cases hNbar_cyclic : IsCyclic Nbar
    · exact
        huppert_III_7_5b_cyclic_quotient_branch (G := S) hSp N Z hNnorm hN_noncyclic
          hZ_normal hZ_le_center (by simpa [Nbar, q] using hNbar_cyclic)
    · have hQ_card : Nat.card S = Nat.card (S ⧸ Z) * 2 := by
        calc
          Nat.card S = Nat.card (S ⧸ Z) * Nat.card Z := by
            simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := S) (s := Z))
          _ = Nat.card (S ⧸ Z) * 2 := by rw [hZ_card]
      have hQ_lt : Nat.card (S ⧸ Z) < Nat.card S := by
        rw [hQ_card]
        have hlt := Nat.mul_lt_mul_of_pos_left (by decide : 1 < 2)
          (Nat.card_pos (α := S ⧸ Z))
        rw [mul_one] at hlt
        exact hlt
      have hQp : IsPGroup 2 (S ⧸ Z) := hSp.to_quotient Z
      let : Fact (IsPGroup 2 (S ⧸ Z)) := ⟨hQp⟩
      obtain ⟨Kbar, hKbar_normal, hKbar_le_Nbar, hKbar_card, hKbar_elem⟩ :=
        aux (S := S ⧸ Z) Nbar hNbar_normal hNbar_le_phi hNbar_cyclic
      let : Kbar.Normal := hKbar_normal
      let M : Subgroup S := Kbar.comap q
      have hM_normal : M.Normal := by
        simpa [M, q] using (inferInstance : (Kbar.comap (QuotientGroup.mk' Z)).Normal)
      let : M.Normal := hM_normal
      have hker_le_N : q.ker ≤ N := by
        simpa [q, QuotientGroup.ker_mk'] using hZ_le_N
      have hNbar_comap_eq : Nbar.comap q = N := by
        simpa [Nbar] using (Subgroup.comap_map_eq_self (f := q) (H := N) hker_le_N)
      have hM_le_N : M ≤ N := by
        have hcomap_le : Kbar.comap q ≤ Nbar.comap q := Subgroup.comap_mono hKbar_le_Nbar
        simpa [M, hNbar_comap_eq] using hcomap_le
      have hM_le_phi : M ≤ frattini S := hM_le_N.trans hN_le_phi
      have hM_card : Nat.card M = 2 ^ 3 := by
        have hcardQuotM : Nat.card (M ⧸ q.ker.subgroupOf M) = Nat.card Kbar := by
          simpa [M] using
            (card_quotient_subgroupOf_comap_eq (f := q) (hf := QuotientGroup.mk'_surjective Z)
              (H := Kbar))
        have hcardKerSub : Nat.card (q.ker.subgroupOf M) = Nat.card Z := by
          have hcardKerSub' : Nat.card (q.ker.subgroupOf M) = Nat.card q.ker := by
            exact Nat.card_congr
              (Subgroup.subgroupOfEquivOfLe (Subgroup.ker_le_comap (f := q) (H := Kbar))).toEquiv
          rw [hcardKerSub']
          simp [q, QuotientGroup.ker_mk']
        calc
          Nat.card M = Nat.card (M ⧸ q.ker.subgroupOf M) * Nat.card (q.ker.subgroupOf M) := by
            simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := q.ker.subgroupOf M))
          _ = 2 ^ 2 * 2 := by rw [hcardQuotM, hcardKerSub, hKbar_card, hZ_card]
          _ = 2 ^ 3 := by ring_nf
      have hM_noncyclic : ¬ IsCyclic M := by
        intro hMcyclic
        have hMmap_cyclic : IsCyclic (M.map q) := by
          let : IsCyclic M := hMcyclic
          exact isCyclic_of_surjective (q.subgroupMap M) (MonoidHom.subgroupMap_surjective q M)
        have hMmap_eq : M.map q = Kbar := by
          simpa [M] using
            (Subgroup.map_comap_eq_self_of_surjective (f := q) (h := QuotientGroup.mk'_surjective Z)
              Kbar)
        have hKbar_cyclic : IsCyclic Kbar := by
          rw [← hMmap_eq]
          exact hMmap_cyclic
        have : IsElementaryAbelian 2 Kbar := hKbar_elem
        exact (IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := 2) (A := Kbar) hKbar_card)
          hKbar_cyclic
      by_cases hMcomm : IsMulCommutative M
      · obtain ⟨K, hK_normal, hK_le_M, hK_card, hK_elem⟩ :=
          huppert_III_7_5b_abelian_branch (G := S) hSp M hM_normal hMcomm hM_noncyclic
        exact ⟨K, hK_normal, hK_le_M.trans hM_le_N, hK_card, hK_elem⟩
      · exact
          huppert_III_7_5b_noncomm_order_eight_branch (G := S) hSp M N hM_normal hM_le_N
            hM_le_phi hM_card hMcomm
  termination_by Nat.card S
  decreasing_by
    exact hQ_lt
  have : Fact (IsPGroup 2 G) := ⟨hGp⟩
  exact aux (S := G) N hNnorm hN_le_phi hN_noncyclic

/-- Huppert III.7.5(b), in the only form needed for III.7.6(b). -/
private theorem huppert_III_7_5b_exists_normal_elementaryAbelian_order_four_of_noncyclic_frattini
    {G : Type u} [Group G] [Finite G]
    (hGp : IsPGroup 2 G) (hPhi_noncyclic : ¬ IsCyclic (frattini G)) :
    ∃ K : Subgroup G,
      K.Normal ∧ K ≤ frattini G ∧ Nat.card K = 2 ^ 2 ∧ IsElementaryAbelian 2 K := by
  classical
  exact
    huppert_III_7_5b_exists_normal_elementaryAbelian_order_four_of_noncyclic_frattini_aux
      (G := G) hGp (frattini G) inferInstance le_rfl hPhi_noncyclic

/-- Huppert III.7.5(b), in the only form needed for III.7.6(b). -/
private theorem huppert_III_7_6b_frattini_isCyclic_of_unique_order_two
    {G : Type u} [Group G] [Finite G]
    (hGp : IsPGroup 2 G)
    (hunique_order_two : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x = y) :
    IsCyclic (frattini G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hPhi_noncyclic
  obtain ⟨K, _hK_normal, _hK_le_phi, hKcard, hKelem⟩ :=
    huppert_III_7_5b_exists_normal_elementaryAbelian_order_four_of_noncyclic_frattini
      (G := G) hGp hPhi_noncyclic
  have : IsElementaryAbelian 2 K := hKelem
  have hK_cyclic : IsCyclic K :=
    huppert_III_7_6b_isCyclic_of_isMulCommutative_unique_order_two
      (G := G) hGp hunique_order_two K hKelem.toIsMulCommutative
  exact (IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := 2) (A := K) hKcard) hK_cyclic
private theorem huppert_III_7_6b_index_eq_two_of_maximal_normal_abelian
    {G : Type u} [Group G] [Finite G]
    (hGp : IsPGroup 2 G)
    (hnot_cyclic : ¬ IsCyclic G)
    (hunique_order_two : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x = y)
    (A : Subgroup G)
    (hPhi_le_A : frattini G ≤ A)
    (hAnorm : A.Normal)
    (hAcomm : IsMulCommutative A)
    (hAmax : ∀ B : Subgroup G, B.Normal → IsMulCommutative B → A ≤ B → B = A)
    (hAcent_le : Subgroup.centralizer (A : Set G) ≤ A) :
    A.index = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 G) := ⟨hGp⟩
  let : A.Normal := hAnorm
  have hA_cyclic : IsCyclic A :=
    huppert_III_7_6b_isCyclic_of_isMulCommutative_unique_order_two
      (G := G) hGp hunique_order_two A hAcomm
  have hA_le_cent : A ≤ Subgroup.centralizer (A : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hAcomm
  have hAcent_eq : Subgroup.centralizer (A : Set G) = A :=
    le_antisymm hAcent_le hA_le_cent
  have hquot_elem : IsElementaryAbelian 2 (G ⧸ A) := by
    refine
      { toIsMulCommutative := ?_
        exponent_dvd_p := ?_ }
    · have hcomm_le : _root_.commutator G ≤ A :=
        (commutator_le_frattini_of_isPGroup (R := G) (p := 2)).trans hPhi_le_A
      exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := A)).2 hcomm_le
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
      intro x
      refine QuotientGroup.induction_on x ?_
      intro g
      have hgpow : g ^ 2 ∈ A :=
        hPhi_le_A (pth_power_mem_frattini_of_isPGroup (R := G) (p := 2) g)
      exact (QuotientGroup.eq_one_iff (N := A) (x := g ^ 2)).2 (by simpa using hgpow)
  let : IsElementaryAbelian 2 (G ⧸ A) := hquot_elem
  by_cases hquot_cyclic : IsCyclic (G ⧸ A)
  · have hquot_not_subsingleton : ¬ Subsingleton (G ⧸ A) := by
      intro hsub
      have hAtop : A = ⊤ := (QuotientGroup.subsingleton_iff (N := A)).1 hsub
      have htop_cyclic : IsCyclic (⊤ : Subgroup G) := by
        rw [← hAtop]
        exact hA_cyclic
      exact hnot_cyclic ((Subgroup.topEquiv (G := G)).isCyclic.mp htop_cyclic)
    have hcard_dvd_two : Nat.card (G ⧸ A) ∣ 2 := by
      simpa [hquot_cyclic.exponent_eq_card] using
        (IsElementaryAbelian.exponent_dvd_p 2 (G ⧸ A))
    have hcard_ne_one : Nat.card (G ⧸ A) ≠ 1 := by
      intro hcard_one
      have hsub : Subsingleton (G ⧸ A) := (Nat.card_eq_one_iff_unique.mp hcard_one).1
      exact hquot_not_subsingleton hsub
    have hcard_eq_two : Nat.card (G ⧸ A) = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hcard_dvd_two with h | h
      · exact False.elim (hcard_ne_one h)
      · exact h
    simpa [Subgroup.index_eq_card] using hcard_eq_two
  · have hquot_not_subsingleton : ¬ Subsingleton (G ⧸ A) := by
      intro hsub
      have hAtop : A = ⊤ := (QuotientGroup.subsingleton_iff (N := A)).1 hsub
      have htop_cyclic : IsCyclic (⊤ : Subgroup G) := by
        rw [← hAtop]
        exact hA_cyclic
      exact hnot_cyclic ((Subgroup.topEquiv (G := G)).isCyclic.mp htop_cyclic)
    obtain ⟨aA, haA_top⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := A)).1 hA_cyclic
    let a : G := (aA : G)
    have ha_zpowers : Subgroup.zpowers a = A := by
      ext x
      constructor
      · intro hx
        rcases Subgroup.mem_zpowers_iff.mp hx with ⟨z, hz⟩
        rw [← hz]
        exact A.zpow_mem aA.property z
      · intro hxA
        have hxA_top : (⟨x, hxA⟩ : A) ∈ (⊤ : Subgroup A) := by simp
        have hxA_zpow : (⟨x, hxA⟩ : A) ∈ Subgroup.zpowers aA := by
          rw [haA_top]
          exact hxA_top
        rcases Subgroup.mem_zpowers_iff.mp hxA_zpow with ⟨z, hz⟩
        refine Subgroup.mem_zpowers_iff.mpr ⟨z, ?_⟩
        exact Subtype.ext_iff.mp hz
    have hA_ne_bot : A ≠ ⊥ := by
      intro hAbot
      have hAtop : A = ⊤ := by
        apply eq_top_iff.2
        intro g _hg
        apply hAcent_le
        rw [Subgroup.mem_centralizer_iff]
        intro x hxA
        have hx_one : x = 1 := by
          have hxbot : x ∈ (⊥ : Subgroup G) := by simpa [hAbot] using hxA
          simpa using hxbot
        simp [hx_one]
      have htop_cyclic : IsCyclic (⊤ : Subgroup G) := by
        rw [← hAtop]
        exact hA_cyclic
      exact hnot_cyclic ((Subgroup.topEquiv (G := G)).isCyclic.mp htop_cyclic)
    have hA_card_ne_one : Nat.card A ≠ 1 := by
      intro hcard_one
      exact hA_ne_bot (Subgroup.card_eq_one.mp hcard_one)
    have hAp : IsPGroup 2 A := hGp.to_subgroup A
    obtain ⟨nA, hA_card_pow⟩ := hAp.exists_card_eq
    have hnA_ne_zero : nA ≠ 0 := by
      intro hnA0
      exact hA_card_ne_one (by simpa [hnA0] using hA_card_pow)
    let k : ℕ := 2 ^ (nA - 1)
    have : NeZero k := ⟨pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)⟩
    have hA_card_two_mul : Nat.card A = 2 * k := by
      have hnA : nA = (nA - 1) + 1 := by omega
      calc
        Nat.card A = 2 ^ nA := hA_card_pow
        _ = 2 ^ ((nA - 1) + 1) := congrArg (fun m : ℕ => 2 ^ m) hnA
        _ = 2 ^ (nA - 1) * 2 := by rw [pow_succ]
        _ = k * 2 := by rfl
        _ = 2 * k := by ring
    have ha_order_G : orderOf a = 2 * k := by
      calc
        orderOf a = Nat.card (Subgroup.zpowers a) := (Nat.card_zpowers a).symm
        _ = Nat.card A := by rw [ha_zpowers]
        _ = 2 * k := hA_card_two_mul
    let π : G →* G ⧸ A := QuotientGroup.mk' A
    have hinverts_of_quot_order_two :
        ∀ q : G ⧸ A, orderOf q = 2 → ∀ b : G, π b = q →
          ∀ z : ℤ, a ^ z * b = b * a ^ (-z) := by
      intro q hq_order b hbq
      let Bbar : Subgroup (G ⧸ A) := Subgroup.zpowers q
      let B : Subgroup G := Bbar.comap π
      have hBbar_normal : Bbar.Normal := by
        let : IsMulCommutative (G ⧸ A) := hquot_elem.toIsMulCommutative
        infer_instance
      have hB_normal : B.Normal := by
        dsimp [B]
        exact hBbar_normal.comap π
      let : B.Normal := hB_normal
      have hA_le_B : A ≤ B := by
        intro g hgA
        change π g ∈ Bbar
        have hπg : π g = 1 := (QuotientGroup.eq_one_iff (N := A) (x := g)).2 hgA
        simp [Bbar, hπg]
      let A_B : Subgroup B := A.subgroupOf B
      have hA_B_normal : A_B.Normal := by
        dsimp [A_B]
        exact Subgroup.Normal.subgroupOf hAnorm B
      let : A_B.Normal := hA_B_normal
      let aB : B := ⟨a, hA_le_B (by rw [← ha_zpowers]; exact Subgroup.mem_zpowers a)⟩
      have hA_B_eq : Subgroup.zpowers aB = A_B := by
        ext x
        constructor
        · intro hx
          rcases Subgroup.mem_zpowers_iff.mp hx with ⟨z, hz⟩
          change ((x : B) : G) ∈ A
          rw [← ha_zpowers]
          refine Subgroup.mem_zpowers_iff.mpr ⟨z, ?_⟩
          exact congrArg (fun y : B => (y : G)) hz
        · intro hxA
          change ((x : B) : G) ∈ A at hxA
          rw [← ha_zpowers] at hxA
          rcases Subgroup.mem_zpowers_iff.mp hxA with ⟨z, hz⟩
          refine Subgroup.mem_zpowers_iff.mpr ⟨z, ?_⟩
          apply Subtype.ext
          exact hz
      have hBbar_card : Nat.card Bbar = 2 := by
        simpa [Bbar, Nat.card_zpowers] using hq_order
      have hker_sub_eq : π.ker.subgroupOf B = A_B := by
        ext x
        change ((x : B) : G) ∈ π.ker ↔ ((x : B) : G) ∈ A
        simp [π]
      have hA_B_index : A_B.index = 2 := by
        calc
          A_B.index = Nat.card (B ⧸ A_B) := Subgroup.index_eq_card A_B
          _ = Nat.card (B ⧸ π.ker.subgroupOf B) := by rw [hker_sub_eq]
          _ = Nat.card Bbar := card_quotient_subgroupOf_comap_eq (f := π)
              (hf := QuotientGroup.mk'_surjective A) (H := Bbar)
          _ = 2 := hBbar_card
      have hq_ne_one : q ≠ 1 := by
        intro hq1
        have : orderOf q = 1 := orderOf_eq_one_iff.mpr hq1
        omega
      have hb_not_A : b ∉ A := by
        intro hbA
        have hb_one : π b = 1 := (QuotientGroup.eq_one_iff (N := A) (x := b)).2 hbA
        rw [hbq] at hb_one
        exact hq_ne_one hb_one
      have hbB : b ∈ B := by
        change π b ∈ Bbar
        rw [hbq]
        exact Subgroup.mem_zpowers q
      let bB : B := ⟨b, hbB⟩
      have hbB_not_A_B : bB ∉ A_B := by
        intro hbA
        exact hb_not_A hbA
      have hA_B_card : Nat.card A_B = Nat.card A := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_le_B).toEquiv
      have hB_card : Nat.card B = 4 * k := by
        calc
          Nat.card B = Nat.card A_B * A_B.index := (Subgroup.card_mul_index A_B).symm
          _ = Nat.card A * 2 := by rw [hA_B_card, hA_B_index]
          _ = (2 * k) * 2 := by rw [hA_card_two_mul]
          _ = 4 * k := by ring
      have haB_order : orderOf aB = 2 * k := by
        simpa [aB, a, Subgroup.orderOf_coe] using ha_order_G
      have hB_not_cyclic : ¬ IsCyclic B := by
        intro hBcyclic
        have hBcomm : IsMulCommutative B := by
          let : IsCyclic B := hBcyclic
          let : CommGroup B := hBcyclic.commGroup
          infer_instance
        have hB_eq_A : B = A := hAmax B hB_normal hBcomm hA_le_B
        have hA_B_top : A_B = ⊤ := by
          apply eq_top_iff.2
          intro x _hx
          change ((x : B) : G) ∈ A
          rw [← hB_eq_A]
          exact x.property
        have hindex_one : A_B.index = 1 := by
          rw [hA_B_top]
          simp
        have : (2 : ℕ) = 1 := hA_B_index.symm.trans hindex_one
        norm_num at this
      have hunique_B : ∀ x y : B, orderOf x = 2 → orderOf y = 2 → x = y := by
        intro x y hx hy
        apply Subtype.ext
        exact hunique_order_two (x : G) (y : G)
          (by simpa [Subgroup.orderOf_coe] using hx)
          (by simpa [Subgroup.orderOf_coe] using hy)
      have hBinv :=
        huppert_I_14_9_conj_inverts_of_cyclic_index_two
          (G := B) (k := k) A_B aB bB hA_B_eq hA_B_index haB_order
          hbB_not_A_B hunique_B hB_not_cyclic hB_card (hGp.to_subgroup B)
      intro z
      have hz := congrArg (fun x : B => (x : G)) (hBinv z)
      simpa [aB, bB, a] using hz
    have hquot_has_nonone : ∃ x : G ⧸ A, x ≠ 1 := by
      by_contra hnone
      push Not at hnone
      have hsub : Subsingleton (G ⧸ A) := ⟨fun x y => by rw [hnone x, hnone y]⟩
      exact hquot_not_subsingleton hsub
    obtain ⟨x, hx_ne_one⟩ := hquot_has_nonone
    have hx_pow : x ^ (2 : ℕ) = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (G ⧸ A)) x
    have hx_order : orderOf x = 2 :=
      (orderOf_eq_prime_iff (x := x) (p := 2)).2 ⟨hx_pow, hx_ne_one⟩
    have hx_zpowers_ne_top : Subgroup.zpowers x ≠ (⊤ : Subgroup (G ⧸ A)) := by
      intro hx_top
      exact hquot_cyclic ((isCyclic_iff_exists_zpowers_eq_top (α := G ⧸ A)).2 ⟨x, hx_top⟩)
    have hquot_has_y : ∃ y : G ⧸ A, y ∉ Subgroup.zpowers x := by
      by_contra hyall_not
      push Not at hyall_not
      exact hx_zpowers_ne_top ((Subgroup.eq_top_iff' (H := Subgroup.zpowers x)).2 hyall_not)
    obtain ⟨y, hy_not_zpowers⟩ := hquot_has_y
    have hy_ne_one : y ≠ 1 := by
      intro hy_one
      exact hy_not_zpowers (by simp [hy_one])
    have hy_pow : y ^ (2 : ℕ) = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (G ⧸ A)) y
    have hy_order : orderOf y = 2 :=
      (orderOf_eq_prime_iff (x := y) (p := 2)).2 ⟨hy_pow, hy_ne_one⟩
    obtain ⟨b, hbq⟩ := QuotientGroup.mk'_surjective A x
    obtain ⟨c, hcq⟩ := QuotientGroup.mk'_surjective A y
    have hbinv : ∀ z : ℤ, a ^ z * b = b * a ^ (-z) :=
      hinverts_of_quot_order_two x hx_order b hbq
    have hcinv : ∀ z : ℤ, a ^ z * c = c * a ^ (-z) :=
      hinverts_of_quot_order_two y hy_order c hcq
    have hbc_cent : b * c ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hgA
      rw [← ha_zpowers] at hgA
      rcases Subgroup.mem_zpowers_iff.mp hgA with ⟨z, hz⟩
      rw [← hz]
      calc
        a ^ z * (b * c) = (a ^ z * b) * c := by group
        _ = (b * a ^ (-z)) * c := by rw [hbinv z]
        _ = b * (a ^ (-z) * c) := by group
        _ = b * (c * a ^ z) := by
          have hc := hcinv (-z)
          simpa using hc
        _ = (b * c) * a ^ z := by group
    have hbcA : b * c ∈ A := hAcent_le hbc_cent
    have hxy_one : x * y = 1 := by
      have hmk_one : π (b * c) = 1 := (QuotientGroup.eq_one_iff (N := A) (x := b * c)).2 hbcA
      calc
        x * y = π b * π c := by rw [hbq, hcq]
        _ = π (b * c) := by simp [π]
        _ = 1 := hmk_one
    have hy_eq_inv : y = x⁻¹ := by
      calc
        y = 1 * y := by simp
        _ = (x⁻¹ * x) * y := by simp
        _ = x⁻¹ * (x * y) := by group
        _ = x⁻¹ := by rw [hxy_one]; simp
    have hx_inv_mem : x⁻¹ ∈ Subgroup.zpowers x :=
      (Subgroup.zpowers x).inv_mem (Subgroup.mem_zpowers x)
    exact False.elim (hy_not_zpowers (by rw [hy_eq_inv]; exact hx_inv_mem))

/--
Huppert III.7.6(b), specialized to the use in III.8.2: a noncyclic finite
`2`-group whose abelian normal subgroups are forced cyclic by the unique
involution hypothesis has a cyclic normal subgroup of index `2`.
-/

public theorem exists_cyclic_normal_index_two_of_unique_involution
    {G : Type u} [Group G] [Finite G]
    (hGp : IsPGroup 2 G)
    (hnot_cyclic : ¬ IsCyclic G)
    (hunique_order_two : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x = y) :
    ∃ A : Subgroup G, ∃ a : G,
      A.Normal ∧ Subgroup.zpowers a = A ∧ A.index = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 G) := ⟨hGp⟩
  have hPhi_cyclic : IsCyclic (frattini G) :=
    huppert_III_7_6b_frattini_isCyclic_of_unique_order_two
      (G := G) hGp hunique_order_two
  let : CommGroup (frattini G) := hPhi_cyclic.commGroup
  have hPhi_comm : IsMulCommutative (frattini G) := inferInstance
  have hPhi_norm : (frattini G).Normal := by infer_instance
  obtain ⟨A, hPhi_le_A, hAnorm, hAcomm, hAmax, hAcent⟩ :=
    exists_normal_abelian_selfCentralizing_containing hGp
      (frattini G) hPhi_norm hPhi_comm
  have hA_cyclic : IsCyclic A :=
    huppert_III_7_6b_isCyclic_of_isMulCommutative_unique_order_two
      (G := G) hGp hunique_order_two A hAcomm
  obtain ⟨aA, haA_top⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := A)).1 hA_cyclic
  refine ⟨A, (aA : G), hAnorm, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      rcases Subgroup.mem_zpowers_iff.mp hx with ⟨z, hz⟩
      rw [← hz]
      exact A.zpow_mem aA.property z
    · intro hxA
      have hxA_top : (⟨x, hxA⟩ : A) ∈ (⊤ : Subgroup A) := by simp
      have hxA_zpow : (⟨x, hxA⟩ : A) ∈ Subgroup.zpowers aA := by
        rw [haA_top]
        exact hxA_top
      rcases Subgroup.mem_zpowers_iff.mp hxA_zpow with ⟨z, hz⟩
      refine Subgroup.mem_zpowers_iff.mpr ⟨z, ?_⟩
      exact Subtype.ext_iff.mp hz
  · exact
      huppert_III_7_6b_index_eq_two_of_maximal_normal_abelian
        (G := G) hGp hnot_cyclic hunique_order_two A hPhi_le_A hAnorm hAcomm hAmax hAcent

/-- The quaternion relations in the noncyclic index-two case. -/
private theorem quaternion_of_cyclic_index_two
    {G : Type u} [Group G] [Finite G] {k : ℕ} [NeZero k]
    (A : Subgroup G) [A.Normal] (a b : G)
    (hA : Subgroup.zpowers a = A) (hidx : A.index = 2)
    (ha : orderOf a = 2 * k) (hb : b ∉ A)
    (hunique : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x = y)
    (hncyc : ¬ IsCyclic G) (hcard : Nat.card G = 4 * k) (hG : IsPGroup 2 G) :
    Nonempty (G ≃* QuaternionGroup k) := by
  have hinv := huppert_I_14_9_conj_inverts_of_cyclic_index_two
    A a b hA hidx ha hb hunique hncyc hcard hG
  have hkpos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hak : orderOf (a ^ k) = 2 := by
    rw [orderOf_pow, ha, Nat.gcd_mul_left_left, Nat.mul_comm 2 k]
    exact Nat.mul_div_right 2 hkpos
  have hakA : a ^ k ∈ A := hA ▸ Subgroup.npow_mem_zpowers a k
  have hbne : b ≠ 1 := fun h => hb (h ▸ A.one_mem)
  have hb2ne : b ^ 2 ≠ 1 := by
    intro h
    have hb2 : orderOf b = 2 := orderOf_eq_prime h hbne
    exact hb ((hunique b (a ^ k) hb2 hak).symm ▸ hakA)
  have hb2A : b ^ 2 ∈ A := A.sq_mem_of_index_two hidx b
  obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp (hA.symm ▸ hb2A)
  have hsqinv : b ^ 2 = (b ^ 2)⁻¹ := by
    have hh := hinv s
    rw [zpow_neg, hs] at hh
    have hh' : b * b ^ 2 = b * (b ^ 2)⁻¹ := by
      calc
        b * b ^ 2 = b ^ 2 * b := by group
        _ = b * (b ^ 2)⁻¹ := hh
    exact mul_left_cancel hh'
  have hb4 : (b ^ 2) ^ 2 = 1 := by
    rw [pow_two]
    nth_rw 1 [hsqinv]
    exact inv_mul_cancel (b ^ 2)
  have hsq : b ^ 2 = a ^ k :=
    hunique _ _ (orderOf_eq_prime hb4 hb2ne) hak
  have hconj : b * a * b⁻¹ = a⁻¹ := by
    have hh := hinv (-1)
    simp only [zpow_neg_one, neg_neg, zpow_one] at hh
    calc
      b * a * b⁻¹ = (a⁻¹ * b) * b⁻¹ := by rw [hh]
      _ = a⁻¹ := by group
  have hgen : Subgroup.closure ({a, b} : Set G) = ⊤ := by
    let C := Subgroup.closure ({a, b} : Set G)
    have haC : a ∈ C := Subgroup.subset_closure (by simp)
    have hbC : b ∈ C := Subgroup.subset_closure (by simp)
    have hAC : A ≤ C := hA ▸ Subgroup.zpowers_le.mpr haC
    apply top_unique
    intro g _
    by_cases hg : g ∈ A
    · exact hAC hg
    · have hbInv : b⁻¹ ∉ A := fun h => hb (by simpa using A.inv_mem h)
      have hbg : b⁻¹ * g ∈ A :=
        (A.mul_mem_iff_of_index_two hidx).mpr ⟨fun h => (hbInv h).elim, fun h => (hg h).elim⟩
      simpa using C.mul_mem hbC (hAC hbg)
  exact QuaternionGroup.quaternionGroup_equiv_of_presentation hkpos a b ha hsq hconj hgen hcard

/-- A finite two-group with exactly one involution is cyclic or generalized quaternion
(Huppert III.8.2). -/
public theorem isCyclic_or_quaternion_of_unique_involution
    {G : Type u} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (hunique : ∃! z : G, orderOf z = 2) :
    IsCyclic G ∨ ∃ n : ℕ, 3 ≤ n ∧ Nonempty (G ≃* QuaternionGroup (2 ^ (n - 2))) := by
  classical
  by_cases hcyc : IsCyclic G
  · exact Or.inl hcyc
  right
  have hu : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x = y :=
    fun _ _ hx hy => hunique.unique hx hy
  obtain ⟨n, hn⟩ := hG.exists_card_eq
  have hn3 : 3 ≤ n := by
    by_contra h
    have hcases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · have hsub : Subsingleton G := (Nat.card_eq_one_iff_unique.mp (by simpa using hn)).1
      exact hcyc (@isCyclic_of_subsingleton G _ hsub)
    · let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact hcyc (isCyclic_of_prime_card (by simpa using hn : Nat.card G = 2))
    · let : CommGroup G := IsPGroup.commGroupOfCardEqPrimeSq (p := 2) hn
      exact hcyc (hG.isCyclic_of_unique_involution_of_isMulCommutative hunique)
  obtain ⟨A, a, hAn, hA, hidx⟩ :=
    exists_cyclic_normal_index_two_of_unique_involution hG hcyc hu
  let : A.Normal := hAn
  obtain ⟨b, hb, -⟩ := (Subgroup.index_eq_two_iff_exists_notMem_and (H := A)).mp hidx
  have hcard : Nat.card G = 4 * 2 ^ (n - 2) := by
    rw [hn]
    have hn' : n = (n - 2) + 2 := by omega
    calc
      2 ^ n = 2 ^ ((n - 2) + 2) := congrArg (2 ^ ·) hn'
      _ = 4 * 2 ^ (n - 2) := by rw [pow_add]; ring
  have hAcard : Nat.card A = 2 * 2 ^ (n - 2) := by
    have hh := A.card_mul_index
    rw [hidx, hcard] at hh
    omega
  have ha : orderOf a = 2 * 2 ^ (n - 2) := by
    rw [← Nat.card_zpowers a, hA, hAcard]
  let : NeZero (2 ^ (n - 2)) := ⟨pow_ne_zero _ (by decide)⟩
  exact ⟨n, hn3, quaternion_of_cyclic_index_two A a b hA hidx ha hb hu hcyc hcard hG⟩

/-- A finite two-group with no elementary four-group is cyclic or generalized
quaternion. The trivial group is included in the cyclic alternative. -/
public theorem isCyclic_or_quaternion_of_no_elementary_four
    {G : Type u} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (hfour : ∀ E : Subgroup G, IsElementaryAbelian 2 E → Nat.card E ≠ 4) :
    IsCyclic G ∨ ∃ n : ℕ, 3 ≤ n ∧ Nonempty (G ≃* QuaternionGroup (2 ^ (n - 2))) := by
  by_cases hcyc : IsCyclic G
  · exact Or.inl hcyc
  let : Nontrivial G := Nontrivial.of_not_isCyclic hcyc
  obtain ⟨z, hz, -, huniq⟩ := hG.exists_central_involution_of_no_elementary_four hfour
  apply hG.isCyclic_or_quaternion_of_unique_involution
  refine ⟨z, hz, fun x hx => ?_⟩
  rcases huniq x (by simpa only [hx] using pow_orderOf_eq_one x) with h | h
  · simp [h] at hx
  · exact h

end IsPGroup
