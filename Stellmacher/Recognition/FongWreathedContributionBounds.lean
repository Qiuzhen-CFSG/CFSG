module

public import Stellmacher.Recognition.FongWreathedLocalBlocks
public import Stellmacher.Recognition.FongWreathedRestrictionCongruences
public import Theory.Character.SimpleFaithfulCharacter
public import Theory.Character.PrimePowerIntegralCongruence
public import Stellmacher.Recognition.FongWreathedLocalContributions
public import Theory.Character.TwoSectionMassBudget

/-!
# Actual-character estimates for Fong's rational rows

The elementary estimates here apply to an actual nonprincipal irreducible
character, independently of the existence of Fong's exceptional packet.
Faithfulness excludes equality with the degree at J. Equality with the negative
degree would make J act as minus the identity; since J = F⁴, rational power
invariance would then force the nonzero value at F to vanish. Prime-power trace
spacing and the cyclic restriction congruence give odd values at J.

The genuine local Cartan calculations give integral generalized decomposition
coefficients at J and F². The six distinct nonidentity two-sections have total
contribution strictly less than 32: the identity section has positive mass.
The other five contributions are at least 4+4+2+3+3, so each target contribution
is below 16, hence at most 15 by integrality. Fong's quadratic-form arithmetic
then bounds both character values by five. Combining these estimates with the
restriction congruences gives the full row conditions for any supplied actual
character, without assuming existence of an exceptional packet.

Source: P. Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)*, J. Algebra 6 (1967), pp. 73–74; and the corrected degree calculation in
refs/original/n-group-global/sylow32-source-audit/fong-degree-calculation-audit.md.
-/

public section
noncomputable section

namespace Stellmacher.Recognition.FongWreathedIntrinsic

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
  (S : Sylow 2 G) (P : ABG.Wreathed.Presentation S 2)

omit [Finite G] [IsSimpleGroup G] in
/-- An integer-valued character whose value at F is odd has odd degree and
odd value at J. No principal-block membership or irreducibility is needed. -/
theorem degree_and_involution_odd_of_character
    {χ : ClassFunction G} (hχ : IsCharacter χ)
    (hint : ∀ g, ∃ z : ℤ, χ g = (z : ℂ))
    (n a f : ℤ) (hn : χ 1 = (n : ℂ))
    (ha : χ (J P : S) = (a : ℂ))
    (hf : χ (F P : S) = (f : ℂ)) (hfodd : Odd f) : Odd n ∧ Odd a := by
  have hC := cyclic_restriction_numerator S P hχ hint n a hn ha
  have hpow : ((F P : S) : G) ^ (2 ^ 3) = 1 := by
    rw [← Subgroup.coe_pow]
    norm_num only [show 2 ^ 3 = 8 by decide]
    rw [← F_orderOf P, pow_orderOf_eq_one, Subgroup.coe_one]
  have heven := hχ.prime_dvd_degree_sub_integer_value ((F P : S) : G)
    (by decide : Nat.Prime 2) hpow n f hn hf
  constructor <;> rw [Int.odd_iff]
  · have := Int.odd_iff.mp hfodd
    omega
  · have := Int.odd_iff.mp hfodd
    omega

omit [Finite G] [IsSimpleGroup G] in
/-- In particular, either exceptional value at F forces odd involution value. -/
theorem involution_odd_of_character
    {χ : ClassFunction G} (hχ : IsCharacter χ)
    (hint : ∀ g, ∃ z : ℤ, χ g = (z : ℂ))
    (n a f : ℤ) (hn : χ 1 = (n : ℂ))
    (ha : χ (J P : S) = (a : ℂ))
    (hf : χ (F P : S) = (f : ℂ)) (hsign : f = 1 ∨ f = -1) : Odd a := by
  apply (degree_and_involution_odd_of_character S P hχ hint n a f hn ha hf ?_).2
  rcases hsign with rfl | rfl <;> decide

/-- The absolute involution value of a nonprincipal rational irreducible is
strictly smaller than its degree whenever its value at F is nonzero. -/
theorem abs_involution_lt_degree_of_character
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) (hnp : χ ≠ 1)
    (hint : ∀ g, ∃ z : ℤ, χ g = (z : ℂ))
    (n a f : ℤ) (hn : χ 1 = (n : ℂ))
    (ha : χ (J P : S) = (a : ℂ))
    (hf : χ (F P : S) = (f : ℂ)) (hfne : f ≠ 0) : |a| < n := by
  obtain ⟨m, ρ, _, rfl, hfaithful⟩ := hχ.exists_faithful_of_ne_one hnp
  have hmn : (m : ℤ) = n := by
    have hh : (m : ℂ) = (n : ℂ) := by simpa using hn
    exact_mod_cast hh
  have hJpow : (ρ ((J P : S) : G)) ^ 2 = 1 := by
    have hj : (J P : S) ^ 2 = 1 := by
      simpa only [J_orderOf] using pow_orderOf_eq_one (J P)
    rw [← map_pow, ← Subgroup.coe_pow, hj, Subgroup.coe_one, map_one]
  have hb : |a| ≤ n := by
    have hh : |(a : ℝ)| ≤ (m : ℝ) := calc
      _ = |(ρ.character ((J P : S) : G)).re| := by rw [ha]; simp
      _ ≤ ‖ρ.character ((J P : S) : G)‖ := Complex.abs_re_le_norm _
      _ ≤ m := by
        simpa [Representation.character] using finite_order_end_norm_trace_le_finrank
          (ρ ((J P : S) : G)) (by decide : 2 ≠ 0) hJpow
    rw [← hmn]
    exact_mod_cast hh
  have hpos : a ≠ n := by
    intro he
    have hρJ : ρ ((J P : S) : G) = 1 :=
      finite_order_end_eq_one_of_trace_eq_finrank _ (by decide : 2 ≠ 0) hJpow
        (by simpa [Representation.character, he, ← hmn] using ha)
    have hJ : (J P : S) = 1 := Subtype.val_injective
      (hfaithful (hρJ.trans (map_one ρ).symm))
    have ho := J_orderOf P
    rw [hJ, orderOf_one] at ho
    omega
  have hneg : a ≠ -n := by
    intro he
    have ht : LinearMap.trace ℂ (Fin m → ℂ) (-ρ ((J P : S) : G)) =
        (Module.finrank ℂ (Fin m → ℂ) : ℂ) := by
      simp only [map_neg]
      change -ρ.character ((J P : S) : G) = _
      simp [ha, he, ← hmn]
    have hnegpow : (-ρ ((J P : S) : G)) ^ 2 = 1 := by
      simpa only [pow_two, Module.End.mul_eq_comp, LinearMap.neg_comp,
        LinearMap.comp_neg, neg_neg] using hJpow
    have hρJ : ρ ((J P : S) : G) = -1 := by
      have hh := finite_order_end_eq_one_of_trace_eq_finrank _
        (by decide : 2 ≠ 0) hnegpow ht
      exact neg_eq_iff_eq_neg.mp hh
    have hFpow : ((F P : S) : G) ^ 8 = 1 := by
      rw [← Subgroup.coe_pow, ← F_orderOf P, pow_orderOf_eq_one, Subgroup.coe_one]
    have hi : IsCharacter ρ.character := ⟨m, ρ, rfl⟩
    have h5 := hi.pow_eq_of_integer_value ((F P : S) : G)
      (by decide : 8 ≠ 0) hFpow (by decide : Nat.Coprime 5 8) (hint _)
    have hv : ρ.character (((F P : S) : G) ^ 5) =
        -ρ.character ((F P : S) : G) := by
      simp only [Representation.character, show 5 = 4 + 1 by decide,
        pow_add, pow_one, map_mul, ← Subgroup.coe_pow, F_four, hρJ,
        Module.End.mul_eq_comp, LinearMap.neg_comp, Module.End.one_eq_id,
        LinearMap.id_comp, map_neg]
    rw [hv, hf] at h5
    have hz : f = 0 := by exact_mod_cast (show (f : ℂ) = 0 by linear_combination -h5 / 2)
    exact hfne hz
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h] at hb ⊢
    exact lt_of_le_of_ne hb hpos
  · rw [abs_of_nonpos h] at hb ⊢
    omega

open scoped BigOperators
open ModularBlock PrincipalBlockConstruction

/-- The six nonidentity sections leave positive mass for the identity section. -/
theorem six_section_contribution_lt_thirty_two
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) :
    32 * Theory.Character.twoSectionMass χ ((F P : S) : G) +
      32 * Theory.Character.twoSectionMass χ ((F P ^ 3 : S) : G) +
      32 * Theory.Character.twoSectionMass χ ((F P ^ 2 : S) : G) +
      32 * Theory.Character.twoSectionMass χ (((F P ^ 2)⁻¹ : S) : G) +
      32 * Theory.Character.twoSectionMass χ ((X P * F P ^ 2 : S) : G) +
      32 * Theory.Character.twoSectionMass χ ((J P : S) : G) < 32 := by
  have hp (i : Fin 6) : ∃ k : ℕ,
      ((fusionRepresentative S P i : S) : G) ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := S.isPGroup' (fusionRepresentative S P i)
    exact ⟨k, congrArg Subtype.val hk⟩
  have hn (i : Fin 6) : ((fusionRepresentative S P i : S) : G) ≠ 1 := by
    intro he
    have hs : fusionRepresentative S P i = 1 := Subtype.val_injective he
    have ho := fusionRepresentative_orderOf S P i
    rw [hs, orderOf_one] at ho
    fin_cases i <;> norm_num at ho
  have h := Theory.Character.sum_twoSectionMass_lt_one
    (fun i : Fin 6 => ((fusionRepresentative S P i : S) : G)) hp hn
    (fusionRepresentative_separated S P) hχ
  simp only [Fin.sum_univ_succ,
    fusionRepresentative, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero] at h
  linarith

private theorem odd_square_ge_one (u : ℤ) (hu : Odd u) : 1 ≤ u ^ 2 := by
  have he := Int.odd_iff.mp hu
  have hn : u ≠ 0 := by omega
  rcases lt_or_gt_of_ne hn with h | h <;> nlinarith

private theorem odd_contribution_ge_three (u v : ℤ) (hu : Odd u) :
    3 ≤ 2 * u ^ 2 + (u - 2 * v) ^ 2 := by
  have hd : Odd (u - 2 * v) := hu.sub_even (even_two_mul v)
  linarith [odd_square_ge_one u hu, odd_square_ge_one (u - 2 * v) hd]

/-- Each two-dimensional Cartan section has contribution at most fifteen.
The other five sections contribute at least 4+4+2+3+3, and the omitted
identity section makes the total budget strictly less than thirty-two. -/
theorem J_and_F_sq_contribution_le_fifteen
    (d : PrincipalCongruenceBlockData G) (hlocal : LocalBlockData S P d)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    (hm : ∃ i ∈ d.block, ∀ g, χ g = d.chi i (ConjClasses.mk g))
    (hint : ∀ g, ∃ z : ℤ, χ g = (z : ℂ))
    (n f : ℤ) (hn : χ 1 = (n : ℂ)) (hnodd : Odd n)
    (hf : χ ((F P : S) : G) = (f : ℂ)) (hsign : f = 1 ∨ f = -1) :
    32 * Theory.Character.twoSectionMass χ ((J P : S) : G) ≤ 15 ∧
      32 * Theory.Character.twoSectionMass χ ((F P ^ 2 : S) : G) ≤ 15 := by
  have hchar : IsCharacter χ := by
    obtain ⟨m, ρ, _, he⟩ := hχ
    exact ⟨m, ρ, he⟩
  obtain ⟨b, hb⟩ := hint ((X P * F P ^ 2 : S) : G)
  obtain ⟨hbodd, hB⟩ := XF_sq_contribution S P d hlocal χ hchar hm n hn hnodd b hb
  obtain ⟨u, v, _, hu, hJ⟩ := J_contribution S P d hlocal χ hchar hm hint n hn hnodd
  obtain ⟨s, t, hv, hs, hC⟩ := F_sq_contribution S P d hlocal χ hchar hm hint n hn hnodd
  have hInv := (F_sq_inverse_value_and_contribution S P hchar ⟨s + 2 * t, hv⟩).2
  have h := six_section_contribution_lt_thirty_two S P hχ
  rw [F_contribution S P d hlocal χ hm f hf hsign,
    F_cube_contribution S P d hlocal χ hchar hm f hf hsign,
    hInv, hB, hJ, hC] at h
  have hb2 : (1 : ℝ) ≤ (b : ℝ) ^ 2 := by exact_mod_cast odd_square_ge_one b hbodd
  have hJ3 : (3 : ℝ) ≤ ((2 * u ^ 2 + (u - 2 * v) ^ 2 : ℤ) : ℝ) := by
    exact_mod_cast odd_contribution_ge_three u v hu
  have hC3 : (3 : ℝ) ≤ ((2 * s ^ 2 + (s - 2 * t) ^ 2 : ℤ) : ℝ) := by
    exact_mod_cast odd_contribution_ge_three s t hs
  have hJlt : (2 * u ^ 2 + (u - 2 * v) ^ 2 : ℤ) < 16 := by
    exact_mod_cast (show ((2 * u ^ 2 + (u - 2 * v) ^ 2 : ℤ) : ℝ) < 16 by linarith)
  have hClt : (2 * s ^ 2 + (s - 2 * t) ^ 2 : ℤ) < 16 := by
    exact_mod_cast (show ((2 * s ^ 2 + (s - 2 * t) ^ 2 : ℤ) : ℝ) < 16 by linarith)
  constructor
  · rw [hJ]
    exact_mod_cast (show (2 * u ^ 2 + (u - 2 * v) ^ 2 : ℤ) ≤ 15 by omega)
  · rw [hC]
    exact_mod_cast (show (2 * s ^ 2 + (s - 2 * t) ^ 2 : ℤ) ≤ 15 by omega)

/-- The actual involution value is at most five in absolute value. -/
theorem abs_involution_le_five_of_character
    (d : PrincipalCongruenceBlockData G) (hlocal : LocalBlockData S P d)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    (hm : ∃ i ∈ d.block, ∀ g, χ g = d.chi i (ConjClasses.mk g))
    (hint : ∀ g, ∃ z : ℤ, χ g = (z : ℂ))
    (n a f : ℤ) (hn : χ 1 = (n : ℂ))
    (ha : χ ((J P : S) : G) = (a : ℂ))
    (hf : χ ((F P : S) : G) = (f : ℂ)) (hsign : f = 1 ∨ f = -1) :
    |a| ≤ 5 := by
  have hchar : IsCharacter χ := by
    obtain ⟨m, ρ, _, he⟩ := hχ
    exact ⟨m, ρ, he⟩
  have hodd : Odd n := (degree_and_involution_odd_of_character S P hchar hint
    n a f hn ha hf (by rcases hsign with rfl | rfl <;> decide)).1
  have hbound := (J_and_F_sq_contribution_le_fifteen S P d hlocal hχ hm hint
    n f hn hodd hf hsign).1
  obtain ⟨u, v, hv, hu, hq⟩ := J_contribution S P d hlocal χ hchar hm hint n hn hodd
  have he : a = u + 2 * v := by exact_mod_cast ha.symm.trans hv
  rw [he]
  apply fong_abs_value_le_five_of_contribution u v hu
  rw [hq] at hbound
  exact_mod_cast hbound

/-- The actual central order-four value satisfies the same bound by five.
This additional bound is essential to exclude the spurious degree-35 row. -/
theorem abs_centralFour_le_five_of_character
    (d : PrincipalCongruenceBlockData G) (hlocal : LocalBlockData S P d)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    (hm : ∃ i ∈ d.block, ∀ g, χ g = d.chi i (ConjClasses.mk g))
    (hint : ∀ g, ∃ z : ℤ, χ g = (z : ℂ))
    (n c f : ℤ) (hn : χ 1 = (n : ℂ))
    (hc : χ ((F P ^ 2 : S) : G) = (c : ℂ))
    (hf : χ ((F P : S) : G) = (f : ℂ)) (hsign : f = 1 ∨ f = -1) :
    |c| ≤ 5 := by
  have hchar : IsCharacter χ := by
    obtain ⟨m, ρ, _, he⟩ := hχ
    exact ⟨m, ρ, he⟩
  obtain ⟨a, ha⟩ := hint ((J P : S) : G)
  have hodd : Odd n := (degree_and_involution_odd_of_character S P hchar hint
    n a f hn ha hf (by rcases hsign with rfl | rfl <;> decide)).1
  have hbound := (J_and_F_sq_contribution_le_fifteen S P d hlocal hχ hm hint
    n f hn hodd hf hsign).2
  obtain ⟨u, v, hv, hu, hq⟩ := F_sq_contribution S P d hlocal χ hchar hm hint n hn hodd
  have he : c = u + 2 * v := by exact_mod_cast hc.symm.trans hv
  rw [he]
  apply fong_abs_value_le_five_of_contribution u v hu
  rw [hq] at hbound
  exact_mod_cast hbound

/-- Every genuine nonprincipal integral irreducible in the supplied principal
block, with value ±1 at F, satisfies the full numerical row interface.
Character existence and selection of an exceptional packet are independent. -/
theorem fongRowConditions_of_character
    (d : PrincipalCongruenceBlockData G) (hlocal : LocalBlockData S P d)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ) (hnp : χ ≠ 1)
    (hm : ∃ i ∈ d.block, ∀ g, χ g = d.chi i (ConjClasses.mk g))
    (hint : ∀ g, ∃ z : ℤ, χ g = (z : ℂ))
    (r : FongCharacterRow) (f : ℤ) (hn : χ 1 = (r.d : ℂ))
    (ha : χ ((J P : S) : G) = (r.a : ℂ))
    (hb : χ ((X P * F P ^ 2 : S) : G) = (r.b : ℂ))
    (hc : χ ((F P ^ 2 : S) : G) = (r.c : ℂ))
    (hf : χ ((F P : S) : G) = (f : ℂ)) (hsign : f = 1 ∨ f = -1) :
    FongRowConditions r f := by
  have hchar : IsCharacter χ := by
    obtain ⟨m, ρ, _, he⟩ := hχ
    exact ⟨m, ρ, he⟩
  apply (fongRestrictionCongruences_of_character S P hlocal.base hchar hint
    r f hn ha hb hc hf).toRowConditions
  · exact abs_involution_lt_degree_of_character S P hχ hnp hint r.d r.a f hn ha hf
      (by rcases hsign with rfl | rfl <;> decide)
  · exact involution_odd_of_character S P hchar hint r.d r.a f hn ha hf hsign
  · exact abs_involution_le_five_of_character S P d hlocal hχ hm hint r.d r.a f hn ha hf hsign
  · exact abs_centralFour_le_five_of_character S P d hlocal hχ hm hint r.d r.c f hn hc hf hsign

end Stellmacher.Recognition.FongWreathedIntrinsic
