module

public import Stellmacher.Recognition.FongWreathedLocalBlocks
public import Theory.Character.TwoSectionInversion
public import Theory.Character.PrimePowerIntegralCongruence
public import Theory.Character.ModularBlock.TwoSectionContribution

/-!
# Fong's actual local contributions

The actual section mass is `Theory.Character.twoSectionMass`; the contribution
for a Sylow subgroup of order 32 is 32 times that mass. Integral values of an
odd-degree character at all Sylow two-elements are odd, by the prime-power
trace congruence. Rational power invariance identifies the values at F and F³.
Inversion identifies both values and masses at F² and its inverse.

Compatible principal projection and twisted genuine Brauer expansions identify
the local sums with the small quotient norms. The degree-one families give
contributions 4, 4, and 2b² at F, F³, and XF². At J and F², integral generalized
decomposition coefficients u,v give the value u+2v and contribution
2u²+(u−2v)², with u odd. These witnesses are derived from the supplied Brauer
families, rather than assumed as quadratic forms.

These results use actual characters and local sums and require no packet or
global section budget. Source: Fong, *Some Sylow subgroups of order 32*,
J. Algebra 6 (1967), printed pp. 73–74.
-/

public section
noncomputable section
namespace Stellmacher.Recognition.FongWreathedIntrinsic

open ABG
variable {G : Type*} [Group G] [Finite G]
  (S : Sylow 2 G) (P : Wreathed.Presentation S 2)

omit [Finite G] in
/-- Every integral value at a Sylow two-element has the parity of an odd degree. -/
theorem sylow_integer_value_odd {χ : ClassFunction G} (hχ : IsCharacter χ)
    (n : ℤ) (hn : χ 1 = (n : ℂ)) (hodd : Odd n)
    (y : S) (a : ℤ) (ha : χ (y : G) = (a : ℂ)) : Odd a := by
  obtain ⟨k, hk⟩ := S.isPGroup' y
  have hg : (y : G) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have hd := hχ.prime_dvd_degree_sub_integer_value (y : G) Nat.prime_two hg n a hn ha
  have he : Even (n - a) := even_iff_two_dvd.mpr hd
  simpa using hodd.sub_even he

omit [Finite G] in
/-- The two order-eight representatives have the same integral character value. -/
theorem F_cube_value_eq {χ : ClassFunction G} (hχ : IsCharacter χ)
    (hint : ∃ f : ℤ, χ ((F P : S) : G) = (f : ℂ)) :
    χ ((F P ^ 3 : S) : G) = χ ((F P : S) : G) := by
  have hF : ((F P : S) : G) ^ 8 = 1 := by
    have h := pow_orderOf_eq_one (F P)
    rw [F_orderOf] at h
    exact congrArg Subtype.val h
  exact hχ.pow_eq_of_integer_value ((F P : S) : G)
    (n := 8) (k := 3) (by decide) hF (by decide) hint

/-- The inverse-square section has the same value and actual contribution as
the square section. -/
theorem F_sq_inverse_value_and_contribution {χ : ClassFunction G}
    (hχ : IsCharacter χ)
    (hint : ∃ c : ℤ, χ ((F P ^ 2 : S) : G) = (c : ℂ)) :
    χ (((F P ^ 2)⁻¹ : S) : G) = χ ((F P ^ 2 : S) : G) ∧
      32 * Theory.Character.twoSectionMass χ (((F P ^ 2)⁻¹ : S) : G) =
        32 * Theory.Character.twoSectionMass χ ((F P ^ 2 : S) : G) := by
  obtain ⟨hv, hm⟩ := Theory.Character.inverse_section_value_and_mass hχ
    ((F P ^ 2 : S) : G) hint
  exact ⟨hv, congrArg (fun r : ℝ => 32 * r) hm⟩

open scoped BigOperators
open ModularBlock PrincipalBlockConstruction ModularBlock.Cartan

omit [Finite G] in
private theorem sylow_two_power (y : S) : ∃ k, (y : G) ^ (2 ^ k) = 1 := by
  obtain ⟨k, hk⟩ := S.isPGroup' y
  exact ⟨k, congrArg Subtype.val hk⟩

private theorem sylow_singleton_mass
    (d : PrincipalCongruenceBlockData G) (χ : ClassFunction G)
    (hm : ∃ i ∈ d.block, ∀ g, χ g = d.chi i (ConjClasses.mk g)) (y : S)
    (a : PrincipalDecompositionData
      (CompatibleBrauerBlock.localData d (Subgroup.centralizer ({(y : G)} : Set G))) 1)
    (hd : a.family.degree 0 = 1)
    (hQ : HasNormalPComplement 2 (Subgroup.centralizer ({(y : G)} : Set G)))
    (b : ℤ) (hb : χ (y : G) = (b : ℂ)) :
    Theory.Character.twoSectionMass χ (y : G) = (b : ℝ) ^ 2 /
      (Nat.card ((Subgroup.centralizer ({(y : G)} : Set G)) ⧸
        pPrimeCore 2 (Subgroup.centralizer ({(y : G)} : Set G))) : ℝ) := by
  exact TwoSectionContribution.mass_of_oddNormal_twoGroup d χ hm (y : G)
    (sylow_two_power S y) a (pPrimeCore 2 _) (pPrimeCore_coprime_card (p := 2)).odd_of_left
    (isPGroup_quotient_pPrimeCore_of_hasNormalPComplement 2 _ hQ) hd b hb

variable [IsSimpleGroup G]
local notation "CF" => Subgroup.centralizer ({((F P : S) : G)} : Set G)
local notation "CF3" => Subgroup.centralizer ({((F P ^ 3 : S) : G)} : Set G)
local notation "CF2" => Subgroup.centralizer ({((F P ^ 2 : S) : G)} : Set G)
local notation "CXF2" => Subgroup.centralizer ({((X P * F P ^ 2 : S) : G)} : Set G)
local notation "CJ" => Subgroup.centralizer ({((J P : S) : G)} : Set G)

/-- The contribution of the actual section at F is four. -/
theorem F_contribution (d : PrincipalCongruenceBlockData G) (hlocal : LocalBlockData S P d)
    (χ : ClassFunction G)
    (hm : ∃ i ∈ d.block, ∀ g, χ g = d.chi i (ConjClasses.mk g))
    (f : ℤ) (hf : χ ((F P : S) : G) = (f : ℂ)) (hfunit : f = 1 ∨ f = -1) :
    32 * Theory.Character.twoSectionMass χ ((F P : S) : G) = 4 := by
  obtain ⟨a, hd, _⟩ := hlocal.F_computation
  have he := sylow_singleton_mass S d χ hm (F P) a hd hlocal.F_normalComplement f hf
  obtain ⟨e⟩ := hlocal.F_quotient
  have hc : Nat.card (CF ⧸ pPrimeCore 2 CF) = 8 := by
    rw [Nat.card_congr e.toEquiv]
    norm_num
  rw [he, hc]
  rcases hfunit with rfl | rfl <;> norm_num

/-- The contribution of the actual section at F³ is four. -/
theorem F_cube_contribution (d : PrincipalCongruenceBlockData G)
    (hlocal : LocalBlockData S P d) (χ : ClassFunction G) (hχ : IsCharacter χ)
    (hm : ∃ i ∈ d.block, ∀ g, χ g = d.chi i (ConjClasses.mk g))
    (f : ℤ) (hf : χ ((F P : S) : G) = (f : ℂ)) (hfunit : f = 1 ∨ f = -1) :
    32 * Theory.Character.twoSectionMass χ ((F P ^ 3 : S) : G) = 4 := by
  obtain ⟨a, hd, _⟩ := hlocal.F_cube_computation
  have hf3 : χ ((F P ^ 3 : S) : G) = (f : ℂ) :=
    (F_cube_value_eq S P hχ ⟨f, hf⟩).trans hf
  have he := sylow_singleton_mass S d χ hm (F P ^ 3) a hd
    hlocal.F_cube_normalComplement f hf3
  obtain ⟨e⟩ := hlocal.F_cube_quotient
  have hc : Nat.card (CF3 ⧸ pPrimeCore 2 CF3) = 8 := by
    rw [Nat.card_congr e.toEquiv]
    norm_num
  rw [he, hc]
  rcases hfunit with rfl | rfl <;> norm_num

/-- The actual section at XF² has contribution twice the square of its odd value. -/
theorem XF_sq_contribution (d : PrincipalCongruenceBlockData G)
    (hlocal : LocalBlockData S P d) (χ : ClassFunction G) (hχ : IsCharacter χ)
    (hm : ∃ i ∈ d.block, ∀ g, χ g = d.chi i (ConjClasses.mk g))
    (n : ℤ) (hn : χ 1 = (n : ℂ)) (hnodd : Odd n)
    (b : ℤ) (hb : χ ((X P * F P ^ 2 : S) : G) = (b : ℂ)) :
    Odd b ∧ 32 * Theory.Character.twoSectionMass χ ((X P * F P ^ 2 : S) : G) =
      2 * (b : ℝ) ^ 2 := by
  refine ⟨sylow_integer_value_odd S hχ n hn hnodd _ b hb, ?_⟩
  obtain ⟨a, hd, _⟩ := hlocal.XF_sq_computation
  have he := sylow_singleton_mass S d χ hm (X P * F P ^ 2) a hd
    hlocal.XF_sq_normalComplement b hb
  obtain ⟨e⟩ := hlocal.XF_sq_quotient
  have hc : Nat.card (CXF2 ⧸ pPrimeCore 2 CXF2) = 16 := by
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_prod]
  rw [he, hc]
  ring

omit [Finite G] [IsSimpleGroup G] in
private theorem odd_coefficient (χ : ClassFunction G) (hχ : IsCharacter χ)
    (n : ℤ) (hn : χ 1 = (n : ℂ)) (hnodd : Odd n) (y : S)
    (u v : ℤ) (hv : χ (y : G) = ((u + 2 * v : ℤ) : ℂ)) : Odd u := by
  have ho := sylow_integer_value_odd S hχ n hn hnodd y (u + 2 * v) hv
  have he : Even (2 * v) := even_two_mul v
  simpa using ho.sub_even he

/-- Fong's quadratic formula at J, obtained from integral generalized
coefficients in its genuine two-character Brauer family. -/
theorem J_contribution (d : PrincipalCongruenceBlockData G)
    (hlocal : LocalBlockData S P d) (χ : ClassFunction G) (hχ : IsCharacter χ)
    (hm : ∃ i ∈ d.block, ∀ g, χ g = d.chi i (ConjClasses.mk g))
    (hint : ∀ g, ∃ k : ℤ, χ g = (k : ℂ))
    (n : ℤ) (hn : χ 1 = (n : ℂ)) (hnodd : Odd n) :
    ∃ u v : ℤ, χ ((J P : S) : G) = ((u + 2 * v : ℤ) : ℂ) ∧ Odd u ∧
      32 * Theory.Character.twoSectionMass χ ((J P : S) : G) =
        ((2 * u ^ 2 + (u - 2 * v) ^ 2 : ℤ) : ℝ) := by
  obtain ⟨a, hd0, hd1, _⟩ := hlocal.J_computation
  let N := pPrimeCore 2 CJ
  let Z := Subgroup.zpowers (QuotientGroup.mk' N (squareInCentralizerJ S P))
  let _ : Z.Normal := squareInCentralizerJ_quotient_zpowers_normal S P
  obtain ⟨e⟩ := hlocal.J_projective_quotient
  have hy : ((J P : S) : G) ^ 4 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [Subgroup.orderOf_coe, J_orderOf]
    decide
  obtain ⟨u, v, _, hv, hq⟩ :=
    TwoSectionContribution.contribution_of_oddNormal_centralFour_symmetricFour d χ hχ hm hint
      ((J P : S) : G) hy a N (pPrimeCore_coprime_card (p := 2)).odd_of_left Z
      (Subgroup.zpowers_le.mpr (squareInCentralizerJ_quotient_mem_center S P))
      (squareInCentralizerJ_quotient_zpowers_card S P) e hd0 hd1
  exact ⟨u, v, hv, odd_coefficient S χ hχ n hn hnodd _ u v hv, hq⟩

/-- Fong's quadratic formula at F², with integral generalized coefficients. -/
theorem F_sq_contribution (d : PrincipalCongruenceBlockData G)
    (hlocal : LocalBlockData S P d) (χ : ClassFunction G) (hχ : IsCharacter χ)
    (hm : ∃ i ∈ d.block, ∀ g, χ g = d.chi i (ConjClasses.mk g))
    (hint : ∀ g, ∃ k : ℤ, χ g = (k : ℂ))
    (n : ℤ) (hn : χ 1 = (n : ℂ)) (hnodd : Odd n) :
    ∃ u v : ℤ, χ ((F P ^ 2 : S) : G) = ((u + 2 * v : ℤ) : ℂ) ∧ Odd u ∧
      32 * Theory.Character.twoSectionMass χ ((F P ^ 2 : S) : G) =
        ((2 * u ^ 2 + (u - 2 * v) ^ 2 : ℤ) : ℝ) := by
  obtain ⟨a, hd0, hd1, _⟩ := hlocal.F_sq_computation
  let N := pPrimeCore 2 CF2
  let z := QuotientGroup.mk' N (squareInCentralizerF2 S P)
  let Z := Subgroup.zpowers z
  let _ : Z.Normal := squareInCentralizerF2_quotient_zpowers_normal S P
  obtain ⟨e⟩ := hlocal.F_sq_projective_quotient
  have hz : z ∈ Subgroup.center (CF2 ⧸ N) := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply (centralizerF2OddCoreEquiv S P).injective
    rw [map_mul, map_mul, centralizerF2OddCoreEquiv_square]
    exact Subgroup.mem_center_iff.mp (squareInCentralizerJ_quotient_mem_center S P) _
  have hzcard : Nat.card Z = 4 := by
    rw [Nat.card_zpowers, ← (centralizerF2OddCoreEquiv S P).orderOf_eq z]
    rw [centralizerF2OddCoreEquiv_square, squareInCentralizerJ_quotient_orderOf]
  have hy : ((F P ^ 2 : S) : G) ^ 4 = 1 := by
    have hs : (F P ^ 2) ^ 4 = 1 := by
      rw [← F_sq_orderOf P]
      exact pow_orderOf_eq_one (F P ^ 2)
    exact congrArg Subtype.val hs
  obtain ⟨u, v, _, hv, hq⟩ :=
    TwoSectionContribution.contribution_of_oddNormal_centralFour_symmetricFour d χ hχ hm hint
      ((F P ^ 2 : S) : G) hy a N (pPrimeCore_coprime_card (p := 2)).odd_of_left Z
      (Subgroup.zpowers_le.mpr hz) hzcard e hd0 hd1
  exact ⟨u, v, hv, odd_coefficient S χ hχ n hn hnodd _ u v hv, hq⟩

end Stellmacher.Recognition.FongWreathedIntrinsic
