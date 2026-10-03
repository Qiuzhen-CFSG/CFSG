module

public import Stellmacher.Recognition.FongWreathedInducedCharacters
public import Stellmacher.Recognition.FongWreathedLocalBlocks
public import Stellmacher.Recognition.FongWreathedFusionSeparation
public import Theory.Character.ModularBlock.SectionKernel

/-!
# Principal-block membership of Fong's induced packets

For any prescribed height-two wreathed Sylow presentation, every irreducible
constituent of either actual induced function belongs to the actual principal
two-block. No fusion orientation or supplied local-block datum is required.

Let K(u) be the principal-block kernel based at u. Section orthogonality
supports K(F) and K(F³) on their respective two-sections; their averages are
one, their squared norms are eight, and their mutual scalar product is zero.
An odd element commuting with F belongs to the odd core of its normalizer,
since the quotient has order sixteen. The same holds for F³, which generates
⟨F⟩. Thus the actual induced functions take constant values 4,4 and 4i,-4i
on these sections. Their squared norms of four imply
Θ₁ = (K(F) + K(F³))/2 and Θ₂ = i(K(F) - K(F³))/2 by positive definiteness.
Ordinary character orthogonality then gives constituent membership.

Source: P. Fong, *Some Sylow subgroups of order 32 and a characterization
of U(3,3)*, J. Algebra 6 (1967), printed p.72, invoking Wong's Theorem 7.
Here the principal-block section kernel and the known column norms give a
direct proof of that instance without general exceptional-character theory.
-/

public section
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite
namespace Stellmacher.Recognition.FongWreathedInduction
open FongWreathedIntrinsic
variable {G : Type*} [Group G] [Finite G]

private theorem odd_mem (d : InducingData G) (v : d.H)
    (hv : Odd (orderOf v)) : v ∈ d.U := by
  let q := QuotientGroup.mk' d.U
  have hc : Nat.card (d.H ⧸ d.U) = 16 := by
    have h := d.U.card_eq_card_quotient_mul_card_subgroup
    rw [d.card_H] at h
    nlinarith [Nat.card_pos (α := d.U)]
  apply (QuotientGroup.eq_one_iff v).mp
  change q v = 1
  apply orderOf_eq_one_iff.mp
  apply Nat.eq_one_of_dvd_coprimes (show Nat.Coprime 16 (orderOf v) from
    (Nat.coprime_pow_left_iff (by decide : 0 < 4) 2 (orderOf v)).mpr (Nat.coprime_two_left.mpr hv))
  · simpa only [hc] using orderOf_dvd_natCard (q v)
  · exact orderOf_map_dvd q v

private theorem commute_mem (S : Sylow 2 G) (P : ABG.Wreathed.Presentation S 2)
    (v : G) (hv : Commute ((F P : S) : G) v) :
    v ∈ (actualInducingData S P).H := by
  rw [(actualInducingData_isActual S P).1]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  change Subgroup.zpowers (v * ((F P : S) : G) * v⁻¹) = _
  rw [hv.symm.eq, mul_assoc, mul_inv_cancel, mul_one]

private theorem values_mul (S : Sylow 2 G) (P : ABG.Wreathed.Presentation S 2)
    (i : Fin 8) (hi : Odd i.val) (v : G) (hv : Odd (orderOf v))
    (hcomm : Commute ((F P : S) : G) v) :
    actualInducedOne S P (((F P : S) : G) ^ i.val * v) = 4 ∧
    actualInducedTwo S P (((F P : S) : G) ^ i.val * v) = 4 * Complex.I ^ i.val := by
  let w : (actualInducingData S P).H := ⟨v, commute_mem S P v hcomm⟩
  have hw : w ∈ (actualInducingData S P).U :=
    odd_mem _ w (by simpa only [Subgroup.orderOf_mk, w] using hv)
  exact actual_induced_on_odd_coset S P i hi ⟨w, hw⟩

end Stellmacher.Recognition.FongWreathedInduction

namespace Stellmacher.Recognition.FongWreathedInduction
open FongWreathedIntrinsic
variable {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (P : ABG.Wreathed.Presentation S 2)

private theorem values_on_section (k : Fin 8) (hk : k = 1 ∨ k = 3)
    (g : G) (hg : ∃ v : G, Odd (orderOf v) ∧
      Commute (((F P : S) : G) ^ k.val) v ∧
        IsConj (((F P : S) : G) ^ k.val * v) g) :
    actualInducedOne S P g = 4 ∧
    actualInducedTwo S P g = 4 * Complex.I ^ k.val := by
  obtain ⟨v, hv, hc, c, hcg⟩ := hg
  have hc' : Commute ((F P : S) : G) v := by
    rcases hk with rfl | rfl
    · simpa using hc
    · have hh := hc.pow_left 3
      have hp : (((F P : S) : G) ^ 3) ^ 3 = ((F P : S) : G) := by
        rw [← pow_mul, show 3 * 3 = 8 + 1 by decide, pow_add, pow_one]
        have h8 : ((F P : S) : G) ^ 8 = 1 := by
          exact_mod_cast (show F P ^ 8 = 1 by simpa only [F_orderOf] using pow_orderOf_eq_one (F P))
        rw [h8, one_mul]
      change Commute ((((F P : S) : G) ^ 3) ^ 3) v at hh
      rwa [hp] at hh
  have ho : Odd k.val := by rcases hk with rfl | rfl <;> decide
  have he := values_mul S P k ho v hv hc'
  have hclass1 := BenderGlauberman.isClassFunction_of_isGeneralizedCharacter
    (actual_induced_gram_data S P).1
  have hclass2 := BenderGlauberman.isClassFunction_of_isGeneralizedCharacter
    (actual_induced_gram_data S P).2.1
  have hg' : (c : G) * (((F P : S) : G) ^ k.val * v) * (c : G)⁻¹ = g := by
    exact mul_inv_eq_iff_eq_mul.mpr hcg.eq
  rw [← hg', hclass1, hclass2]
  exact he
end Stellmacher.Recognition.FongWreathedInduction

namespace Stellmacher.Recognition.FongWreathedInduction
open FongWreathedIntrinsic ModularBlock PrincipalBlockConstruction SectionKernel
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (P : ABG.Wreathed.Presentation S 2)
    (x : G) (hx : orderOf x = 2)
    [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))]
    (d : PrincipalCongruenceBlockData G)

include x hx in
private theorem kernel_gram :
    scalarProduct G (kernel d ((F P : S) : G)) (kernel d ((F P : S) : G)) = 8 ∧
    scalarProduct G (kernel d ((F P ^ 3 : S) : G)) (kernel d ((F P ^ 3 : S) : G)) = 8 ∧
    scalarProduct G (kernel d ((F P : S) : G)) (kernel d ((F P ^ 3 : S) : G)) = 0 := by
  have hcol := localPrincipalColumnNormData_of_cartan S P d
    (localPrincipalCartanData S P x hx d)
  simp only [kernel_scalar_kernel]
  refine ⟨hcol.F_column, hcol.F_cube_column, ?_⟩
  apply SectionOrthogonality.principalBlock_column_eq_zero_of_not_isConj
  · obtain ⟨n, hn⟩ := S.isPGroup'.exists_pow_pow_eq_one (F P ^ 3)
    exact ⟨n, congrArg Subtype.val hn⟩
  · obtain ⟨n, hn⟩ := S.isPGroup'.exists_pow_pow_eq_one (F P)
    exact ⟨n, congrArg Subtype.val hn⟩
  · exact fun h => not_isConj_F_F_cube S P h.symm

omit [IsSimpleGroup G] [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))] in
private theorem kernel_pairings :
    scalarProduct G (actualInducedOne S P) (kernel d ((F P : S) : G)) = 4 ∧
    scalarProduct G (actualInducedOne S P) (kernel d ((F P ^ 3 : S) : G)) = 4 ∧
    scalarProduct G (actualInducedTwo S P) (kernel d ((F P : S) : G)) = 4 * Complex.I ∧
    scalarProduct G (actualInducedTwo S P) (kernel d ((F P ^ 3 : S) : G)) = -4 * Complex.I := by
  have hp (a : S) : ∃ n : ℕ, (a : G) ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_pow_pow_eq_one a
    exact ⟨n, congrArg Subtype.val hn⟩
  have h1 (g : G) (hg : ∃ v : G, Odd (orderOf v) ∧ Commute ((F P : S) : G) v ∧
      IsConj (((F P : S) : G) * v) g) :
      actualInducedOne S P g = 4 ∧ actualInducedTwo S P g = 4 * Complex.I := by
    simpa using values_on_section S P 1 (Or.inl rfl) g (by simpa using hg)
  have h3 (g : G) (hg : ∃ v : G, Odd (orderOf v) ∧ Commute ((F P ^ 3 : S) : G) v ∧
      IsConj (((F P ^ 3 : S) : G) * v) g) :
      actualInducedOne S P g = 4 ∧ actualInducedTwo S P g = -4 * Complex.I := by
    have hh := values_on_section S P 3 (Or.inr rfl) g (by simpa using hg)
    norm_num [Complex.I_pow_three] at hh ⊢
    exact hh
  exact ⟨scalar_kernel_of_constant d _ (hp _) _ _ (fun g hg => (h1 g hg).1),
    scalar_kernel_of_constant d _ (hp _) _ _ (fun g hg => (h3 g hg).1),
    scalar_kernel_of_constant d _ (hp _) _ _ (fun g hg => (h1 g hg).2),
    scalar_kernel_of_constant d _ (hp _) _ _ (fun g hg => (h3 g hg).2)⟩

include x hx in
/-- The first actual induced function is the half-sum of the two principal-block kernels. -/
theorem actualInducedOne_eq_kernels :
    actualInducedOne S P = (1 / 2 : ℂ) • kernel d ((F P : S) : G) +
      (1 / 2 : ℂ) • kernel d ((F P ^ 3 : S) : G) := by
  obtain ⟨hu, hv, huv⟩ := kernel_gram S P x hx d
  obtain ⟨hfu, hfv, _, _⟩ := kernel_pairings S P d
  apply eq_two_kernels_of_norm d _ _ _ _ _ hu hv huv
  · norm_num; exact hfu
  · norm_num; exact hfv
  · norm_num; exact (actual_induced_gram_data S P).2.2.1

include x hx in
/-- The second actual induced function is i times the half-difference of the two kernels. -/
theorem actualInducedTwo_eq_kernels :
    actualInducedTwo S P = (Complex.I / 2) • kernel d ((F P : S) : G) +
      (-Complex.I / 2) • kernel d ((F P ^ 3 : S) : G) := by
  obtain ⟨hu, hv, huv⟩ := kernel_gram S P x hx d
  obtain ⟨_, _, hfu, hfv⟩ := kernel_pairings S P d
  apply eq_two_kernels_of_norm d _ _ _ _ _ hu hv huv
  · rw [hfu]; ring
  · rw [hfv]; ring
  · rw [(actual_induced_gram_data S P).2.2.2.1]
    norm_num [Complex.star_def, Complex.conj_I]
    ring_nf
    norm_num [Complex.I_sq]

include x hx in
/-- Every irreducible constituent of the first actual induced function belongs to the prescribed principal block. -/
theorem actualInducedOne_constituent_mem (χ : ClassFunction G)
    (hχ : IsIrreducibleCharacter χ)
    (hcoeff : scalarProduct G (actualInducedOne S P) χ ≠ 0) :
    ∃ i : d.I, i ∈ d.block ∧ ∀ g, χ g = d.chi i (ConjClasses.mk g) :=
  constituent_mem_of_eq d _ _ _ _ _ χ (actualInducedOne_eq_kernels S P x hx d) hχ hcoeff

include x hx in
/-- Every irreducible constituent of the second actual induced function belongs to the prescribed principal block. -/
theorem actualInducedTwo_constituent_mem (χ : ClassFunction G)
    (hχ : IsIrreducibleCharacter χ)
    (hcoeff : scalarProduct G (actualInducedTwo S P) χ ≠ 0) :
    ∃ i : d.I, i ∈ d.block ∧ ∀ g, χ g = d.chi i (ConjClasses.mk g) :=
  constituent_mem_of_eq d _ _ _ _ _ χ (actualInducedTwo_eq_kernels S P x hx d) hχ hcoeff
end Stellmacher.Recognition.FongWreathedInduction
