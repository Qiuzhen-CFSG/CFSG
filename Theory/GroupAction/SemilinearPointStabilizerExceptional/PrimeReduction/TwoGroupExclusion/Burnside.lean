module

public import Theory.Character.BurnsideIntegrality
public import Theory.Character.BurnsideScalar
public import Theory.Character.Orthogonality
public import Theory.Character.Cyclotomic
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Burnside's prime-power conjugacy-class argument

In a nonabelian finite simple group, every nonprincipal irreducible complex
representation is faithful. On an element with a p-power conjugacy class,
Burnside's scalar-or-zero criterion therefore forces every nonprincipal
character of degree prime to p to vanish. Second orthogonality would then
make -1/p an algebraic integer, which is impossible.

Unlike the existing involution-specific argument, this theorem applies to
elements of arbitrary order, including elements of the odd scalar subgroup.
It is consumed by the solvability induction in `TwoGroupExclusion.Solvability`.

Source: Isaacs, Character Theory of Finite Groups, 3.8–3.9, as applied in
GLS, Volume 4, Chapter 1, Lemma 3.8(b), `refs/KGroup/GLS4/Chapter1.tex`,
lines 419–430. The scalar criterion is the independently proved
`Theory.Character.BurnsideScalar`.
-/

noncomputable section
open scoped BigOperators
open Representation

private theorem finrank_one_of_ker_top
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (hker : ρ.ker = ⊤) : Module.finrank ℂ V = 1 := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have hρ : ρ = 1 := MonoidHom.ker_eq_top_iff.mp hker
  let d := Module.finrank ℂ V
  have hcf (x : G) : (characterClassFunction ρ) (ConjClasses.mk x) = (d : ℂ) := by
    change ρ.character x = (d : ℂ)
    rw [hρ]
    simp [Representation.character, d]
  have hnorm := (irreducible_iff_character_norm_one ρ).1 inferInstance
  rw [classFunctionInner] at hnorm
  simp_rw [hcf] at hnorm
  have hcardne : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp [hcardne] at hnorm
  norm_num [Complex.normSq_eq_conj_mul_self] at hnorm
  have hnormNat : d * d = 1 := by exact_mod_cast hnorm
  nlinarith

/-- Burnside's prime-power class argument: a finite simple group with a
nonidentity element whose conjugacy class has prime-power size is abelian. -/
public theorem IsSimpleGroup.isMulCommutative_of_prime_power_conjClass
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (s : G) (hs : s ≠ 1) {p n : ℕ} (hp : p.Prime)
    (hclass : Nat.card (ConjClasses.mk s).carrier = p ^ n) :
    IsMulCommutative G := by
  classical
  by_contra hna
  obtain ⟨ι, hι, χ, hχ, horth⟩ := second_orthogonality (G := G)
  let : Fintype ι := hι
  choose d ρ hχρ using fun i => (hχ.1 i).1
  have hirr (i : ι) : (ρ i).IsIrreducible := by
    apply (irreducible_iff_character_norm_one (ρ i)).2
    simpa [hχρ i] using (hχ.1 i).2
  have hval (i : ι) (x : G) : χ i (ConjClasses.mk x) = (ρ i).character x := by
    rw [hχρ i]
    rfl
  have hdeg (i : ι) : χ i (ConjClasses.mk (1 : G)) = (d i : ℂ) := by
    rw [hval]
    simp
  let triv : Representation ℂ G ℂ := Representation.trivial ℂ G ℂ
  obtain ⟨i₀, hi₀⟩ := hχ.2.1 (characterClassFunction triv)
    (isIrreducibleCharacter_characterClassFunction triv trivial_complex_irreducible)
  have htriv (x : G) : χ i₀ (ConjClasses.mk x) = 1 := by
    rw [hi₀]
    change triv.character x = 1
    simp [Representation.character, triv]
  have hfaith (i : ι) (hi : i ≠ i₀) : Function.Injective (ρ i) := by
    apply (ρ i).ker_eq_bot_iff.mp
    rcases (MonoidHom.normal_ker (ρ i)).eq_bot_or_eq_top with hk | hk
    · exact hk
    · exfalso
      apply hi
      let := hirr i
      have hd : d i = 1 := by simpa using finrank_one_of_ker_top (ρ i) hk
      have hrho : ρ i = 1 := MonoidHom.ker_eq_top_iff.mp hk
      apply hχ.2.2
      rw [hi₀, hχρ i]
      ext c
      obtain ⟨x, rfl⟩ := ConjClasses.exists_rep c
      change (ρ i).character x = triv.character x
      rw [hrho]
      simp [Representation.character, hd, triv]
  have hzero (i : ι) (hi : i ≠ i₀) (hpd : ¬ p ∣ d i) : (ρ i).character s = 0 := by
    let := hirr i
    have hc : (Module.finrank ℂ (Fin (d i) → ℂ)).Coprime
        (Nat.card (ConjClasses.mk s).carrier) := by
      simpa [hclass] using (hp.coprime_iff_not_dvd.mpr hpd).symm.pow_right n
    have hint := (ρ i).isIntegral_character_div_finrank_of_coprime_class_card s hc
    have hpow : ρ i s ^ orderOf s = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    rcases burnside_scalar_or_zero (d i) (ρ i s) (orderOf s) (orderOf_pos s).ne' hpow
      (by simpa [Representation.character] using hint) with hz | ⟨a, ha⟩
    · exact hz
    · have hcentral : s ∈ Subgroup.center G := by
        apply Subgroup.mem_center_iff.mpr
        intro y
        apply hfaith i hi
        simp only [map_mul, ha]
        ext v
        simp
      rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with hz | hz
      · exact (hs (by simpa [hz] using hcentral)).elim
      · exact (hna (Subgroup.center_eq_top_iff.mp hz)).elim
  have hclassne : ConjClasses.mk s ≠ ConjClasses.mk (1 : G) := by
    intro h
    exact hs (isConj_one_left.mp (ConjClasses.mk_eq_mk_iff_isConj.mp h))
  have hsum : ∑ i : ι, χ i (ConjClasses.mk s) * (d i : ℂ) = 0 := by
    simpa only [hdeg, star_natCast] using (horth s 1).2 hclassne
  have hterm (i : ι) (hi : i ≠ i₀) :
      IsIntegral ℤ (χ i (ConjClasses.mk s) * (d i : ℂ) / (p : ℂ)) := by
    rw [hval]
    by_cases hpd : p ∣ d i
    · obtain ⟨k, hk⟩ := hpd
      have he : (ρ i).character s * (d i : ℂ) / (p : ℂ) =
          (ρ i).character s * (k : ℂ) := by
        have hcast : (d i : ℂ) = (p : ℂ) * (k : ℂ) := by exact_mod_cast hk
        rw [hcast]
        field_simp [Nat.cast_ne_zero.mpr hp.ne_zero]
      rw [he]
      exact (representation_character_isIntegral (ρ i) s).mul (isIntegral_natCast _)
    · rw [hzero i hi hpd]
      simpa only [zero_mul, zero_div] using (isIntegral_zero : IsIntegral ℤ (0 : ℂ))
  have hrest : IsIntegral ℤ
      (∑ i ∈ Finset.univ.erase i₀, χ i (ConjClasses.mk s) * (d i : ℂ) / (p : ℂ)) := by
    exact IsIntegral.sum _ (fun i hi => hterm i (Finset.ne_of_mem_erase hi))
  have hsplit : (1 : ℂ) +
      ∑ i ∈ Finset.univ.erase i₀, χ i (ConjClasses.mk s) * (d i : ℂ) = 0 := by
    have hd₀ : (d i₀ : ℂ) = 1 := (hdeg i₀).symm.trans (htriv 1)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)] at hsum
    simpa only [htriv, hd₀, mul_one] using hsum
  have hresteq : (∑ i ∈ Finset.univ.erase i₀,
      χ i (ConjClasses.mk s) * (d i : ℂ) / (p : ℂ)) = -1 / (p : ℂ) := by
    rw [← Finset.sum_div]
    congr 1
    exact eq_neg_of_add_eq_zero_right hsplit
  rw [hresteq] at hrest
  have hdvd : (p : ℤ) ∣ -1 := integer_division_of_integral_quotient
    (by exact_mod_cast hp.ne_zero) (by simpa using hrest)
  have : p ∣ 1 := Int.natCast_dvd_natCast.mp (dvd_neg.mp hdvd)
  exact hp.not_dvd_one this

