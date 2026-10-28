module
public import Theory.SpecificGroups.PSL2.PrimeSylowComponents
public import Theory.SpecificGroups.PSL2.QuadraticNonsolvableSylowOvergroups

/-!
# Full-Sylow component tests in quadratic odd PSL₂

The full-Sylow Dickson sieve leaves only prime-field PSL₂ and PGL₂ as
nonsolvable proper overgroups. Their perfect subnormal subgroups fill the
actual PSL₂ subgroup. This proves uniqueness and forces a factor three,
closing the quadratic-field containing row of the Chapter 10 pair argument.
Source: Aschbacher--Smith A.3.12(8) and 10.2.6, pp.47--48,748--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.PSL2.QuadraticSylowComponents
variable {F : Type} [Field F] [Finite F] {p : ℕ}

private theorem three_dvd_card (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p ^ 2) :
    3 ∣ Nat.card PSL(2,F) := by
  rw [GorensteinWalter.psl2_card_formula F ⟨p,2,hp,ho,by decide,hF⟩]
  let q := Nat.card F
  have hpos : 1 ≤ q := Nat.card_pos
  have hpowpos : 1 ≤ q ^ 2 := one_le_pow₀ hpos
  have hb : q % 6 < 6 := Nat.mod_lt q (by decide)
  have hc : q % 6 = 0 ∨ q % 6 = 1 ∨ q % 6 = 2 ∨ q % 6 = 3 ∨
      q % 6 = 4 ∨ q % 6 = 5 := by omega
  have hd : 6 ∣ q * (q ^ 2 - 1) := by
    apply Nat.dvd_of_mod_eq_zero
    rcases hc with h | h | h | h | h | h
    all_goals
      have hpow := Nat.pow_mod q 2 6
      rw [h] at hpow
      norm_num at hpow
      have hsub : (q ^ 2 - 1) % 6 = (q ^ 2 % 6 + 5) % 6 := by omega
      norm_num only [Nat.mul_mod,h,hsub,hpow]
  obtain ⟨n,hn⟩ := hd
  refine ⟨n,?_⟩
  change q * (q ^ 2 - 1) / 2 = 3 * n
  omega

/-- Every three-free full-Sylow overgroup in a quadratic odd projective line group is solvable. -/
theorem isSolvable_of_three_free (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p ^ 2)
    (S : Sylow 2 PSL(2,F)) (A : Subgroup PSL(2,F)) (hSA : (S : Subgroup _) ≤ A)
    (h3 : ¬ 3 ∣ Nat.card A) : Group.IsSolvable A := by
  classical
  by_contra hn
  let : Fact p.Prime := ⟨hp⟩
  by_cases ht : A = ⊤
  · exact h3 (by rw [ht,card_top]; exact three_dvd_card hp ho hF)
  have hfp : Nat.card (GaloisField p 1) = p := by
    simpa using GaloisField.card p 1 (by decide)
  rcases quadratic_nonsolvable_proper_sylow_models ho hF S A hSA ht hn with h | h
  all_goals obtain ⟨e⟩ := h
  · exact h3 (prime_model_three_dvd_card hp ho hfp e)
  · apply h3
    rw [Nat.card_congr e.toEquiv]
    exact (prime_model_three_dvd_card hp ho hfp (MulEquiv.refl _)).trans
      (card_dvd_of_injective Matrix.ProjectiveSpecialLinearGroup.toPGL
        Matrix.ProjectiveSpecialLinearGroup.toPGL_injective)

private theorem components_eq_in_prime_models {A : Type*} [Group A] [Finite A] [Fact p.Prime]
    (hp : p.Prime) (ho : Odd p) {B C : Subgroup A} (hB : B.IsCComponent) (hC : C.IsCComponent)
    (hm : Nonempty (A ≃* BenderSuzuki.MatrixGroups.PSL2MatrixGroup (GaloisField p 1)) ∨
      Nonempty (A ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p 1))) : B = C := by
  let : Fact p.Prime := ⟨hp⟩
  have hc : Nat.card (GaloisField p 1) = p := by
    simpa using GaloisField.card p 1 (by decide)
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p 1)) :=
    ⟨p,1,hp,ho,by decide,by simpa using hc⟩
  rcases hm with hm | hm
  all_goals obtain ⟨e⟩ := hm
  · have hb := hB.map_equiv e
    have hcc := hC.map_equiv e
    apply map_injective (f := e.toMonoidHom) e.injective
    exact (GorensteinWalter.psl2_perfect_subnormal_eq_top _ hodd _ hb.ne_bot hb.perfect hb.subnormal).2.trans
      (GorensteinWalter.psl2_perfect_subnormal_eq_top _ hodd _ hcc.ne_bot hcc.perfect hcc.subnormal).2.symm
  · have hb := hB.map_equiv e
    have hcc := hC.map_equiv e
    apply map_injective (f := e.toMonoidHom) e.injective
    exact (GorensteinWalter.pgl2_perfect_subnormal_eq_commutator _ hodd _ hb.ne_bot hb.perfect hb.subnormal).2.trans
      (GorensteinWalter.pgl2_perfect_subnormal_eq_commutator _ hodd _ hcc.ne_bot hcc.perfect hcc.subnormal).2.symm

/-- The quadratic full-Sylow sieve proves uniqueness, using the inherited ambient component. -/
theorem sylow_unique (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p ^ 2)
    (htop : (⊤ : Subgroup PSL(2,F)).IsCComponent) : SylowOvergroupComponentUnique PSL(2,F) := by
  intro S P hSP B C hB hC
  by_cases ht : P = ⊤
  · subst P
    exact (htop.eq_top_of_isCComponent hB).trans (htop.eq_top_of_isCComponent hC).symm
  let : Fact p.Prime := ⟨hp⟩
  apply components_eq_in_prime_models hp ho hB hC
  exact quadratic_nonsolvable_proper_sylow_models ho hF S P hSP ht (by
    intro h
    let := h
    exact hB.not_isSolvable inferInstance)

end Theory.PSL2.QuadraticSylowComponents
