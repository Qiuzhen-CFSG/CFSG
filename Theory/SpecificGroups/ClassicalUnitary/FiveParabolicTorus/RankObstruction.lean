module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicTorus
public import Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel
public import Theory.GroupTheory.QuasithinBasic

/-!
# All obstruction primes in the unitary-five line parabolic

The diagonal special-unitary torus is faithful before projectivization, and
its projective kernel has order at most five. For fifth-primary parameters
we use the cube of the 25th-root group: the image has order at least 5^5 and
exponent dividing 25, hence generator rank at least three. Together with the
existing prime-to-five embedding this proves the bound for every prime divisor
of (q+1)/gcd(q+1,5), retaining the literal line parabolic and scalar quotient.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, Lemma
A.2.18, printed p.40. This rank argument does not require a direct-product
Levi decomposition.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
open scoped IsMulCommutative
namespace Theory.SpecificGroups.UnitaryFive
variable {F : Type*} [Field F]
variable (J : HermitianForm 5 F) (hJ : J.form = 1)
variable (C : Subgroup Fˣ) (hC : ∀ u : C, J.conj (u.val : F) * (u.val : F) = 1)

theorem torusSpecial_injective : Function.Injective (torusSpecial J hJ C hC) := by
  intro a b hab
  have hd (i : Fin 5) : torusEntries C a i = torusEntries C b i := by
    apply Subtype.ext
    apply Units.ext
    simpa [torusSpecial, torusMatrix_val] using
      congrArg (fun x : J.specialSubgroup => x.val.val i i) hab
  funext i
  fin_cases i
  · exact hd 0
  · exact hd 2
  · exact hd 3

variable [Finite F]

theorem torusParabolic_card_ker_le_five {q : ℕ}
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q) :
    Nat.card (torusParabolic J hJ C hC).ker ≤ 5 := by
  let g : (torusParabolic J hJ C hC).ker →
      (ClassicalUnitary.ProjectiveKernel.project J).ker := fun a =>
    ⟨torusSpecial J hJ C hC a.val, by
      apply Subtype.ext
      exact congrArg (fun x : lineParabolic J => x.val.val) a.property⟩
  have hg : Function.Injective g := by
    intro a b h
    apply Subtype.ext
    exact torusSpecial_injective J hJ C hC (congrArg Subtype.val h)
  exact (Nat.card_le_card_of_injective g hg).trans (by
    rw [ClassicalUnitary.ProjectiveKernel.card_project_kernel J hconj hcard]
    exact Nat.gcd_le_left _ (by decide))

include hJ in
theorem primeRank_lineParabolic_five_ge_of_twentyfive_dvd {q : ℕ}
    (hcard : Nat.card F = q ^ 2) (hq : 2 ≤ q)
    (hconj : ∀ x, J.conj x = x ^ q) (hd : 25 ∣ q + 1) :
    3 ≤ primeRank 5 (lineParabolic J) := by
  let : Finite (GL (Fin 5) F) := Finite.of_injective Units.val Units.val_injective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective (project J) (project_surjective J)
  have hc : Nat.card (rootsOfUnity 25 F) = 25 := by
    apply FiniteField.card_rootsOfUnity_of_dvd
    rw [hcard]
    have he : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      nlinarith [Nat.sub_add_cancel (show 1 ≤ q by omega),
        Nat.sub_add_cancel (show 1 ≤ q ^ 2 by nlinarith)]
    rw [he]
    exact dvd_mul_of_dvd_left hd _
  have hn (u : rootsOfUnity 25 F) : J.conj (u.val : F) * (u.val : F) = 1 := by
    rw [hconj, ← pow_succ]
    obtain ⟨d, hd⟩ := hd
    rw [hd, pow_mul, (mem_rootsOfUnity' 25 u.val).mp u.property, one_pow]
  let f := torusParabolic J hJ (rootsOfUnity 25 F) hn
  have hpow (a : Fin 3 → rootsOfUnity 25 F) : a ^ 25 = 1 := by
    funext i
    exact Subtype.ext ((mem_rootsOfUnity 25 _).mp (a i).property)
  have hAp : IsPGroup 5 (Fin 3 → rootsOfUnity 25 F) := fun a => ⟨2, hpow a⟩
  have hr := f.range.rank_le_primeRank 5
    (hAp.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  suffices 3 ≤ Group.rank f.range from this.trans hr
  by_contra h
  have hle : Group.rank f.range ≤ 2 := by omega
  have hpowR (a : f.range) : a ^ 25 = 1 := by
    obtain ⟨a, rfl⟩ := f.rangeRestrict_surjective a
    rw [← map_pow, hpow, map_one]
  have hbound : Nat.card f.range ≤ 625 :=
    (Nat.le_of_dvd (by positivity) (card_dvd_exponent_pow_rank' f.range hpowR)).trans
      (Nat.pow_le_pow_right (by decide) hle)
  have hk : Nat.card f.ker ≤ 5 :=
    torusParabolic_card_ker_le_five J hJ _ hn hcard hconj
  have hprod : Nat.card f.ker * Nat.card f.range = 15625 := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index, Nat.card_fun, hc, Nat.card_fin]
    norm_num
  nlinarith

include hJ in
theorem primeRank_lineParabolic_ge_of_dvd_quotient {q p : ℕ}
    (hcard : Nat.card F = q ^ 2) (hq : 2 ≤ q)
    (hconj : ∀ x, J.conj x = x ^ q) (hp : p.Prime)
    (hd : p ∣ (q + 1) / Nat.gcd (q + 1) 5) :
    3 ≤ primeRank p (lineParabolic J) := by
  have hdq : p ∣ q + 1 := hd.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
  by_cases h5 : p = 5
  · subst p
    have hg : Nat.gcd (q + 1) 5 = 5 := Nat.gcd_eq_right_iff_dvd.mpr hdq
    rw [hg] at hd
    apply primeRank_lineParabolic_five_ge_of_twentyfive_dvd J hJ hcard hq hconj
    simpa using Nat.mul_dvd_of_dvd_div hdq hd
  · exact primeRank_lineParabolic_ge_of_prime_ne_five J hJ hcard hq hconj hp hdq h5
end Theory.SpecificGroups.UnitaryFive
