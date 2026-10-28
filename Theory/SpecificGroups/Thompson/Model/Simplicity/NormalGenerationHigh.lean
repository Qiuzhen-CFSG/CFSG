module

public import Theory.SpecificGroups.Thompson.Model.Simplicity.PrimeRepresentatives
public import Theory.SpecificGroups.Thompson.Model.Simplicity.Reduction
public import Theory.SpecificGroups.Thompson.Model.Simplicity.NormalGenerationHigh.Word31

/-!
# Normal generation by the high prime-class words of the Thompson model

For the proposed 7A and 13A words, killing the word in a quotient identifies
coprime powers of `ab` and `ab²`. The relations `a² = b³ = (ab)¹⁹ = 1` then
kill `ab`. The 19A word is `ab` itself. For 31A–B, a kernel-checked coset-word
trace kills `a` using the same three relations and the killed word.

No assertion about the words' orders or conjugacy classes is used. The product
relation remains an explicit hypothesis, to be supplied by a matrix certificate.
Source words: https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Th/ ; see also
`NormalGenerationHigh/source/README.md` for the deduction trace.
-/

namespace Thompson.Simplicity

section
variable {G : Type*} [Group G] (a b : G) (ha : a ^ 2 = 1) (hb : b ^ 3 = 1)
    (hab : (a * b) ^ 19 = 1)

include ha hb hab

private lemma ab2_pow_nineteen : (a * b ^ 2) ^ 19 = 1 := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ha)
  have hbi : b⁻¹ = b ^ 2 := inv_eq_of_mul_eq_one_right (by simpa [pow_succ, mul_assoc] using hb)
  have heq : a * b ^ 2 = a * (a * b)⁻¹ * a⁻¹ := by simp [hai, hbi, mul_assoc, ← pow_two, ha]
  rw [heq, conj_pow, inv_pow, hab]
  simp

private lemma ab_eq_one_of_seven_word_eq_one (h : (a * b)^6 * (a * b^2)^6 = 1) : a * b = 1 := by
  have hy := ab2_pow_nineteen a b ha hb hab
  have heq : (a * b)^6 = ((a * b^2)⁻¹)^6 := by
    rw [inv_pow]
    exact eq_inv_of_mul_eq_one_left h
  have hp := congrArg (fun z : G => z ^ 16) heq
  rw [← pow_mul, ← pow_mul] at hp
  have hx96 : (a * b)^96 = (a * b)^1 := pow_eq_pow_of_modEq (by decide : 96 ≡ 1 [MOD 19]) hab
  have hyi : ((a * b^2)⁻¹)^19 = 1 := by rw [inv_pow, hy, inv_one]
  have hy96 : ((a * b^2)⁻¹)^96 = ((a * b^2)⁻¹)^1 :=
    pow_eq_pow_of_modEq (by decide : 96 ≡ 1 [MOD 19]) hyi
  change (a * b)^96 = ((a * b^2)⁻¹)^96 at hp
  rw [hx96, hy96, pow_one, pow_one] at hp
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ha)
  have hbi : (b^2)⁻¹ = b := inv_eq_of_mul_eq_one_right (by simpa only [← pow_succ] using hb)
  have hcomm : a * b = b * a := by
    simpa only [mul_inv_rev, hai, hbi] using hp
  have hx6 : (a * b)^6 = 1 := by
    rw [(show Commute a b from hcomm).mul_pow]
    have ha6 : a^6 = 1 := by
      calc a^6 = (a^2)^3 := by rw [← pow_mul]
           _ = 1 := by rw [ha, one_pow]
    have hb6 : b^6 = 1 := by
      calc b^6 = (b^3)^2 := by rw [← pow_mul]
           _ = 1 := by rw [hb, one_pow]
    rw [ha6, hb6, one_mul]
  exact (pow_eq_one_iff_of_coprime (by decide : Nat.Coprime 6 19)).mp ⟨hx6, hab⟩

private lemma ab_eq_one_of_thirteen_word_eq_one (h : (a * b)^9 * (a * b^2)^3 = 1) : a * b = 1 := by
  have hy := ab2_pow_nineteen a b ha hb hab
  have heq : (a * b^2)^3 = ((a * b)⁻¹)^9 := by
    rw [inv_pow]
    exact eq_inv_of_mul_eq_one_right h
  have hp := congrArg (fun z : G => z ^ 13) heq
  rw [← pow_mul, ← pow_mul] at hp
  have hy39 : (a * b^2)^39 = (a * b^2)^1 :=
    pow_eq_pow_of_modEq (by decide : 39 ≡ 1 [MOD 19]) hy
  have hxi : ((a * b)⁻¹)^19 = 1 := by rw [inv_pow, hab, inv_one]
  have hx117 : ((a * b)⁻¹)^117 = ((a * b)⁻¹)^3 :=
    pow_eq_pow_of_modEq (by decide : 117 ≡ 3 [MOD 19]) hxi
  change (a * b^2)^39 = ((a * b)⁻¹)^117 at hp
  rw [hy39, hx117, pow_one] at hp
  have hbpow : b = ((a * b)⁻¹)^4 := by
    calc b = (a * b)⁻¹ * (a * b^2) := by group
         _ = ((a * b)⁻¹)^4 := by rw [hp, ← pow_succ']
  have hx12 : ((a * b)⁻¹)^12 = 1 := by
    calc ((a * b)⁻¹)^12 = (((a * b)⁻¹)^4)^3 := by rw [← pow_mul]
         _ = 1 := by rw [← hbpow, hb]
  have hh := (pow_eq_one_iff_of_coprime (by decide : Nat.Coprime 12 19)).mp ⟨hx12, hxi⟩
  exact inv_eq_one.mp hh
end

private theorem normal_eq_top_of_ab_mem (N : Subgroup Model) [N.Normal]
    (hab : generatorA * generatorB ∈ N) : N = ⊤ := by
  have hle : Subgroup.normalClosure ({generatorA * generatorB} : Set Model) ≤ N :=
    Subgroup.normalClosure_le_normal (by simpa using hab)
  rw [normalClosure_ab] at hle
  exact top_unique hle

private theorem normalClosure_primeRepresentative_five
    (hab19 : (generatorA * generatorB)^19 = 1) :
    Subgroup.normalClosure ({primeRepresentative 5} : Set Model) = ⊤ := by
  let N := Subgroup.normalClosure ({primeRepresentative 5} : Set Model)
  let q := QuotientGroup.mk' N
  have hw : q (primeRepresentative 5) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure (Set.mem_singleton _))
  change q ((generatorA * generatorB)^6 * (generatorA * generatorB^2)^6) = 1 at hw
  have hab : q (generatorA * generatorB) = 1 := by
    rw [map_mul]
    exact ab_eq_one_of_seven_word_eq_one (q generatorA) (q generatorB)
      (by simpa using congrArg q generatorA_sq)
      (by simpa using congrArg q generatorB_cube)
      (by simpa using congrArg q hab19)
      (by simpa only [map_mul, map_pow] using hw)
  exact normal_eq_top_of_ab_mem N ((QuotientGroup.eq_one_iff _).mp hab)

private theorem normalClosure_primeRepresentative_six
    (hab19 : (generatorA * generatorB)^19 = 1) :
    Subgroup.normalClosure ({primeRepresentative 6} : Set Model) = ⊤ := by
  let N := Subgroup.normalClosure ({primeRepresentative 6} : Set Model)
  let q := QuotientGroup.mk' N
  have hw : q (primeRepresentative 6) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure (Set.mem_singleton _))
  change q ((generatorA * generatorB)^9 * (generatorA * generatorB^2)^3) = 1 at hw
  have hab : q (generatorA * generatorB) = 1 := by
    rw [map_mul]
    exact ab_eq_one_of_thirteen_word_eq_one (q generatorA) (q generatorB)
      (by simpa using congrArg q generatorA_sq)
      (by simpa using congrArg q generatorB_cube)
      (by simpa using congrArg q hab19)
      (by simpa only [map_mul, map_pow] using hw)
  exact normal_eq_top_of_ab_mem N ((QuotientGroup.eq_one_iff _).mp hab)

private theorem normalClosure_primeRepresentative_eight
    (hab19 : (generatorA * generatorB)^19 = 1) :
    Subgroup.normalClosure ({primeRepresentative 8} : Set Model) = ⊤ := by
  let N := Subgroup.normalClosure ({primeRepresentative 8} : Set Model)
  let q := QuotientGroup.mk' N
  have hw : q (word "abababababababbabbabababababbababababababababb") = 1 :=
    (QuotientGroup.eq_one_iff (primeRepresentative 8)).mpr
      (Subgroup.subset_normalClosure (Set.mem_singleton _))
  have ha : generatorA ∈ N := (QuotientGroup.eq_one_iff _).mp
    (generatorA_eq_one_of_word31 q hab19 hw)
  have hle : Subgroup.normalClosure ({generatorA} : Set Model) ≤ N :=
    Subgroup.normalClosure_le_normal (by simpa using ha)
  rw [normalClosure_generatorA_of_ab19 hab19] at hle
  exact top_unique hle

/-- Each proposed prime representative with index five through eight normally
generates, provided the standard product relation is certified. -/
public theorem normalClosure_primeRepresentative_high
    (hab19 : (generatorA * generatorB)^19 = 1)
    (i : Fin 9) (hi : 5 ≤ i.val) :
    Subgroup.normalClosure ({primeRepresentative i} : Set Model) = ⊤ := by
  have hcases : i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · exact normalClosure_primeRepresentative_five hab19
  · exact normalClosure_primeRepresentative_six hab19
  · exact normalClosure_ab
  · exact normalClosure_primeRepresentative_eight hab19

end Thompson.Simplicity
