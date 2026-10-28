module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.Irreducibility
public import Theory.Representation.SL2.PrimeFieldParameters.Unsigned
public import Theory.Representation.Quotient

/-!
# The cubic field ratio in the unequal binary hexagon

The actual radical representation is irreducible, faithful and has binary
dimension d=2a+2b, strictly between 2b and 4b. Transport it through the
proved pinning of the actual R_j by SL2(F). The all-characteristic
highest-weight theorem supplies b=s*t and d=s*c^t, where c is the product
of one repeated binary digit block and c≥2. Every nontrivial binary digit
product is even, so c is even.

The bounds give t<4. For t=1 or 2 they force c=2 and d=2b, a contradiction.
For t=3 they force c=2 and d=8s; hence a=s and b=3a. This binary argument
also excludes the degree-3b alternative directly, without applying an
odd-characteristic theorem or assuming later triality field pinnings.

Source: Fong--Seitz I (4B) and the final paragraph of (6E), printed pp.19--22,45.
The actual all-characteristic highest-weight and Frobenius-descent proof
is imported from PrimeFieldParameters.Unsigned. The CFSG companion supplies
the full unequal-linear structural output, including R_j itself, the literal
commutators and the irreducible action, on the original/geometric quotient.
Nonlinear local exclusions and the solvable effective-section source branches
remain separate obligations of the full binary hexagon family.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups MonoidAlgebra
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure

private theorem binary_digit_block_even {n m c t : ℕ} (ht : 0 < t) (hc : 2 ≤ c)
    (hprod : (∏ i : Fin m, (n / 2 ^ (i : ℕ) % 2 + 1)) = c^t) : Even c := by
  by_contra hn
  have hnot : ¬ 2 ∣ c^t := fun hd => hn ((even_iff_two_dvd).mpr (Nat.prime_two.dvd_of_dvd_pow hd))
  have hone (i : Fin m) : n / 2 ^ (i : ℕ) % 2 + 1 = 1 := by
    have hi : n / 2 ^ (i : ℕ) % 2 < 2 := Nat.mod_lt _ (by decide)
    by_contra he
    have htwo : n / 2 ^ (i : ℕ) % 2 + 1 = 2 := by omega
    have hh : (n / 2 ^ (i : ℕ) % 2 + 1) ∣ ∏ k : Fin m, (n / 2 ^ (k : ℕ) % 2 + 1) :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    rw [htwo,hprod] at hh
    exact hnot hh
  have he : c^t = 1 := hprod.symm.trans (Finset.prod_eq_one (fun i _ => hone i))
  have hh : c ≤ c^t := Nat.le_self_pow ht.ne' _
  omega

private theorem four_mul_le_two_power {t : ℕ} (ht : 4 ≤ t) : 4*t ≤ 2^t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih => rw [pow_succ]; nlinarith

private theorem cubic_of_even_block {a b s t c : ℕ}
    (ha : 0 < a) (hab : a < b) (_hs : 0 < s) (ht : 0 < t)
    (hc : 2 ≤ c) (heven : Even c) (hb : b = s*t) (hd : 2*a+2*b = s*c^t) : b = 3*a := by
  have hsmall : c^t < 4*t := by nlinarith
  have htlt : t < 4 := by
    by_contra! hh
    have hp := (four_mul_le_two_power hh).trans (Nat.pow_le_pow_left hc t)
    omega
  have ht123 : t = 1 ∨ t = 2 ∨ t = 3 := by omega
  rcases ht123 with rfl | rfl | rfl
  · have hc2 : c = 2 := by
      simp only [pow_one] at hsmall
      obtain ⟨k,hk⟩ := heven
      omega
    simp only [hc2,pow_one,mul_one] at hd hb
    omega
  · have hc2 : c = 2 := by
      by_contra! hh
      have hp := Nat.pow_le_pow_left (show 3 ≤ c by omega) 2
      norm_num at hp hsmall
      omega
    norm_num [hc2] at hd
    omega
  · have hc2 : c = 2 := by
      by_contra! hh
      have hp := Nat.pow_le_pow_left (show 3 ≤ c by omega) 3
      norm_num at hp hsmall
      omega
    norm_num [hc2] at hd
    omega

private theorem cubic_ratio_of_binary_irreducible
    {F V : Type*} [Field F] [Finite F] [CharP F 2]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2,F) V) [ρ.IsIrreducible]
    (hnt : ∃ g, ρ g ≠ 1) {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hF : Nat.card F = 2^b) (hd : Module.finrank (ZMod 2) V = 2*a+2*b) : b = 3*a := by
  obtain ⟨hs,n,hn,hsdiv,hperiod,hdim⟩ :=
    Representation.SL2.Unsigned.exists_primeField_highestWeight_parameters 2 ρ hnt b hF
  let s := Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,F)] ρ.asModule)
  change 0 < s at hs
  change s ∣ b at hsdiv
  obtain ⟨t,hbt⟩ := hsdiv
  have ht : 0 < t := by
    by_contra! hh
    have ht0 : t = 0 := by omega
    simp only [ht0,mul_zero] at hbt
    omega
  have hnlt : n.val < 2^(s*t) := by rw [←hbt,←hF]; exact n.isLt
  have hper : (2^(s*t)-1) ∣ n.val*(2^s-1) := by simpa only [hF,hbt] using hperiod
  obtain ⟨c,hc,hprod,_⟩ := Nat.exists_digit_product_pow_of_period 2 s t n.val
    (by decide) hs ht hn hnlt hper
  have heven := binary_digit_block_even ht hc hprod
  rw [hbt,hprod,hd] at hdim
  exact cubic_of_even_block ha hab hs ht hc heven hbt hdim

open RootCoordinates GTwoSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  {F E : Type*} [Field F] [Finite F] [CharP F 2]
  [Field E] [Finite E] [CharP E 2]

/-- The actual irreducible binary radical action forces the cubic ratio.
No odd-characteristic degree theorem or later cubic pinning is assumed. -/
theorem unequal_linear_cubic_ratio
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* PSL(2,F))
    (si : RootReflection Q split i) (sj : RootReflection Q split j)
    {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (hE : Nat.card E = 2^a) (hF : Nat.card F = 2^b) : b = 3*a := by
  let := linear_pair_radicalQuotient_elementary Q split hm i j hij μi μj
  let e := alignedPinning Q split j hKj μj sj
  let ρ₀ := radicalRepresentation Q split j hKj
  let ρ : Representation (ZMod 2) SL(2,F) (Additive (RadicalQuotient Q split j)) :=
    ρ₀.comp e.toMonoidHom
  let : ρ₀.IsIrreducible := unequal_linear_radical_irreducible Q split hm i j hij
    hKi hKj μi μj si sj ha hab hE hF
  let : ρ.IsIrreducible := (Representation.irreducible_comp_surjective_iff
    e.toMonoidHom e.surjective ρ₀).mpr inferInstance
  have hf : Function.Injective ρ :=
    (linear_radicalRepresentation_injective Q split j hKj μj sj hm i hij hKi).comp e.injective
  have hnt : ∃ g, ρ g ≠ 1 := by
    refine ⟨Theory.PSL2.SemilinearCoverage.uni 1,fun he => ?_⟩
    have hh := hf (he.trans (map_one ρ).symm)
    have h01 := congrArg (fun g : SL(2,F) => g.val 0 1) hh
    simp [Theory.PSL2.SemilinearCoverage.uni] at h01
  exact cubic_ratio_of_binary_irreducible ρ hnt ha hab hF
    (unequal_linear_radical_finrank Q split hm i j hij hKi hKj μi μj si sj ha hab hE hF)
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
