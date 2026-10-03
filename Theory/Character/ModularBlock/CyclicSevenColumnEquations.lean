module

public import Theory.Character.ModularBlock.CyclicSevenIntegralData
public import Theory.Character.CyclicSevenPeriodNorms

/-!
# Ordinary column equations for integral order-seven restrictions

The nonidentity Sylow elements have centralizer order seven. Ordinary column
orthogonality, split into the three exceptional rows and their complement,
therefore combines with the local period moment five to give the quadratic
integer equation. Orthogonality between the identity and a nonidentity column
gives the degree-weighted integer equation. All complementary degrees are
natural numbers because the rows are actual ordinary characters.

This constructs `ColumnEquations` from explicit `IntegralValues`; it neither
assumes nor enumerates the five ordinary rows.

Source: Fong (1967), printed p.75, citing Brauer (1942).
Adapted from `Theory.Character.ModularBlock.CyclicThirteenColumnEquations`,
whose source is Alperin--Brauer--Gorenstein, III.8, pp.116--117.
-/

public section
open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite
namespace ModularBlock.CyclicSeven
open PrimeBlockConstruction CyclicSevenNormalizer
variable {G : Type*} [Group G] [Finite G]
variable {d : PrimeCongruenceBlockData 7 G} {P : Sylow 7 G}
  {s : PeriodRows (P : Subgroup G)}

private theorem sum_split {A B M : Type*} [Fintype A] [Fintype B] [AddCommMonoid M]
    (e : A ↪ B) (f : B → M) :
    ∑ i, f i = (∑ a, f (e a)) + ∑ b : {b // b ∉ Set.range e}, f b.val := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (fun b => b ∈ Set.range e) f]
  congr 1
  symm
  convert Fintype.sum_equiv (Equiv.ofInjective e e.injective) (fun a => f (e a)) (fun b => f b.val) (fun _ => rfl) using 1
  congr
  exact Subsingleton.elim _ _

  congr
  exact Subsingleton.elim _ _

private theorem centralizer_card (hP : Nat.card P = 7)
    (hC : Subgroup.centralizer (P : Set G) = (P : Subgroup G)) (u : P) (hu : u ≠ 1) :
    Nat.card {x : G // x * (u : G) = (u : G) * x} = 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hpow := pow_card_eq_one' (x := u)
  change u ^ Nat.card (P : Subgroup G) = 1 at hpow
  rw [hP] at hpow
  have huorder : orderOf (u : G) = 7 := by
    exact (Subgroup.orderOf_coe u).trans (orderOf_eq_prime
      hpow hu)
  have hz : Subgroup.zpowers (u : G) = (P : Subgroup G) := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr u.property)
    rw [Nat.card_zpowers, huorder]
    exact hP.le
  have hc : Subgroup.centralizer ({(u : G)} : Set G) = (P : Subgroup G) := by
    rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure, hz]
    exact hC
  calc
    _ = Nat.card (Subgroup.centralizer ({(u : G)} : Set G)) :=
      Nat.card_congr (Equiv.subtypeEquivRight
        (fun _ => Subgroup.mem_centralizer_singleton_iff.symm))
    _ = 7 := by rw [hc]; exact hP

private theorem column_norm (hP : Nat.card P = 7)
    (hC : Subgroup.centralizer (P : Set G) = (P : Subgroup G)) (u : P) (hu : u ≠ 1) :
    ∑ i, Complex.normSq (d.chi i (ConjClasses.mk (u : G))) = 7 := by
  classical
  obtain ⟨b, hb⟩ := completeFamily_form_basis d.complete
  have hc := centralizer_card hP hC u hu
  have hh := class_card_mul_centralizer_card (u : G)
  rw [hc] at hh
  have hpos : 0 < Nat.card (ConjClasses.mk (u : G)).carrier := by
    let : Nonempty (ConjClasses.mk (u : G)).carrier := ⟨⟨u, ConjClasses.mem_carrier_mk⟩⟩
    exact Nat.card_pos
  have he : (∑ i, d.chi i (ConjClasses.mk (u : G)) *
      star (d.chi i (ConjClasses.mk (u : G)))) = (7 : ℂ) := by
    rw [basis_sum_character_projection d.complete b hb, classProjection_apply_eq]
    apply (div_eq_iff (by exact_mod_cast hpos.ne')).mpr
    have hh' : (Nat.card (ConjClasses.mk (u : G)).carrier : ℂ) * 7 = (Nat.card G : ℂ) := by
      exact_mod_cast hh
    linear_combination -hh'
  have hr := congrArg Complex.re he
  simpa [Complex.re_sum, Complex.star_def, Complex.mul_conj] using hr

private theorem degree_column (u : P) (hu : u ≠ 1) :
    ∑ i, d.chi i (ConjClasses.mk (u : G)) * star (d.chi i (ConjClasses.mk 1)) = 0 := by
  classical
  obtain ⟨b, hb⟩ := completeFamily_form_basis d.complete
  rw [basis_sum_character_projection d.complete b hb]
  apply classProjection_apply_ne
  intro he
  apply hu
  apply Subtype.ext
  exact isConj_one_left.mp (ConjClasses.mk_eq_mk_iff_isConj.mp he)

/-- Ordinary orthogonality supplies both integer equations for the integral
restriction data of a self-centralizing Sylow subgroup of order seven. -/
theorem IntegralValues.columnEquations (v : IntegralValues d P s) (hP : Nat.card P = 7)
    (hC : Subgroup.centralizer (P : Set G) = (P : Subgroup G)) :
    Nonempty (ColumnEquations v) := by
  classical
  let R := {i : d.I // i ∉ Set.range v.exceptionalRows}
  have hn (i : R) : ∃ n : ℕ, d.chi i.val (ConjClasses.mk 1) = (n : ℂ) := by
    obtain ⟨n, ρ, hρ⟩ := (d.complete.1 i.val).1
    refine ⟨n, ?_⟩
    rw [hρ]
    change ρ.character 1 = (n : ℂ)
    simp
  choose n hn using hn
  let u := s.generator
  have hu : u ≠ 1 := s.generator_ne_one
  let z : Fin 3 → ℂ := fun k => s.chi k (ConjClasses.mk (inclusion (P : Subgroup G) u))
  have hz : ∑ k, z k = -1 := s.toRows.sum_restriction hP u hu
  have hzn : ∑ k, Complex.normSq (z k) = 5 := s.toRows.sum_normSq_restriction hP u hu
  have he : ∑ k, d.chi (v.exceptionalRows k) (ConjClasses.mk (u : G)) =
      (3 * v.shift - v.sign : ℤ) := by
    simp_rw [v.exceptional_value _ u hu]
    change (∑ k, ((v.shift : ℂ) + (v.sign : ℂ) * z k)) = _
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hz]
    simp
    ring
  have hex : ∑ k, Complex.normSq (d.chi (v.exceptionalRows k) (ConjClasses.mk (u : G))) =
      ((3 * v.shift ^ 2 - 2 * v.sign * v.shift + 5 : ℤ) : ℝ) := by
    have hzr : ∑ k, (z k).re = -1 := by
      simpa using congrArg Complex.re hz
    have hp (k : Fin 3) :
        Complex.normSq ((v.shift : ℂ) + (v.sign : ℂ) * z k) =
        (v.shift : ℝ)^2 + Complex.normSq (z k) +
          2 * (v.sign : ℝ) * v.shift * (z k).re := by
      rcases v.sign_unit with h | h <;>
        simp [h, Complex.normSq, pow_two] <;> ring
    simp_rw [v.exceptional_value _ u hu]
    change (∑ k, Complex.normSq ((v.shift : ℂ) + (v.sign : ℂ) * z k)) = _
    simp_rw [hp]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hzn, hzr]
    simp
    ring
  refine ⟨⟨n, hn, ?_, ?_⟩⟩
  · have hh := column_norm (d := d) hP hC u hu
    rw [sum_split v.exceptionalRows, hex] at hh
    simp_rw [v.remainder_value _ u hu, Complex.normSq_intCast] at hh
    have hreal : (((∑ i, v.remainder i ^ 2) + 3 * v.shift ^ 2 -
        2 * v.sign * v.shift : ℤ) : ℝ) = 2 := by
      push_cast at hh ⊢
      simp_rw [pow_two] at *
      have hh' : 3 * ((v.shift : ℝ) * v.shift) - 2 * v.sign * v.shift + 5 +
          (∑ i, (v.remainder i : ℝ) * v.remainder i) = 7 := by
        convert hh using 1
        congr
        exact Subsingleton.elim _ _
      linarith only [hh']
    exact_mod_cast hreal
  · have hh := degree_column (d := d) u hu
    rw [sum_split v.exceptionalRows] at hh
    simp_rw [v.degree, star_natCast] at hh
    rw [← Finset.sum_mul, he] at hh
    have hr : (∑ i : R, d.chi i.val (ConjClasses.mk (u : G)) *
        star (d.chi i.val (ConjClasses.mk 1))) =
        ((∑ i : R, (n i : ℤ) * v.remainder i : ℤ) : ℂ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro i _
      rw [hn, v.remainder_value _ u hu, star_natCast]
      ring
    have hh' : (3 * v.shift - v.sign : ℤ) * (v.commonDegree : ℂ) +
        (∑ i : R, d.chi i.val (ConjClasses.mk (u : G)) *
        star (d.chi i.val (ConjClasses.mk 1))) = 0 := by
      convert hh using 1
      congr
      exact Subsingleton.elim _ _
    rw [hr] at hh'
    have hc : (((∑ i : R, (n i : ℤ) * v.remainder i) +
        (3 * v.shift - v.sign) * (v.commonDegree : ℤ) : ℤ) : ℂ) = 0 := by
      push_cast at hh' ⊢
      linear_combination hh'
    exact_mod_cast hc
end ModularBlock.CyclicSeven
