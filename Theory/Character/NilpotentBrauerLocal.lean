module

public import Theory.Character.NilpotentBrauerIdeal
public import Theory.Character.CharacterValues
public import Theory.Character.CyclicInductionFourier
public import Theory.GroupTheory.ElementaryCentralizer
public import Theory.GroupTheory.PrimeRegularDecomposition
public import Mathlib.RingTheory.Ideal.Int

/-!
# Local nonvanishing for integral Brauer induction

A maximal ideal of the algebraic integers has prime residue characteristic.
Modulo such an ideal, deleting a commuting prime-power part of a group element
preserves every virtual character value. To see this, decompose a representation
into eigenspaces of the prime-power part: its eigenvalues reduce to one, and the
traces of the other factor on these eigenspaces are algebraic integers.

Consequently local nonvanishing reduces to prime-regular elements. A finite
algebraic-integer combination of induced character values equal to an integer
outside the ideal guarantees that one of the induced characters survives.
For a prime-regular element, a Sylow subgroup of its centralizer together with
its cyclic subgroup supplies a nilpotent subgroup with cyclic retraction.
Cyclic Fourier orthogonality produces the required combination: its value is
the element order times the relative centralizer index, both prime to the
residue characteristic. Thus a nilpotent-induced character survives every
evaluation modulo a maximal ideal.

Source: Serre, *Linear Representations of Finite Groups*, Chapter 10,
the local character-ring proof of Brauer induction.
-/

public section

open scoped BigOperators
open Representation
noncomputable section
namespace BrauerInduction

/-- A maximal ideal of the algebraic integers contracts to a prime ideal `(p)` of ℤ. -/
theorem exists_residue_prime (P : Ideal (integralClosure ℤ ℂ)) (hP : P.IsMaximal) :
    ∃ p : ℕ, p.Prime ∧ ∀ n : ℕ, (n : integralClosure ℤ ℂ) ∈ P ↔ p ∣ n := by
  let := hP
  let : NeZero P := ⟨Ideal.IsMaximal.ne_bot_of_isIntegral_int P⟩
  refine ⟨Ideal.absNorm (P.under ℤ), Nat.absNorm_under_prime P, ?_⟩
  intro n
  simpa only [Int.cast_natCast, Int.natCast_dvd_natCast] using
    (Int.cast_mem_ideal_iff (I := P) (d := (n : ℤ)))

private theorem prime_power_root_sub_one_mem
    (P : Ideal (integralClosure ℤ ℂ)) (hP : P.IsMaximal) {p : ℕ} (hp : p.Prime)
    (hchar : ∀ n : ℕ, (n : integralClosure ℤ ℂ) ∈ P ↔ p ∣ n)
    (z : integralClosure ℤ ℂ) {k : ℕ} (hz : z ^ (p ^ k) = 1) : z - 1 ∈ P := by
  let := hP
  let : Fact p.Prime := ⟨hp⟩
  let : CharP ((integralClosure ℤ ℂ) ⧸ P) p := (charP_iff _ _).mpr (fun n => by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
    exact hchar n)
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub, map_one]
  apply sub_eq_zero.mpr
  have hpow : (Ideal.Quotient.mk P z - 1) ^ (p ^ k) = 0 := by
    rw [sub_pow_char_pow, ← map_pow, hz, map_one, one_pow, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero k hp.ne_zero)).mp hpow)

/-- Removing a commuting prime-power element preserves an ordinary character value
modulo a maximal ideal of residue characteristic `p`. -/
theorem representation_character_prime_part_sub_mem
    {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (P : Ideal (integralClosure ℤ ℂ)) (hP : P.IsMaximal) {p : ℕ} (hp : p.Prime)
    (hchar : ∀ n : ℕ, (n : integralClosure ℤ ℂ) ∈ P ↔ p ∣ n)
    (ρ : Representation ℂ G V) {t s : G} {k : ℕ}
    (ht : t ^ (p ^ k) = 1) (hcomm : Commute t s) :
    (⟨ρ.character (t * s), character_value_isIntegral ρ (t * s)⟩ : integralClosure ℤ ℂ) -
      ⟨ρ.character s, character_value_isIntegral ρ s⟩ ∈ P := by
  classical
  let f : Module.End ℂ V := ρ t
  let T : Module.End ℂ V := ρ s
  have hf : f ^ (p ^ k) = 1 := by rw [← map_pow, ht, map_one]
  have hT : T ^ orderOf s = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hcomm' : f * T = T * f := (hcomm.map ρ).eq
  let z : f.Eigenvalues → integralClosure ℤ ℂ := fun μ =>
    ⟨(μ : ℂ), eigen_value_isIntegral_of_pow_eq_one (pow_pos hp.pos k) hf μ.property⟩
  let b : f.Eigenvalues → integralClosure ℤ ℂ := fun μ =>
    ⟨LinearMap.trace ℂ (f.eigenspace (μ : ℂ))
      (T.restrict (eigenspace_mapsTo_of_commute hcomm' μ)),
      trace_isIntegral_of_forall_eigenvalue _ (fun w hw =>
        eigen_value_isIntegral_of_pow_eq_one (orderOf_pos s)
          (restrict_pow_eq_one _ hT) hw)⟩
  have hz (μ : f.Eigenvalues) : z μ - 1 ∈ P := by
    apply prime_power_root_sub_one_mem P hP hp hchar (z μ) (k := k)
    apply Subtype.ext
    exact eigenvalue_pow_eq_one_of_pow_eq_one hf μ.property
  have heq : (⟨ρ.character (t * s), character_value_isIntegral ρ (t * s)⟩ : integralClosure ℤ ℂ) -
      ⟨ρ.character s, character_value_isIntegral ρ s⟩ =
        ∑ μ : f.Eigenvalues, (z μ - 1) * b μ := by
    apply Subtype.ext
    have hsum : (↑(∑ μ : f.Eigenvalues, (z μ - 1) * b μ) : ℂ) =
        ∑ μ : f.Eigenvalues, (((z μ - 1) * b μ : integralClosure ℤ ℂ) : ℂ) :=
      map_sum (integralClosure ℤ ℂ).val _ _
    rw [hsum]
    change LinearMap.trace ℂ V (ρ (t * s)) - LinearMap.trace ℂ V T =
      ∑ μ : f.Eigenvalues, ((μ : ℂ) - 1) *
        LinearMap.trace ℂ (f.eigenspace (μ : ℂ))
          (T.restrict (eigenspace_mapsTo_of_commute hcomm' μ))
    rw [map_mul, trace_mul_eq_sum_eigen_mul_trace_restrict
      (pow_ne_zero k hp.ne_zero) hf hcomm',
      trace_eq_sum_trace_restrict_eigenspaces_of_commute
        (pow_ne_zero k hp.ne_zero) hf hcomm']
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib]
  rw [heq]
  exact P.sum_mem fun μ _ => P.mul_mem_right _ (hz μ)

/-- The prime-part congruence extends to the entire ring generated by ordinary characters. -/
theorem characterEvaluation_prime_part_sub_mem
    {G : Type*} [Group G] [Fintype G]
    (P : Ideal (integralClosure ℤ ℂ)) (hP : P.IsMaximal) {p : ℕ} (hp : p.Prime)
    (hchar : ∀ n : ℕ, (n : integralClosure ℤ ℂ) ∈ P ↔ p ∣ n)
    {t s : G} {k : ℕ} (ht : t ^ (p ^ k) = 1) (hcomm : Commute t s)
    (f : characterRing G) : characterEvaluation (t * s) f - characterEvaluation s f ∈ P := by
  let E (g : G) := (Ideal.Quotient.mk P).comp (characterEvaluation g)
  suffices heq : E (t * s) f = E s f by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub]
    exact sub_eq_zero.mpr heq
  obtain ⟨f, hf⟩ := f
  induction hf using Subring.closure_induction with
  | mem f hf =>
    obtain ⟨n, ρ, rfl⟩ := hf
    apply sub_eq_zero.mp
    change Ideal.Quotient.mk P (characterEvaluation (t * s) _) -
      Ideal.Quotient.mk P (characterEvaluation s _) = 0
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (representation_character_prime_part_sub_mem P hP hp hchar ρ ht hcomm)
  | zero => change E (t * s) 0 = E s 0; simp only [map_zero]
  | one => change E (t * s) 1 = E s 1; simp only [map_one]
  | add f h hf hh ihf ihh =>
    change E (t * s) (⟨f, hf⟩ + ⟨h, hh⟩) = E s (⟨f, hf⟩ + ⟨h, hh⟩)
    simp only [map_add, ihf, ihh]
  | neg f hf ih =>
    change E (t * s) (-⟨f, hf⟩) = E s (-⟨f, hf⟩)
    simp only [map_neg, ih]
  | mul f h hf hh ihf ihh =>
    change E (t * s) (⟨f, hf⟩ * ⟨h, hh⟩) = E s (⟨f, hf⟩ * ⟨h, hh⟩)
    simp only [map_mul, ihf, ihh]

/-- It suffices to establish local nonvanishing at prime-regular elements. -/
theorem local_nonvanishing_of_prime_regular
    {G : Type*} [Group G] [Fintype G]
    (hregular : ∀ (p : ℕ), p.Prime → ∀ (P : Ideal (integralClosure ℤ ℂ)), P.IsMaximal →
      (∀ n : ℕ, (n : integralClosure ℤ ℂ) ∈ P ↔ p ∣ n) → ∀ s : G, ¬ p ∣ orderOf s →
      ∃ f : characterRing G, f.val ∈ nilpotentInducedSpan G ∧ characterEvaluation s f ∉ P)
    (g : G) (P : Ideal (integralClosure ℤ ℂ)) (hP : P.IsMaximal) :
    ∃ f : characterRing G, f.val ∈ nilpotentInducedSpan G ∧ characterEvaluation g f ∉ P := by
  obtain ⟨p, hp, hchar⟩ := exists_residue_prime P hP
  obtain ⟨t, s, ⟨k, ht⟩, hs, hcomm, rfl⟩ := exists_commuting_prime_parts p hp g
  obtain ⟨f, hf, hnot⟩ := hregular p hp P hP hchar s hs
  refine ⟨f, hf, fun hmem => hnot ?_⟩
  have hdiff := characterEvaluation_prime_part_sub_mem P hP hp hchar ht hcomm f
  simpa only [sub_sub_cancel] using P.sub_mem hmem hdiff

/-- An integral weighted sum outside an ideal detects a nilpotent-induced character
outside that ideal. -/
theorem local_nonvanishing_of_induced_sum
    {G : Type*} [Group G] [Fintype G]
    (s : G) (P : Ideal (integralClosure ℤ ℂ)) (H : Subgroup G) (hH : Group.IsNilpotent H)
    (n m : ℕ) (φ : Fin n → ClassFunction H) (hφ : ∀ i, IsCharacter (φ i))
    (a : Fin n → ℂ) (ha : ∀ i, IsIntegral ℤ (a i))
    (hsum : (∑ i, a i * inducedClassFunction H (φ i) s) = (m : ℂ))
    (hm : (m : integralClosure ℤ ℂ) ∉ P) :
    ∃ f : characterRing G, f.val ∈ nilpotentInducedSpan G ∧ characterEvaluation s f ∉ P := by
  classical
  let f : Fin n → characterRing G := fun i =>
    ⟨inducedClassFunction H (φ i),
      character_mem_characterRing (inducedClassFunction_isCharacter H (hφ i))⟩
  have hf (i : Fin n) : (f i).val ∈ nilpotentInducedSpan G :=
    nilpotentInduced_mem H hH (hφ i)
  by_contra! h
  apply hm
  have heq : (∑ i, (⟨a i, ha i⟩ : integralClosure ℤ ℂ) * characterEvaluation s (f i)) =
      (m : integralClosure ℤ ℂ) := by
    apply Subtype.ext
    calc
      (↑(∑ i, (⟨a i, ha i⟩ : integralClosure ℤ ℂ) * characterEvaluation s (f i)) : ℂ) =
          ∑ i, (↑((⟨a i, ha i⟩ : integralClosure ℤ ℂ) * characterEvaluation s (f i)) : ℂ) :=
        map_sum (integralClosure ℤ ℂ).val _ _
      _ = (m : ℂ) := hsum
      _ = ↑(m : integralClosure ℤ ℂ) := by norm_cast
  rw [← heq]
  exact P.sum_mem fun i _ => P.mul_mem_left _ (h (f i) (hf i))

/-- At every group element and modulo every maximal ideal of the algebraic
integers, some element of the nilpotent-induced character span has nonzero value. -/
theorem local_nonvanishing
    {G : Type*} [Group G] [Fintype G]
    (g : G) (P : Ideal (integralClosure ℤ ℂ)) (hP : P.IsMaximal) :
    ∃ f : characterRing G,
      f.val ∈ nilpotentInducedSpan G ∧ characterEvaluation g f ∉ P := by
  apply local_nonvanishing_of_prime_regular _ g P hP
  intro p hp P hP hchar s hs
  obtain ⟨H, r, hH, hHC, hsH, hret, hi⟩ :=
    Subgroup.exists_nilpotent_centralizer_retraction p hp s hs
  obtain ⟨n, φ, a, hφ, ha, hsum⟩ :=
    cyclicInductionFourier p hp s hs H hHC hsH r hret
  apply local_nonvanishing_of_induced_sum s P H hH n _ φ hφ a ha hsum
  intro hmem
  exact (hp.not_dvd_mul hs hi) ((hchar _).mp hmem)

end BrauerInduction
