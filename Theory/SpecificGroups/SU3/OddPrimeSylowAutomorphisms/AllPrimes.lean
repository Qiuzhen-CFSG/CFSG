module

public import Theory.SpecificGroups.SU3.OddInvolutionFixed
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.OrthogonalOrder
public import BenderSuzuki.External.Huppert.II.theorem_10_12
public import Mathlib.Algebra.Order.Ring.Abs

/-!
# Odd-prime Sylow fixers in PSU₃

Normalize an outer involution to entrywise conjugation. Its full fixed group
is the ternary special orthogonal group of order p(p² − 1). The unitary
order formula implies that its index, multiplied by gcd(3,p+1), is
p²(p³+1), which is even. Since that gcd is odd, the fixed group cannot
contain a Sylow two-subgroup. The normalization and order computations use
actual projective equivalences and retain the original coefficient field
and Hermitian conjugation. No congruence condition modulo eight is needed.

Source: Aschbacher--Smith, proof of 1.1.5(3), printed p.503;
Huppert II.10.12; GLS3, §§2.5, 2.7 and 4.3.
-/

open Matrix Subgroup
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

/-- An automorphism squaring to one and fixing a Sylow two-subgroup pointwise
is inner, for every odd prime and every nondegenerate ternary Hermitian form. -/
public theorem inner_of_involutive_fixing_sylow [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card E = p ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = p)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha : a ^ 2 = 1) (hfix : ∀ x ∈ P, a x = x) :
    ∃ k, a = MulAut.conj k := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  by_contra houter
  obtain ⟨J₀, e, hc, hJ₀, hgraph⟩ :=
    OddInvolutionNormalization.normalized_outer J hp ho hcard hfixed a ha houter
  have hf : Nat.card {x : E // J₀.conj x = x} = p := by rwa [hc]
  obtain ⟨_, _, _, _, _, _, _, _, horder, _⟩ :=
    BenderSuzuki.External.huppert_II_10_12 J₀ p hcard hf hJ₀
  have hG : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) =
      (p ^ 3 + 1) * p ^ 3 * (p ^ 2 - 1) / Nat.gcd 3 (p + 1) :=
    (Nat.card_congr e.toEquiv).trans horder
  let F := FixedBy.subfield E J₀.conj
  have hF : Nat.card F = p := hf
  have h2 : (2 : F) ≠ 0 := by
    let : Fintype F := Fintype.ofFinite F
    apply Ring.two_ne_zero
    intro he
    have hh := FiniteField.even_card_of_char_two he
    rw [← Nat.card_eq_fintype_card, hF] at hh
    have hh' := Nat.odd_iff.mp ho
    omega
  have hC : Nat.card a.fixedSubgroup = p * (p ^ 2 - 1) := by
    rw [Nat.card_congr (MulAut.fixedSubgroupCongr e a).toEquiv,
      Nat.card_congr (projectiveFixedEquivOrthogonal J₀ hJ₀ hgraph).toEquiv,
      card_splitOrthogonal_specialSubgroup h2, hF]
  have hPC : (P : Subgroup _) ≤ a.fixedSubgroup := by
    intro x hx
    exact (MulAut.mem_fixedSubgroup _ _).mpr (hfix x hx)
  have hi : Odd a.fixedSubgroup.index := by
    apply Nat.odd_iff.mpr
    have hn : ¬ 2 ∣ a.fixedSubgroup.index :=
      fun hd => P.not_dvd_index (hd.trans (index_dvd_of_le hPC))
    omega
  have hd : Nat.gcd 3 (p + 1) ∣ (p ^ 3 + 1) * p ^ 3 * (p ^ 2 - 1) := by
    have hd' : p + 1 ∣ p ^ 3 + 1 := by
      simpa using (show Odd 3 from by decide).nat_add_dvd_pow_add_pow p 1
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
      ((Nat.gcd_dvd_right 3 (p + 1)).trans hd') _) _
  have hmul := a.fixedSubgroup.card_mul_index
  rw [hC, hG] at hmul
  have he : p * (p ^ 2 - 1) *
      (a.fixedSubgroup.index * Nat.gcd 3 (p + 1)) =
      p * (p ^ 2 - 1) * (p ^ 2 * (p ^ 3 + 1)) := by
    calc
      _ = (p * (p ^ 2 - 1) * a.fixedSubgroup.index) * Nat.gcd 3 (p + 1) := by ring
      _ = (p ^ 3 + 1) * p ^ 3 * (p ^ 2 - 1) := by rw [hmul, Nat.div_mul_cancel hd]
      _ = _ := by ring
  have hp2 : 1 < p ^ 2 := by nlinarith [hp.two_le]
  have hcancel := Nat.eq_of_mul_eq_mul_left
    (mul_pos hp.pos (Nat.sub_pos_of_lt hp2)) he
  have hiOdd := hi.mul ((show Odd 3 from by decide).of_dvd_nat (Nat.gcd_dvd_left 3 (p + 1)))
  rw [hcancel] at hiOdd
  have heven : Even (p ^ 2 * (p ^ 3 + 1)) :=
    (Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr (ho.pow : Odd (p ^ 3)))).mul_left _
  exact (Nat.not_even_iff_odd.mpr hiOdd) heven

end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow
