module
public import Theory.SpecificGroups.GL2.QuadraticSemidihedralGenerators
public import Theory.GroupTheory.SemidihedralCenter
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Explicit semidihedral Sylow subgroups of the full general linear group

For a finite field F with |F| congruent to three modulo four, the full
GL2(F) has a Sylow two-subgroup with explicit semidihedral generators.
The conclusion retains their orders, conjugation relation, generation,
the actual center, and the scalar half-power identity. No abstract
semidihedral predicate or chosen characteristic parameter is required.

Write |F|+1 = 2^k*u with u odd. Then k≥2 and |F|-1 = 2*r with r odd.
The quadratic torus supplies a rotation of order 2^(k+1) and an external
normalizing Frobenius involution. Their join has order 2^(k+2), whereas
the full general linear group has order 2^(k+2)*(|F|*r²*u), by Mathlib's
matrix cardinality formula. The join thus has odd index and is Sylow.
Restrict the same generators to this subgroup and apply the explicit
semidihedral center calculation; the rotation's half-power remains −I.
The final order parameter is k+2, including height four when |F|=3.

This assembles the quadratic construction of Alperin–Brauer–Gorenstein
II.2 Lemma 1 (article p17), with full-group Sylow maximality, for the
GL2 centralizer model in Brauer II, pp125–126. The determinant-sign
subgroup wrappers remain separate and unchanged.
-/

namespace Matrix.GeneralLinearGroup

private theorem full_card_two_part (F : Type*) [Field F] [Finite F]
    (n : ℕ) (hn : 2 ≤ n) (hd : 2 ^ n ∣ Nat.card F + 1)
    (ho : Odd ((Nat.card F + 1) / 2 ^ n)) :
    ∃ r, Odd r ∧ Nat.card (GL (Fin 2) F) = 2 ^ (n + 2) * r := by
  let : Fintype F := Fintype.ofFinite F
  let q := Nat.card F
  obtain ⟨hqodd, _, _⟩ := quadratic_two_part_arithmetic q n hn hd ho
  have h4 : 4 ∣ q + 1 := (show 4 ∣ 2 ^ n by simpa using Nat.pow_dvd_pow 2 hn).trans hd
  obtain ⟨r, hr⟩ := hqodd
  have hro : Odd r := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    omega
  let k := (q + 1) / 2 ^ n
  have hk : q + 1 = 2 ^ n * k := (Nat.mul_div_cancel' hd).symm
  have hqo : Odd q := ⟨r, hr⟩
  refine ⟨q * r ^ 2 * k, (hqo.mul hro.pow).mul ho, ?_⟩
  have hs : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have hsq : q ^ 2 = (q - 1) * (q + 1) + 1 := by
      rw [hr]; simp only [Nat.add_sub_cancel]; ring
    omega
  have ht : q ^ 2 - q = q * (q - 1) := by
    rw [pow_two, Nat.mul_sub_left_distrib, mul_one]
  rw [Matrix.card_GL_field]
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  simp only [← Nat.card_eq_fintype_card]
  change (q ^ 2 - 1) * (q ^ 2 - q) = _
  rw [hs, ht, show q - 1 = 2 * r by omega, hk, pow_add]
  ring

public theorem exists_semidihedral_sylow (F : Type*) [Field F] [Finite F]
    (hF : Nat.card F % 4 = 3) :
    ∃ (P : Sylow 2 (GL (Fin 2) F)) (n : ℕ), 4 ≤ n ∧ Nat.card P = 2 ^ n ∧
      ∃ a b : P, orderOf a = 2 ^ (n - 1) ∧ orderOf b = 2 ∧
        b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1) ∧
        Subgroup.closure ({a, b} : Set P) = ⊤ ∧
        Subgroup.center P = Subgroup.zpowers (a ^ (2 ^ (n - 2))) ∧
        (a : GL (Fin 2) F) ^ (2 ^ (n - 2)) = scalar (Fin 2) (-1 : Fˣ) := by
  obtain ⟨n, k, hk, he⟩ := Nat.exists_eq_two_pow_mul_odd
    (show Nat.card F + 1 ≠ 0 by omega)
  have hn : 2 ≤ n := by
    by_contra h
    have hn' : n = 0 ∨ n = 1 := by omega
    obtain ⟨j, hj⟩ := hk
    rcases hn' with rfl | rfl <;> simp only [pow_zero, pow_one, one_mul] at he <;> omega
  have hd : 2 ^ n ∣ Nat.card F + 1 := ⟨k, he⟩
  have ho : Odd ((Nat.card F + 1) / 2 ^ n) := by
    rw [he, Nat.mul_div_cancel_left _ (by positivity)]
    exact hk
  let : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  obtain ⟨a, w, ha, hw, hout, hconj, hscalar⟩ :=
    finite_quadratic_semidihedral_generators F (ringChar F) n hn hd ho
  let T := Subgroup.zpowers a ⊔ Subgroup.zpowers w
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hw)
  have hforward : ∀ x ∈ Subgroup.zpowers a, w * x * w⁻¹ ∈ Subgroup.zpowers a := by
    intro x hx
    have hm : (Subgroup.zpowers a).map (MulAut.conj w).toMonoidHom ≤ Subgroup.zpowers a := by
      rw [MonoidHom.map_zpowers]
      apply Subgroup.zpowers_le.mpr
      change w * a * w⁻¹ ∈ Subgroup.zpowers a
      rw [hconj]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers a) _
    exact hm (Subgroup.mem_map_of_mem _ hx)
  have hnorm : w ∈ Subgroup.normalizer (Subgroup.zpowers a : Set (GL (Fin 2) F)) := by
    apply Subgroup.mem_normalizer_iff.mpr
    intro x
    refine ⟨hforward x, fun hx => ?_⟩
    have h := hforward _ hx
    have he : w * (w * x * w⁻¹) * w⁻¹ = x := by
      rw [hwi]
      calc
        w * (w * x * w) * w = (w * w) * x * (w * w) := by group
        _ = x := by rw [← pow_two, hw]; simp
    rwa [he] at h
  have hcard : Nat.card T = 2 ^ (n + 2) := by
    rw [Subgroup.card_sup_zpowers_of_normalizing_involution _ _ hw hout hnorm,
      Nat.card_zpowers, ha]
    simp only [show n + 2 = (n + 1) + 1 by omega, pow_succ, Nat.mul_comm]
  have hT2 : IsPGroup 2 T := IsPGroup.of_card hcard
  obtain ⟨r, hr, hGLcard⟩ := full_card_two_part F n hn hd ho
  have hindex : T.index = r := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0 < 2) (n + 2))
    calc
      2 ^ (n + 2) * T.index = Nat.card T * T.index := by rw [hcard]
      _ = Nat.card (GL (Fin 2) F) := T.card_mul_index
      _ = 2 ^ (n + 2) * r := hGLcard
  have hnot : ¬2 ∣ T.index := by
    rw [hindex]
    exact Nat.not_even_iff_odd.mpr hr |>.comp (even_iff_two_dvd.mpr)
  let P := hT2.toSylow hnot
  let aT : T := ⟨a, (show Subgroup.zpowers a ≤ T from le_sup_left) (Subgroup.mem_zpowers a)⟩
  let wT : T := ⟨w, (show Subgroup.zpowers w ≤ T from le_sup_right) (Subgroup.mem_zpowers w)⟩
  have haT : orderOf aT = 2 ^ ((n + 2) - 1) := by
    rw [← orderOf_injective T.subtype T.subtype_injective]
    simpa [aT] using ha
  have hwT : orderOf wT = 2 := by
    apply orderOf_eq_prime
    · exact Subtype.ext hw
    · intro he
      have he' : w = 1 := congrArg Subtype.val he
      exact hout (he'.symm ▸ (Subgroup.one_mem (Subgroup.zpowers a)))
  have hcT : wT * aT * wT⁻¹ = aT ^ (2 ^ ((n + 2) - 2) - 1) := by
    apply Subtype.ext
    simpa [aT, wT] using hconj
  have hgen : Subgroup.closure ({aT, wT} : Set T) = ⊤ := by
    apply (Subgroup.map_injective T.subtype_injective)
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, T.range_subtype,
      Set.image_insert_eq, Set.image_singleton]
    change Subgroup.closure ({a, w} : Set (GL (Fin 2) F)) = T
    simp only [T, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
      Set.singleton_union]
  exact ⟨P, n + 2, by omega, hcard, aT, wT, haT, hwT, hcT, hgen,
    Semidihedral.center_eq (by omega) aT wT haT hwT hcT hgen, hscalar⟩

end Matrix.GeneralLinearGroup
