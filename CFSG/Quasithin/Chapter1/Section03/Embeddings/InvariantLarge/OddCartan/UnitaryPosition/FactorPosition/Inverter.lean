module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.UnitaryPosition.SL2Subgroups
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.Sign

/-!
# The square of the source SL₂ inverter

A nontrivial odd-order element of SL₂ inverted by t forces t to have trace
zero. Cayley--Hamilton, here calculated in two-by-two coordinates, then gives
t² = -1. Thus the inverter supplied by A.3.15 has order four and its square
is the central involution of the supplied SL₂. The embedded-residual theorem
identifies that SL₂ with the residual at this very square.

This places the base involution in S and C(B), retaining the inverter in
N_S(B). It does not yet place the involution in Z(S).

Source: Aschbacher--Smith, A.3.15(3), printed pp.50--51, and the proof of
1.3.4, printed pp.510--511 of refs/quasithin.pdf.
-/

public section

open Matrix Subgroup
open scoped MatrixGroups

private theorem inverter_sq_neg_one {F : Type*} [Field F]
    (t b : SL(2, F)) (hb : b ≠ b⁻¹) (hi : t * b * t⁻¹ = b⁻¹) :
    t ^ 2 = -1 := by
  have hm : t * b = b⁻¹ * t := (mul_inv_eq_iff_eq_mul).mp hi
  have hmM := congrArg (fun a : SL(2, F) => (a : Matrix (Fin 2) (Fin 2) F)) hm
  change (t : Matrix (Fin 2) (Fin 2) F) * b = Matrix.adjugate (b : Matrix (Fin 2) (Fin 2) F) * t at hmM
  rw [Matrix.adjugate_fin_two] at hmM
  have he (i j : Fin 2) := congrArg (fun a : Matrix (Fin 2) (Fin 2) F => a i j) hmM
  have h00 := he 0 0
  have h01 := he 0 1
  have h10 := he 1 0
  have h11 := he 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  have ht : t 0 0 + t 1 1 = 0 := by
    by_contra hn
    have hb01 : b 0 1 = 0 := by
      apply (mul_eq_zero.mp (show (t 0 0 + t 1 1) * b 0 1 = 0 by linear_combination h01)).resolve_left hn
    have hb10 : b 1 0 = 0 := by
      apply (mul_eq_zero.mp (show (t 0 0 + t 1 1) * b 1 0 = 0 by linear_combination h10)).resolve_left hn
    have hbd : b 0 0 = b 1 1 := by
      apply sub_eq_zero.mp
      apply (mul_eq_zero.mp (show (t 0 0 + t 1 1) * (b 0 0 - b 1 1) = 0 by
        linear_combination h00 - h11)).resolve_left hn
    apply hb
    rw [SpecialLinearGroup.SL2_inv_expl]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb01, hb10, hbd]
  have hd := t.property
  rw [Matrix.det_fin_two] at hd
  apply Subtype.ext
  change (t : Matrix (Fin 2) (Fin 2) F) ^ 2 = -1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination t 0 0 * ht - hd
  · linear_combination t 0 1 * ht
  · linear_combination t 1 0 * ht
  · linear_combination t 1 1 * ht - hd

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition
variable {J : Type*} [Group J] [Finite J]

omit [Finite J] in
private theorem left_prime_dvd {B K : Subgroup J} {p : ℕ} [Fact p.Prime]
    (hB : IsPGroup p B) (hC : CyclicDecomposition B K) (hn : ¬ IsCyclic B) :
    p ∣ Nat.card (B ⊓ K : Subgroup J) := by
  have hp : IsPGroup p (B ⊓ K : Subgroup J) :=
    hB.of_injective (inclusion inf_le_left) (inclusion_injective inf_le_left)
  rcases hp.card_eq_or_dvd with he | he
  · exact (hC.left_ne_bot hn (Subgroup.card_eq_one.mp he)).elim
  · exact he

omit [Finite J] in
theorem caseThree_prime_ne_characteristic
    {κ : GroupClass} {D B K : Subgroup J} {S : Sylow 2 J} {p q : ℕ}
    [Fact q.Prime] (hA : AmbientInput κ D B S p)
    (hC : CaseThree D B (S : Subgroup J) K q .unitary .unitary)
    (hn : ¬ IsCyclic B) : p ≠ q := by
  let : Fact p.Prime := ⟨hA.prime⟩
  have hd : p ∣ q + 1 := (left_prime_dvd hA.p_group hC.toCyclicDecomposition hn).trans hC.sl2_dvd
  intro he
  rw [← he] at hd
  have hp1 : p ∣ 1 := (Nat.dvd_add_iff_left (dvd_refl p)).mpr (by simpa only [Nat.add_comm] using hd)
  have := Nat.le_of_dvd (by decide : 0 < 1) hp1
  have := hA.large
  omega

theorem caseThree_inverter_square
    {κ : GroupClass} {D B K : Subgroup J} {S : Sylow 2 J} {p q : ℕ}
    [Fact q.Prime] (hA : AmbientInput κ D B S p)
    (hC : CaseThree D B (S : Subgroup J) K q .unitary .unitary)
    (hn : ¬ IsCyclic B) (hlarge : 3 < q)
    {t : J} (ht : t ∈ K)
    (hi : ∀ b ∈ B ⊓ K, t * b * t⁻¹ = b⁻¹) :
    orderOf t = 4 ∧ t ^ 2 ∈ centerImage K ∧ orderOf (t ^ 2) = 2 ∧
      t ∉ centralizer (B : Set J) := by
  let : Fact p.Prime := ⟨hA.prime⟩
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := (B ⊓ K : Subgroup J)) p
    (left_prime_dvd hA.p_group hC.toCyclicDecomposition hn)
  have hbp : orderOf (b : J) = p := by simpa only [orderOf_coe] using hb
  have hbne : (b : J) ≠ (b : J)⁻¹ := by
    intro he
    have hb2 : (b : J) ^ 2 = 1 := by rw [pow_two]; exact (eq_inv_iff_mul_eq_one.mp he)
    have hd : p ∣ 2 := hbp ▸ orderOf_dvd_of_pow_eq_one hb2
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    have := hA.large
    omega
  let tk : K := ⟨t, ht⟩
  let bk : K := ⟨b, b.property.2⟩
  obtain ⟨e⟩ := hC.sl2
  have hei : e tk * e bk * (e tk)⁻¹ = (e bk)⁻¹ := by
    simpa only [map_mul, map_inv] using congrArg e
      (show tk * bk * tk⁻¹ = bk⁻¹ from Subtype.ext (hi b b.property))
  have heb : e bk ≠ (e bk)⁻¹ := by
    intro he
    apply hbne
    exact congrArg (fun a : K => (a : J)) (e.injective (he.trans (map_inv e bk).symm))
  have hsq := inverter_sq_neg_one (e tk) (e bk) heb hei
  have hnegne : (-1 : SL(2, ZMod q)) ≠ 1 := by
    intro he
    let : Fact (2 < q) := ⟨by omega⟩
    have hh := congrArg (fun a : SL(2, ZMod q) => a 0 0) he
    exact CharP.neg_one_ne_one (ZMod q) q (by simpa using hh)
  have hnegord : orderOf (-1 : SL(2, ZMod q)) = 2 :=
    orderOf_eq_prime (by simp [pow_two]) hnegne
  have hzc : tk ^ 2 ∈ center K := by
    apply mem_center_iff.mpr
    intro k
    apply e.injective
    simp only [map_mul, map_pow, hsq]
    simp
  have hz : orderOf (t ^ 2) = 2 := by
    calc
      orderOf (t ^ 2) = orderOf (tk ^ 2) := orderOf_coe (tk ^ 2)
      _ = orderOf (e (tk ^ 2)) := (e.orderOf_eq _).symm
      _ = 2 := by rw [map_pow, hsq, hnegord]
  refine ⟨?_, ⟨tk ^ 2, hzc, rfl⟩, hz, ?_⟩
  · apply orderOf_eq_prime_pow (p := 2) (n := 1)
    · simpa only [pow_one] using (show t ^ 2 ≠ 1 by intro he; simp [he] at hz)
    · change t ^ 4 = 1
      have hh := pow_orderOf_eq_one (t ^ 2)
      simpa only [hz, ← pow_mul] using hh
  · intro hc
    apply hbne
    calc
      (b : J) = t * b * t⁻¹ := by rw [← hc b b.property.1, mul_inv_cancel_right]
      _ = (b : J)⁻¹ := hi b b.property

/-- The source inverter bases the supplied residual at its square, in S and C(B). -/
theorem caseThree_inverter_residual
    {κ : GroupClass} {D B K : Subgroup J} {S : Sylow 2 J} {p q : ℕ}
    [Fact q.Prime] (hA : AmbientInput κ D B S p)
    (hC : CaseThree D B (S : Subgroup J) K q .unitary .unitary)
    (hn : ¬ IsCyclic B) (hlarge : 3 < q) :
    ∃ t ∈ (S : Subgroup J) ⊓ normalizer B,
      t ∈ K ∧ orderOf t = 4 ∧ t ∉ centralizer (B : Set J) ∧
      ∃ z : D, (z : J) = t ^ 2 ∧ orderOf z = 2 ∧
        (z : J) ∈ (S : Subgroup J) ∧ (z : J) ∈ centralizer (B : Set J) ∧
        K = involutionResidual D z := by
  obtain ⟨t, ht, htK, hi⟩ := hC.exists_normalizing_inverter
  obtain ⟨ht4, htc, ht2, htnc⟩ := caseThree_inverter_square hA hC hn hlarge htK hi
  obtain ⟨w, hw, hwv⟩ := htc
  change (w : J) = t ^ 2 at hwv
  let z : D := ⟨w, hC.sl2_inside w.property⟩
  have hw2 : orderOf w = 2 := by rw [← orderOf_coe w, hwv]; exact ht2
  have hz2 : orderOf z = 2 := by
    rw [← orderOf_coe z]
    change orderOf (w : J) = 2
    rw [hwv]
    exact ht2
  obtain ⟨e⟩ := hC.sl2
  refine ⟨t, ht, htK, ht4, htnc, z, hwv, hz2, ?_, ?_, ?_⟩
  · change (w : J) ∈ (S : Subgroup J)
    rw [hwv]
    exact (S : Subgroup J).pow_mem ht.1 2
  · exact le_centralizer_iff.mp
      (cyclicDecomposition_le_centralizer_centerImage hC.toCyclicDecomposition) ⟨w, hw, rfl⟩
  · exact sl2_eq_involutionResidual D K hC.sl2_inside q hC.odd_characteristic hlarge
      hC.model e w hw hw2

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition
