module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.LinearPosition.SL2Subgroups
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.Sign
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# The source inverter and the unique SL₂ involution

An SL₂ over an odd prime field has a unique involution. The source inverter
normalizes B and does not centralize it when both odd cyclic factors are
nontrivial. Its nontrivial two-part therefore puts the central SL₂ involution
in S. Moreover its square is nonidentity: an involutory inverter would be
central in SL₂ and hence would centralize B.

These facts will identify a central power of the inverter with the base
involution of the supplied residual. They do not assume that K is invariant.

Source: Aschbacher–Smith, A.3.15(3), printed pp.50–51, and the proof of
1.3.4, printed pp.510–511. Recovered from the saved linear factor-position
attempt, with its finite-field and projective conventions unchanged.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan

private theorem sl2_involution_central {F : Type*} [Field F]
    (h2 : (2 : F) ≠ 0) (x : SL(2, F)) (hx : orderOf x = 2) : x ∈ center SL(2, F) := by
  have hi : x = x⁻¹ := eq_inv_iff_mul_eq_one.mpr (by
    simpa only [hx, pow_two] using pow_orderOf_eq_one x)
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl] at hi
  have hd : x 0 0 = x 1 1 := congrArg (fun a : SL(2, F) => a 0 0) hi
  have hb : x 0 1 = -x 0 1 := congrArg (fun a : SL(2, F) => a 0 1) hi
  have hc : x 1 0 = -x 1 0 := congrArg (fun a : SL(2, F) => a 1 0) hi
  have hb0 : x 0 1 = 0 := (mul_eq_zero.mp (show (2 : F) * x 0 1 = 0 by
    linear_combination hb)).resolve_left h2
  have hc0 : x 1 0 = 0 := (mul_eq_zero.mp (show (2 : F) * x 1 0 = 0 by
    linear_combination hc)).resolve_left h2
  apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨x 0 0, ?_, ?_⟩
  · simpa only [Fintype.card_fin, pow_two, Matrix.det_fin_two, ← hd, hb0, hc0,
      zero_mul, sub_zero] using x.property
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.scalar_apply, hd, hb0, hc0]

/-- The actual SL₂ over an odd prime field has only one involution. -/
theorem sl2_involutions_equal (q : ℕ) [Fact q.Prime] (hq : Odd q)
    (x y : SL(2, ZMod q)) (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  have h2 : (2 : ZMod q) ≠ 0 := by
    apply CharP.cast_ne_zero_of_ne_of_prime (ZMod q) Nat.prime_two
    obtain ⟨k, hk⟩ := hq
    omega
  have hc : Nat.card (center SL(2, ZMod q)) = 2 := by
    rw [← GorensteinWalter.sl2ProjectiveProjection_ker]
    exact GorensteinWalter.sl2ProjectiveProjection_ker_card (ZMod q) (by simpa using hq)
  let : IsCyclic (center SL(2, ZMod q)) := isCyclic_of_prime_card hc
  exact congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
    (x := ⟨x, sl2_involution_central h2 x hx⟩)
    (y := ⟨y, sl2_involution_central h2 y hy⟩)
    (by simpa only [← Subgroup.orderOf_coe] using hx)
    (by simpa only [← Subgroup.orderOf_coe] using hy))

variable {J : Type*} [Group J] [Finite J]

omit [Finite J] in
/-- A nontrivial odd factor cannot be both centralized and inverted. -/
theorem CyclicDecomposition.inverter_not_centralizing
    {B K : Subgroup J} {p : ℕ} (h : CyclicDecomposition B K)
    (hB : IsPGroup p B) (hp : Odd p) (hn : ¬ IsCyclic B)
    {t : J} (hi : ∀ b ∈ B ⊓ K, t * b * t⁻¹ = b⁻¹) :
    t ∉ centralizer (B : Set J) := by
  obtain ⟨b, hb, hb1⟩ := (B ⊓ K).bot_or_exists_ne_one.resolve_left (h.left_ne_bot hn)
  intro ht
  have hbi : b = b⁻¹ := by
    have he : t * b = b * t := (ht b hb.1).symm
    simpa only [he, mul_inv_cancel_right] using hi b hb
  let bB : B := ⟨b, hb.1⟩
  have hb2 : orderOf bB ∣ 2 := orderOf_dvd_of_pow_eq_one (by
    apply Subtype.ext
    change b ^ 2 = 1
    rw [pow_two]
    exact eq_inv_iff_mul_eq_one.mp hbi)
  have ho : orderOf bB = 1 := Nat.eq_one_of_dvd_coprimes
    (hB.orderOf_coprime (Nat.coprime_two_right.mpr hp) bB) (dvd_refl _) hb2
  exact hb1 (congrArg Subtype.val (orderOf_eq_one_iff.mp ho))

/-- The central involution of the supplied SL₂ already lies in S.
The source inverter supplies a nonidentity two-element of K. -/
theorem CaseThree.sl2_central_involution_mem_sylow
    {D B K : Subgroup J} {S : Sylow 2 J} {p q : ℕ} [Fact q.Prime] {δ ε : Sign}
    (h : CaseThree D B (S : Subgroup J) K q δ ε)
    (hB : IsPGroup p B) (hp : Odd p) (hn : ¬ IsCyclic B)
    (z : K) (hz : orderOf z = 2) : (z : J) ∈ S := by
  obtain ⟨t, ht, htK, hi⟩ := h.exists_normalizing_inverter
  have ht1 : t ≠ 1 := by
    intro he
    exact h.toCyclicDecomposition.inverter_not_centralizing hB hp hn hi
      (he ▸ (centralizer (B : Set J)).one_mem)
  let tS : S := ⟨t, ht.1⟩
  let n := orderOf tS / 2
  have ho : orderOf (tS ^ n) = 2 := orderOf_pow_orderOf_div (orderOf_pos tS).ne'
    (S.isPGroup'.dvd_orderOf (fun he => ht1 (congrArg Subtype.val he)))
  let w : K := ⟨t ^ n, K.pow_mem htK n⟩
  have hw : orderOf w = 2 := (Subgroup.orderOf_coe w).symm.trans
    ((Subgroup.orderOf_coe (tS ^ n)).trans ho)
  obtain ⟨e⟩ := h.sl2
  have hzw : z = w := e.injective (sl2_involutions_equal q h.odd_characteristic
    (e z) (e w) ((e.orderOf_eq z).trans hz) ((e.orderOf_eq w).trans hw))
  rw [hzw]
  exact S.pow_mem ht.1 n

/-- A noncentralizing source inverter has nonidentity square. -/
theorem CaseThree.inverter_sq_ne_one
    {D B K : Subgroup J} {S : Sylow 2 J} {p q : ℕ} [Fact q.Prime] {δ ε : Sign}
    (h : CaseThree D B (S : Subgroup J) K q δ ε)
    (hB : IsPGroup p B) (hp : Odd p) (hn : ¬ IsCyclic B)
    {t : J} (htK : t ∈ K) (hi : ∀ b ∈ B ⊓ K, t * b * t⁻¹ = b⁻¹) :
    t ^ 2 ≠ 1 := by
  have htnc := h.toCyclicDecomposition.inverter_not_centralizing hB hp hn hi
  have ht1 : t ≠ 1 := fun he => htnc (he ▸ (centralizer (B : Set J)).one_mem)
  intro ht2
  have hto : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  obtain ⟨e⟩ := h.sl2
  obtain ⟨z, hzc, hz⟩ := sl2_exists_central_involution K q h.odd_characteristic e
  let tk : K := ⟨t, htK⟩
  have he : tk = z := e.injective (sl2_involutions_equal q h.odd_characteristic
    (e tk) (e z) ((e.orderOf_eq tk).trans (by simpa only [← orderOf_coe] using hto))
    ((e.orderOf_eq z).trans hz))
  apply htnc
  apply le_centralizer_iff.mp h.toCyclicDecomposition.le_centralizer_centerImage
  exact ⟨tk, he ▸ hzc, rfl⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
