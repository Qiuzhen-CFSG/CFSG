module

public import CFSG.Quasithin.Chapter16.Section01To02.LiePreliminaries.Basic
public import Theory.SpecificGroups.PSL2.SylowPointwiseInner
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.OuterFixed

/-!
# Linear and Suzuki automorphism cases in Chapter 16

For a perfect central cover of binary PSL₂, an automorphism fixing a Sylow
two-subgroup pointwise is inner, with a conjugating element in that Sylow
subgroup. For a perfect central cover of Sz(2^(2m+1)), every automorphism
of two-power order is inner. These proofs use the genuine quotient action;
no splitting of the cover or proper-K hypothesis is required.

For an outer involution acting on the binary PSL₂ quotient, the full fixed
subgroup is PSL₂ over the square-root field. The degree-one endpoint is
retained: the fixed group there is PSL₂(2), before taking its two-residual.
This quotient calculation alone does not assert injectivity of the fixed
residual projection from an arbitrary central cover.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
16.1.4(4) and 16.1.6, printed pp.1171–1172; the reused model proofs establish
the inner-field coverage and fixed-field descent in GLS III, 2.5.12 and
2.6.5(e), and GLS IV, Chapter 4, 3.4(c).
-/

public section

namespace CFSG.Quasithin.Chapter16.LiePreliminaries
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups

variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]

/-- The binary PSL₂ case of the innerness assertion in 16.1.6.
It holds for arbitrary automorphisms, so includes every two-power order. -/
theorem psl2_sylow_fixing_inner (hodd : pPrimeCore 2 L = ⊥)
    {n : ℕ} (_hn : 0 < n)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (P : Sylow 2 L) (r : MulAut L) (hr : ∀ x ∈ P, r x = x) :
    ∃ x ∈ P, r = MulAut.conj x := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  exact MulAut.fixing_sylow_inner_of_centralQuotient
    ((centerQuotientEquivTwoCore hodd).trans e)
    Theory.PSL2.aut_fixing_sylow_inner P r hr

/-- Every two-element acts inner on a quasisimple Suzuki cover, including
the exceptional covers of Sz(8). No Sylow-fixing assumption is needed. -/
theorem suzuki_two_element_inner (hodd : pPrimeCore 2 L = ⊥)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m)
    (r : MulAut L) {k : ℕ} (hr : r ^ (2 ^ k) = 1) :
    ∃ x : L, r = MulAut.conj x := by
  let c := (centerQuotientEquivTwoCore hodd).trans e
  apply (MulAut.centralQuotientAction_inner_iff c r).mp
  apply MulAut.inner_of_two_pow_eq_one_of_odd_index (suzuki_odd_outer_index m hm)
  rw [← map_pow, hr, map_one]

/-- The Suzuki exclusion in Notation 16.1.3 and 16.1.4(4), on actual covers. -/
theorem suzuki_involution_inner (hodd : pPrimeCore 2 L = ⊥)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m)
    (r : MulAut L) (hr : orderOf r = 2) : ∃ x : L, r = MulAut.conj x := by
  apply suzuki_two_element_inner hodd hm e r (k := 1)
  simpa only [pow_one, hr] using pow_orderOf_eq_one r

/-- The actual quotient action of an outer involution in the binary PSL₂
case has the square-root-field fixed subgroup, including PSL₂(2). -/
theorem psl2_quotient_outer_fixed_model (hodd : pPrimeCore 2 L = ⊥)
    {n : ℕ} (hn : 2 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* PSL2BinaryMatrixGroup n)
    (r : MulAut L) (hr : orderOf r = 2)
    (houter : ¬ ∃ x : L, r = MulAut.conj x) :
    let c := (centerQuotientEquivTwoCore hodd).trans e
    ∃ m : ℕ, 0 < m ∧ n = 2 * m ∧
      Nonempty ((MulAut.centralQuotientAction c r).fixedSubgroup ≃*
        PSL2BinaryMatrixGroup m) := by
  dsimp only
  let c := (centerQuotientEquivTwoCore hodd).trans e
  let b := MulAut.centralQuotientAction c r
  have hrpow : r ^ 2 = 1 := by simpa only [hr] using pow_orderOf_eq_one r
  have hb : b ^ 2 = 1 := by
    change (MulAut.centralQuotientAction c r) ^ 2 = 1
    rw [← map_pow, hrpow, map_one]
  have hout : ¬ ∃ y, b = MulAut.conj y := fun h =>
    houter ((MulAut.centralQuotientAction_inner_iff c r).mp h)
  obtain ⟨g, σ, he⟩ := BenderSuzuki.ZD.Linear.binary_semilinear_coverage hn b
  exact BenderSuzuki.ZD.Linear.outer_fixed_model_of_semilinear hn b hb g σ he hout

/-- The field label in 16.1.4(4) is realized by an actual conjugation of an
entrywise field automorphism, with nonidentity involutory coefficient action. -/
theorem psl2_quotient_outer_field_action (hodd : pPrimeCore 2 L = ⊥)
    {n : ℕ} (hn : 2 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* PSL2BinaryMatrixGroup n)
    (r : MulAut L) (hr : orderOf r = 2)
    (houter : ¬ ∃ x : L, r = MulAut.conj x) :
    let c := (centerQuotientEquivTwoCore hodd).trans e
    ∃ (σ : BenderSuzuki.PFAppendixIII.BinaryGaloisField n ≃+*
        BenderSuzuki.PFAppendixIII.BinaryGaloisField n) (g : PSL2BinaryMatrixGroup n),
      Function.Involutive σ ∧ σ ≠ RingEquiv.refl _ ∧
      MulAut.centralQuotientAction c r =
        MulAut.congr (MulAut.conj g) (BenderSuzuki.ZD.Linear.fieldAut σ) := by
  dsimp only
  let c := (centerQuotientEquivTwoCore hodd).trans e
  let b := MulAut.centralQuotientAction c r
  have hrpow : r ^ 2 = 1 := by simpa only [hr] using pow_orderOf_eq_one r
  have hb : b ^ 2 = 1 := by
    change (MulAut.centralQuotientAction c r) ^ 2 = 1
    rw [← map_pow, hrpow, map_one]
  obtain ⟨g, σ, he⟩ := BenderSuzuki.ZD.Linear.binary_semilinear_coverage hn b
  obtain ⟨hs, hg⟩ := BenderSuzuki.ZD.Linear.semilinear_involution_data σ g
    (by rw [← he]; exact hb)
  have hne : σ ≠ RingEquiv.refl _ := by
    intro h
    apply houter
    apply (MulAut.centralQuotientAction_inner_iff c r).mp
    refine ⟨g, ?_⟩
    simpa only [h, BenderSuzuki.ZD.Linear.fieldAut_refl, mul_one] using he
  obtain ⟨d, hd⟩ := BenderSuzuki.ZD.Linear.semilinear_coboundary σ hs hne g hg
  exact ⟨σ, d, hs, hne, he.trans
    (BenderSuzuki.ZD.Linear.semilinear_congr_of_coboundary σ g d hd).symm⟩

end CFSG.Quasithin.Chapter16.LiePreliminaries
