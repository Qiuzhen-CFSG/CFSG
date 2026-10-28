module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.ModelComparison.Inputs
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.LieParameter.CardBounds
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import Theory.SpecificGroups.Janko1.Model.Certification.Order

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.FormTransport
public import BenderSuzuki.External.Huppert.II.theorem_10_12
public import Theory.SpecificGroups.ThreeDivisibility.Classical

/-!
# Classical exclusions in the moving-component comparison

For q = 2^m ≥ 4, the orders of PSU₃(q), PSL₃(q), and PSp₄(q) have
respective two-power divisors q³, q³, and q⁴. Their total orders are too
small for either binary or odd-prime PSL₂ with those divisors. Divisibility
by three excludes Suzuki, while divisibility by sixteen excludes the
certified J₁ matrix group. This treats all four constructors of the actual
nonnormal C-component list.

The unitary calculation transports every allowed Hermitian form by an actual
projective conjugation equivalence. The symplectic calculation uses the
proved equivalence from Sp₄ to its central quotient in characteristic two.
The bound m ≥ 2 is retained, in particular excluding the PSL₃(2) endpoint.

The intrinsic order estimates adapt the calculations in
`RankOneModels.LieParameter.SplitModels` and `.Unitary` from Chapter 15;
only the elementary arithmetic theorem from `.CardBounds` is imported.
No later source theorem is used. The matrix order results retain their
ATLAS attribution and license in their owning lower modules.

Source: Aschbacher–Smith, 1.1.5(3a,b), printed pp.501–503, 1.2.1(3),
p.504, and their comparison in the proof of 13.6.6, p.927.
-/

open CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent.ModelComparison
variable {Q : Type*} [Group Q]

/-- The odd factor in the binary PSL₂ order cannot absorb a power of two. -/
private theorem not_binary_of_order_bounds {f n b : ℕ} (hf : 2 ≤ f)
    (hmodel : ClassicalGroup.IsPSL Q 2 (2^f)) (hd : 2^n ∣ Nat.card Q)
    (hc : Nat.card Q ≤ 2^n*(2^n-1)*b) (hb : 2*b+2 < 2^n) : False := by
  have ht : 2 ≤ 2^f := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 1 ≤ f by omega)
  have heven : Even (2^f) := even_two.pow_of_ne_zero (by omega)
  have hodd : Odd (2^f-1) := Nat.Even.sub_odd (by omega) heven odd_one
  have he := psl_two_card_mul hmodel
  rw [(Nat.coprime_two_left.mpr hodd).gcd_eq_one, mul_one] at he
  have hsodd : Odd ((2^f)^2-1) :=
    Nat.Even.sub_odd (by nlinarith) (heven.pow_of_ne_zero (by decide)) odd_one
  have hcop := (Nat.coprime_two_left.mpr hsodd).pow_left n
  have hdiv : 2^n ∣ 2^f := hcop.dvd_mul_right.mp (he ▸ hd)
  have hle : 2^n ≤ 2^f := Nat.le_of_dvd (by positivity) hdiv
  have hlower := Nat.mul_le_mul hle
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left hle 2) 1)
  let a := 2^n
  have ha : 3 ≤ a := by dsimp [a]; omega
  have hs1 : a-1+1=a := Nat.sub_add_cancel (by omega)
  have hs2 : a^2-1+1=a^2 := Nat.sub_add_cancel (by nlinarith)
  have hfac : (a-1)*(a+1) = a^2-1 := by nlinarith
  have hlt : a*(a-1)*b < a*(a^2-1) := by
    calc
      _ < a*(a-1)*(a+1) := Nat.mul_lt_mul_of_pos_left (by dsimp [a]; omega)
        (Nat.mul_pos (by omega) (by omega))
      _ = _ := by rw [mul_assoc, hfac]
  exact (not_lt_of_ge (hlower.trans_eq he.symm)) (hc.trans_lt hlt)

/-- A common order comparison eliminates the complete four-model list. -/
private theorem not_nonnormal_of_order_bounds {n b : ℕ} (hn : 4 ≤ n)
    (hd : 2^n ∣ Nat.card Q) (hc : Nat.card Q ≤ 2^n*(2^n-1)*b)
    (hb : 2*b+2 < 2^n) (hthree : 3 ∣ Nat.card Q) :
    ¬ NonnormalCComponentModel Q := by
  intro h
  cases h with
  | linear_even f hf iso => exact not_binary_of_order_bounds hf iso hd hc hb
  | suzuki m hm iso =>
      obtain ⟨e⟩ := iso
      rw [Nat.card_congr e.toEquiv] at hthree
      exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega) hthree
  | linear_prime p hp ho iso =>
      exact LieParameter.not_of_two_power_order_product ho hp.two_le iso hd hc hb
  | janko iso =>
      obtain ⟨e⟩ := iso
      have h16 : 16 ∣ Nat.card Q := (show 2^4 ∣ 2^n from pow_dvd_pow 2 hn).trans hd
      rw [Nat.card_congr e.toEquiv, Janko1.card_model] at h16
      norm_num at h16

private theorem twice_square_lt_pow {q r : ℕ} (hq : 4 ≤ q) (hr : 3 ≤ r) :
    2*(q^2-1)+2 < q^r := by
  have hs : q^2-1+1=q^2 := Nat.sub_add_cancel (by nlinarith)
  have hh := Nat.mul_lt_mul_of_pos_left (show 2 < q by omega)
    (show 0 < q^2 by positivity)
  have hc : 2*(q^2-1)+2 < q^3 := by nlinarith
  exact hc.trans_le (Nat.pow_le_pow_right (by omega) hr)

private theorem linear_not_nonnormal {f : ℕ} (hf : 2 ≤ f)
    (hmodel : ClassicalGroup.IsPSL Q 3 (2^f)) : ¬ NonnormalCComponentModel Q := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
  let q := 2^f
  have hq : 4 ≤ q := by simpa [q] using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hf
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  rw [← Nat.card_congr e.toEquiv, hF] at hc
  change Nat.card Q * Nat.gcd 3 (q-1) * (q-1) = _ at hc
  simp only [Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero,
    pow_one, Nat.zero_add, Nat.reduceAdd, Fin.prod_univ_zero, mul_one] at hc
  change Nat.card Q * Nat.gcd 3 (q-1) * (q-1) =
    (q^3-1)*((q^3-q)*(q^3-q^2)) at hc
  have hfact1 : q^3-q = q*(q^2-1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]; congr 1; ring
  have hfact2 : q^3-q^2 = q^2*(q-1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]; congr 1
  have hc' : Nat.card Q * Nat.gcd 3 (q-1) = q^3*(q^3-1)*(q^2-1) := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < q-1 by omega)
    calc
      _ = (q^3-1)*((q^3-q)*(q^3-q^2)) := hc
      _ = _ := by rw [hfact1, hfact2]; ring
  have hd : q^3 ∣ Nat.card Q := by
    have hcop : Nat.Coprime (q^3) (Nat.gcd 3 (q-1)) := by
      apply Nat.Coprime.pow_left
      apply Nat.Coprime.pow_left
      exact (show Nat.Coprime 2 3 by decide).of_dvd_right (Nat.gcd_dvd_left 3 (q-1))
    apply hcop.dvd_mul_right.mp
    rw [hc']
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  apply not_nonnormal_of_order_bounds (n := f*3) (b := q^2-1) (by omega)
  · simpa only [pow_mul] using hd
  · rw [pow_mul]
    exact (Nat.le_mul_of_pos_right _ (Nat.gcd_pos_of_pos_left _ (by decide))).trans_eq hc'
  · simpa only [pow_mul] using twice_square_lt_pow hq (by decide : 3 ≤ 3)
  · rw [Nat.card_congr e.toEquiv]
    exact Matrix.ProjectiveSpecialLinearGroup.three_dvd_card F 3 (by decide)

private theorem symplectic_not_nonnormal {f : ℕ} (hf : 2 ≤ f)
    (hmodel : ClassicalGroup.IsPSp Q 2 (2^f)) : ¬ NonnormalCComponentModel Q := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
  let := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hc := (Nat.card_congr e.toEquiv).trans
    (Nat.card_congr (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm.toEquiv)
  rw [Theory.SpecificGroups.SymplecticFour.card_sp, hF] at hc
  let q := 2^f
  have hq : 4 ≤ q := by simpa [q] using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hf
  have hc' : Nat.card Q = q^4*(q^4-1)*(q^2-1) := by rw [hc]; ring
  apply not_nonnormal_of_order_bounds (n := f*4) (b := q^2-1) (by omega)
  · rw [hc', pow_mul]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  · rw [pow_mul]; exact hc'.le
  · simpa only [pow_mul] using twice_square_lt_pow hq (by decide : 3 ≤ 4)
  · rw [Nat.card_congr e.toEquiv]
    exact Theory.SpecificGroups.ThreeDivisibility.symplectic F hF

private theorem unitary_order_estimate {q : ℕ} (hq : 4 ≤ q) :
    (q^3+1)*q^3*(q^2-1) ≤ q^3*(q^3-1)*(q^2+1) ∧
      2*(q^2+1)+2 < q^3 := by
  have hsq : 1 ≤ q^2 := by nlinarith
  have hcube : q^2 ≤ q^3 := by nlinarith [sq_nonneg q]
  have hs2 : q^2-1+1=q^2 := Nat.sub_add_cancel hsq
  have hs3 : q^3-1+1=q^3 := Nat.sub_add_cancel (by omega)
  constructor
  · have h : (q^3+1)*(q^2-1) ≤ (q^3-1)*(q^2+1) := by nlinarith
    calc
      _ = q^3*((q^3+1)*(q^2-1)) := by ring
      _ ≤ q^3*((q^3-1)*(q^2+1)) := Nat.mul_le_mul_left _ h
      _ = _ := by ring
  · nlinarith [sq_nonneg (q-4)]

open Matrix BenderSuzuki.MatrixGroups CFSG.Quasithin.ChapterF.Source.Unitary in
private theorem unitary_not_nonnormal {f : ℕ} (hf : 2 ≤ f)
    (h : ClassicalGroup.IsPSU Q 3 (2^f)) : ¬ NonnormalCComponentModel Q := by
  rcases h with ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J f (by omega) hcard hconj
  let K := FormTransport.standardForm J
  let e' := e.trans (FormTransport.projectiveEquiv J C hC)
  have hfixed : Nat.card {x : F // K.conj x = x} = 2^f :=
    fixed_card J f (by omega) hcard hconj
  rcases BenderSuzuki.External.huppert_II_10_12 K (2^f) hcard hfixed rfl with
    ⟨_, _rho, _pinf, _hrho, _hnatural, _hUcard, hroot, _htwo, horder, _hthree⟩
  have he : Nat.card Q = Nat.card (ProjectiveSpecialUnitaryMatrixGroup K) :=
    Nat.card_congr e'.toEquiv
  have hq : 4 ≤ 2^f := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hf
  obtain ⟨hbound, hsmall⟩ := unitary_order_estimate hq
  apply not_nonnormal_of_order_bounds (n := f*3) (b := (2^f)^2+1) (by omega)
  · rcases hroot with ⟨R, H, _, _, _, _, _, _, hRcard, _⟩
    rw [he, pow_mul, ← hRcard]
    exact R.card_subgroup_dvd_card
  · calc
      Nat.card Q ≤ ((2^f)^3+1)*(2^f)^3*((2^f)^2-1) := by
        rw [he, horder]
        exact Nat.div_le_self _ _
      _ ≤ _ := by simpa only [pow_mul] using hbound
  · simpa only [pow_mul] using hsmall
  · rw [Nat.card_congr e.toEquiv]
    exact Theory.SpecificGroups.ThreeDivisibility.unitary_three_dvd J f (by omega) hcard hconj

universe u
/-- The three larger classical models are absent from the complete nonnormal list. -/
public theorem classical_exclusions (Q : Type u) [Group Q] [Finite Q] [IsSimpleGroup Q]
    [Group.IsPerfect Q] : ClassicalExclusions Q where
  unitary _ hm h := unitary_not_nonnormal hm h
  linear _ hm h := linear_not_nonnormal hm h
  symplectic _ hm h := symplectic_not_nonnormal hm h

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent.ModelComparison
