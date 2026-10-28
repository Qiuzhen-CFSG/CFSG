module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio.Models

/-!
# Comparisons for the surviving B.4.5 rows

The actual Suzuki group determines its parameter. The two-part of the
Mathieu order excludes M₂₂ against every source family. For SU₃, the
projective root rank and order first recover the fixed-field exponent;
an explicit primitive cubic scalar then contradicts centerlessness at odd
exponent. No projective group is identified with SU without proving that
its central kernel vanishes.

Source: Aschbacher--Smith, B.4.5 and K.3.3, printed pp.87 and 456,
and the odd-exponent restriction on printed p.1152.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Matrix
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio
open FFExclusions.ModelRigidity
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.UnitaryModels

variable {S : Type*} [Group S] {f : ℕ}

/-- Transport a source marking along a specified group isomorphism. -/
theorem SourceModel.transport {R : Type*} [Group R]
    (h : SourceModel S f) (a : R ≃* S) : SourceModel R f := by
  cases h with
  | linearTwo F hF e => exact .linearTwo F hF (a.trans e)
  | linearThree F hF e => exact .linearThree F hF (a.trans e)
  | symplecticFour F hF e => exact .symplecticFour F hF (a.trans e)
  | suzuki m hm he e => exact .suzuki m hm he (a.trans e)
  | unitary F J hF hc e => exact .unitary F J hF hc (a.trans e)

theorem SourceModel.suzuki_degree (hs : SourceModel S f) (hf : 1 < f)
    {k : ℕ} (hk : 0 < k) (a : S ≃* SuzukiMatrixGroup k) : f = 2 * k + 1 := by
  have hn : ¬ 3 ∣ Nat.card S := by
    rw [Nat.card_congr a.toEquiv]
    exact suzukiMatrixGroup_three_free k hk
  cases hs with
  | linearTwo F hF e =>
    exact (hn (ComponentModel.three_dvd_card (.linearTwo F (by omega) hF e))).elim
  | linearThree F hF e =>
    exact (hn (ComponentModel.three_dvd_card (.linearThree F (by omega) hF e))).elim
  | symplecticFour F hF e =>
    exact (hn (ComponentModel.three_dvd_card
      (.symplecticFour F hf hF (e.trans (symplecticProjectiveEquiv hf hF))))).elim
  | unitary F J hF hc e =>
    apply (hn ?_).elim
    rw [Nat.card_congr e.toEquiv]
    exact Theory.SpecificGroups.ThreeDivisibility.unitary_three_dvd J f (by omega) hF hc
  | suzuki m hm he e =>
    have hcard := Nat.card_congr (e.symm.trans a).toEquiv
    have hmk := suzukiMatrixGroup_degree_dvd_of_card_dvd hm hk (dvd_of_eq hcard)
    have hkm := suzukiMatrixGroup_degree_dvd_of_card_dvd hk hm (dvd_of_eq hcard.symm)
    exact he.trans (Nat.dvd_antisymm hmk hkm)

theorem SourceModel.not_mathieuTwentyTwo (hs : SourceModel S f) (hf : 1 < f)
    (a : S ≃* Sporadic.Mathieu.M22) : False := by
  have horder : Nat.card S = 443520 :=
    (Nat.card_congr a.toEquiv).trans Sporadic.Mathieu.m22_order
  have hpart : (Nat.card S).factorization 2 = 7 := by
    rw [horder]; decide +kernel
  cases hs with
  | linearTwo F hF e =>
    have hp := (pslTwo_invariants (by omega : 0 < f) hF).2
    rw [← Nat.card_congr e.toEquiv, hpart] at hp
    have hc := pslTwo_card hF
    rw [← Nat.card_congr e.toEquiv, horder, ← hp] at hc
    norm_num at hc
  | linearThree F hF e =>
    have hp := (pslThree_invariants (by omega : 0 < f) hF).2
    rw [← Nat.card_congr e.toEquiv, hpart] at hp
    omega
  | symplecticFour F hF e =>
    have hp := (spFour_invariants (by omega : 0 < f) hF).2
    rw [← Nat.card_congr (e.trans (symplecticProjectiveEquiv hf hF)).toEquiv, hpart] at hp
    omega
  | unitary F J hF hc e =>
    have hp := (projective_invariants J (by omega : 0 < f) hF hc).2
    rw [← Nat.card_congr e.toEquiv, hpart] at hp
    omega
  | suzuki m hm _ e =>
    apply suzukiMatrixGroup_three_free m hm
    rw [← Nat.card_congr e.toEquiv, horder]
    decide

/-- Order's two-part recovers the unitary fixed-field exponent. The root
rank excludes all three other three-divisible infinite source families. -/
theorem SourceModel.unitary_degree [Finite S] (hs : SourceModel S f) (hf : 1 < f)
    {E : Type} [Field E] [Finite E] (J : HermitianForm 3 E) {n : ℕ}
    (hn : 0 < n) (hE : Nat.card E = (2 ^ n) ^ 2)
    (hc : ∀ x, J.conj x = x ^ (2 ^ n))
    (a : S ≃* ProjectiveSpecialUnitaryMatrixGroup J) : n = f := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv S a.toEquiv
  obtain ⟨hr, hp⟩ := projective_invariants J hn hE hc
  rw [← primeRank_equiv 2 a] at hr
  rw [← Nat.card_congr a.toEquiv] at hp
  cases hs with
  | linearTwo F hF e =>
    obtain ⟨hr', hp'⟩ := pslTwo_invariants (by omega : 0 < f) hF
    rw [← primeRank_equiv 2 e] at hr'
    rw [← Nat.card_congr e.toEquiv] at hp'
    omega
  | linearThree F hF e =>
    obtain ⟨hr', hp'⟩ := pslThree_invariants (by omega : 0 < f) hF
    rw [← primeRank_equiv 2 e] at hr'
    rw [← Nat.card_congr e.toEquiv] at hp'
    omega
  | symplecticFour F hF e =>
    let b := e.trans (symplecticProjectiveEquiv hf hF)
    obtain ⟨hr', hp'⟩ := spFour_invariants (by omega : 0 < f) hF
    rw [← primeRank_equiv 2 b] at hr'
    rw [← Nat.card_congr b.toEquiv] at hp'
    omega
  | unitary F J' hF hc' e =>
    have hp' := (projective_invariants J' (by omega : 0 < f) hF hc').2
    rw [← Nat.card_congr e.toEquiv] at hp'
    omega
  | suzuki m hm _ e =>
    apply (suzukiMatrixGroup_three_free m hm ?_).elim
    rw [Nat.card_congr (e.symm.trans a).toEquiv]
    exact Theory.SpecificGroups.ThreeDivisibility.unitary_three_dvd J n hn hE hc

/-- A primitive cubic scalar is a nonidentity central SU₃ element when the
fixed-field exponent is odd. This is about SU, not its projective image. -/
theorem specialUnitary_center_ne_bot {E : Type} [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (ho : Odd n)
    (hE : Nat.card E = (2 ^ n) ^ 2) (hc : ∀ x, J.conj x = x ^ (2 ^ n)) :
    center J.specialSubgroup ≠ ⊥ := by
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Eˣ) 3 (by
    rw [Nat.card_units, hE, ← pow_mul]
    exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff (n * 2)).mpr ⟨n, by omega⟩)
  have hu3 : u ^ 3 = 1 := (orderOf_eq_prime_iff.mp hu).1
  have hne : u ≠ 1 := (orderOf_eq_prime_iff.mp hu).2
  have huv : (u : E) ^ 3 = 1 := congrArg Units.val hu3
  have hnorm : J.conj (u : E) * u = 1 := by
    rw [hc, ← pow_succ]
    have hm := Nat.BinaryTorusParity.two_pow_mod_three n
    have ho' := Nat.odd_iff.mp ho
    rw [ho'] at hm
    norm_num at hm
    have hd : 3 ∣ 2 ^ n + 1 := by omega
    obtain ⟨k, hk⟩ := hd
    rw [hk, pow_mul, huv, one_pow]
  have hs : GeneralLinearGroup.scalar (Fin 3) u ∈ J.specialSubgroup := by
    rw [J.mem_specialSubgroup_iff]
    constructor
    · have hadj : J.conjTranspose (Matrix.scalar (Fin 3) (u : E)) =
          Matrix.scalar (Fin 3) (J.conj u) := by
        ext i j
        by_cases hij : i = j
        · subst j; simp [HermitianForm.conjTranspose, Matrix.scalar_apply]
        · simp [HermitianForm.conjTranspose, Matrix.scalar_apply, hij, Ne.symm hij]
      change J.conjTranspose (Matrix.scalar (Fin 3) (u : E)) * J.form *
        Matrix.scalar (Fin 3) (u : E) = J.form
      rw [hadj]
      ext i j
      simp only [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
      calc J.conj (u : E) * J.form i j * u = (J.conj (u : E) * u) * J.form i j := by ring
           _ = J.form i j := by rw [hnorm, one_mul]
    · change GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) u) = 1
      simpa using hu3
  let z : J.specialSubgroup := ⟨_, hs⟩
  have hz : z ∈ center J.specialSubgroup := by
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact mem_center_iff.mp (by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨u, rfl⟩) x.val
  intro hbot
  have he : z = 1 := by simpa only [hbot, mem_bot] using hz
  have he' := congrArg (fun g : J.specialSubgroup => g.val.val 0 0) he
  apply hne
  apply Units.ext
  simpa [z, GeneralLinearGroup.scalar] using he'

theorem SourceModel.not_specialUnitary [Finite S] (hs : SourceModel S f)
    (hf : 1 < f) (ho : Odd f) (hz : center S = ⊥)
    {E : Type} [Field E] [Finite E] (J : HermitianForm 3 E) {n : ℕ}
    (hn : 0 < n) (hE : Nat.card E = (2 ^ n) ^ 2)
    (hc : ∀ x, J.conj x = x ^ (2 ^ n)) (a : S ≃* J.specialSubgroup) : False := by
  have hz' := centerless_of_equiv hz a
  have he := hs.unitary_degree hf J hn hE hc
    (a.trans (J.specialProjectiveEquivOfCenterEqBot hz'))
  exact specialUnitary_center_ne_bot J (he.symm ▸ ho) hE hc hz'

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio
