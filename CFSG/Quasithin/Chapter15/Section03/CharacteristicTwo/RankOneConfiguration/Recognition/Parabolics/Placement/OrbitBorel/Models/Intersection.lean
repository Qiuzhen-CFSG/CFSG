module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.Reduction
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.OddRank.CoreNormalization.Models
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.QuasisimpleModels
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.Orders
public import Theory.SpecificGroups.PSL2.PrimeFieldTwoRank
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.SpecificGroups.G2Even.TwoRank
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAction
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder


/-!
# Intersection of the nonnormal and FF component models

For a finite quasisimple group, the complete lists in 1.2.1(3) and B.5.6
intersect in binary PSL₂ and PSL₃(2), provided three divides the order.
Both input predicates retain their actual multiplicative equivalences.
This is an intrinsic conditional comparison, not a proof of either catalogue
or of the ambient normality conclusion of 15.3.27.

The binary PSL₂ branch survives with every degree at least two; Suzuki is
excluded by its order. Odd-prime PSL₂ has two-rank two, and the order of J₁
bounds its two-rank by three. Hence the remaining FF field families reduce
to degree one, where explicit order comparisons settle every nonsurviving
case. The triple cover is excluded by its center. In particular, the full
G₂(2) and its genuine derived subgroup are compared separately.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 1.2.1(3),
printed pp.503–504; B.5.3–6, pp.104–105; proof of 15.3.27, pp.1130–1131.
The matrix order and rank results are the checked, attributed imports below.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel
open Chapter1.Section02
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels
universe u
variable {X : Type u} [Group X] [Finite X]

private def RemainingModel (X : Type u) [Group X] : Prop :=
  (∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL X 2 p) ∨ Nat.card X = 175560

omit [Finite X] in
private theorem odd_psl_card_ne_of_gap {p c b : ℕ} (ho : Odd p)
    (hm : ClassicalGroup.IsPSL X 2 p)
    (hlo : b * (b ^ 2 - 1) < 2 * c)
    (hhi : 2 * c < (b + 1) * ((b + 1) ^ 2 - 1)) : Nat.card X ≠ c := by
  intro hc
  have he := psl_two_card_mul hm
  have hg : Nat.gcd 2 (p - 1) = 2 :=
    Nat.gcd_eq_left (even_iff_two_dvd.mp (ho.tsub_odd odd_one))
  rw [hc, hg, mul_comm c 2] at he
  by_cases hpb : p ≤ b
  · have h := Nat.mul_le_mul hpb
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hpb 2) 1)
    omega
  · have hbp : b + 1 ≤ p := by omega
    have h := Nat.mul_le_mul hbp
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hbp 2) 1)
    omega

omit [Finite X] in
private theorem remaining_card_not_mem (hm : RemainingModel X) :
    Nat.card X ∉ ({6, 360, 720, 2520, 6048, 12096, 20160, 9999360} : Finset ℕ) := by
  rcases hm with ⟨p, hp, ho, hm⟩ | hc
  · intro hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with hc | hc | hc | hc | hc | hc | hc | hc
    · exact odd_psl_card_ne_of_gap ho hm (b := 2) (by norm_num) (by norm_num) hc
    · have he := parameter_nine_of_card_360 hm hc
      rw [he] at hp
      norm_num at hp
    · exact odd_psl_card_ne_of_gap ho hm (b := 11) (by norm_num) (by norm_num) hc
    · exact odd_psl_card_ne_of_gap ho hm (b := 17) (by norm_num) (by norm_num) hc
    · exact odd_psl_card_ne_of_gap ho hm (b := 22) (by norm_num) (by norm_num) hc
    · exact odd_psl_card_ne_of_gap ho hm (b := 28) (by norm_num) (by norm_num) hc
    · exact odd_psl_card_ne_of_gap ho hm (b := 34) (by norm_num) (by norm_num) hc
    · exact odd_psl_card_ne_of_gap ho hm (b := 271) (by norm_num) (by norm_num) hc
  · rw [hc]
    norm_num

private theorem remaining_two_rank_le (hm : RemainingModel X)
    (hns : ¬ Group.IsSolvable X) : primeRank 2 X ≤ 3 := by
  rcases hm with ⟨p, hp, ho, hm⟩ | hc
  · let : Fact p.Prime := ⟨hp⟩
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
    have hnsF : ¬ Group.IsSolvable PSL(2,F) := by
      intro hs
      let := hs
      exact hns (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
    have hlarge : 3 < p := hF ▸
      Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
        (hF ▸ ho) hnsF
    let : Fintype F := Fintype.ofFinite F
    let ef : F ≃+* ZMod p := (ZMod.ringEquivOfPrime F hp
      (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
    rw [primeRank_equiv 2 (e.trans (Atlas.fieldEquivPSL 2 ef)),
      Theory.PSL2.primeField_two_rank hlarge]
    decide
  · apply (primeRank_le_iff_elementary_card_le X).mpr
    intro A hA
    let := hA
    obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    have hk3 : k ≤ 3 := by
      by_contra h
      have hd := ((hk ▸ pow_dvd_pow 2 (show 4 ≤ k by omega))).trans
        A.card_subgroup_dvd_card
      rw [hc] at hd
      norm_num at hd
    rw [hk]
    exact Nat.pow_le_pow_right (by decide) hk3

private noncomputable def projectiveEquivOfCenterless {d : ℕ} {F : Type}
    [Field F] (hz : center X = ⊥) (e : X ≃* SL(d,F)) : X ≃* PSL(d,F) := by
  have hz' : center SL(d,F) = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv, hz]
    exact Nat.card_unique
  exact e.trans ((QuotientGroup.quotientMulEquivOfEq hz').trans
    QuotientGroup.quotientBot).symm

private theorem remaining_ff_intersection (hm : RemainingModel X)
    (hns : ¬ Group.IsSolvable X) (hz : center X = ⊥)
    (hf : FFAlternatives.QuasisimpleModel X) :
    (∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSL X 2 (2 ^ n)) ∨ ClassicalGroup.IsPSL X 3 2 := by
  have hr := remaining_two_rank_le hm hns
  have hno := remaining_card_not_mem hm
  cases hf with
  | linearTwo F e =>
    have hn : 2 ≤ F.degree := by
      by_contra hn
      have he : F.degree = 1 := by have := F.degree_pos; omega
      have hc := Nat.card_congr e.toEquiv
      rw [Atlas.card_sl_two, F.card_eq, he] at hc
      norm_num at hc
      apply hno
      simp [hc]
    exact Or.inl ⟨F.degree, hn, F.Carrier, inferInstance, inferInstance,
      F.card_eq, ⟨projectiveEquivOfCenterless hz e⟩⟩
  | linearThree F e =>
    let ep := projectiveEquivOfCenterless hz e
    have hrf := Matrix.PSL3Even.two_rank F.Carrier F.degree_pos F.card_eq
    rw [← primeRank_equiv 2 ep] at hrf
    have hn : F.degree = 1 := by have := F.degree_pos; omega
    exact Or.inr ⟨F.Carrier, inferInstance, inferInstance,
      by simpa [hn] using F.card_eq, ⟨ep⟩⟩
  | symplecticFour F e =>
    have hrf := Theory.SpecificGroups.SymplecticFour.EvenTwoRank.rank F.card_eq F.degree_pos
    rw [← primeRank_equiv 2 e] at hrf
    have hn : F.degree = 1 := by have := F.degree_pos; omega
    have hc := Nat.card_congr e.toEquiv
    rw [Theory.SpecificGroups.SymplecticFour.card_sp, F.card_eq, hn] at hc
    norm_num at hc
    exact (hno (by simp [hc])).elim
  | g2 F e =>
    have hrf := Atlas.G2.EvenTwoRank.two_rank F.Carrier F.card_eq
    rw [← primeRank_equiv 2 e] at hrf
    have hn : F.degree = 1 := by have := F.degree_pos; omega
    have hc := Nat.card_congr e.toEquiv
    rw [Atlas.G2.card_Model, F.card_eq, hn] at hc
    norm_num at hc
    exact (hno (by simp [hc])).elim
  | alternatingSix e =>
    have hc := Nat.card_congr e.toEquiv
    rw [nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial] at hc
    exact (hno (by simp [hc])).elim
  | alternatingSeven e =>
    have hc := Nat.card_congr e.toEquiv
    rw [nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial] at hc
    exact (hno (by simp [hc])).elim
  | tripleSix e _ =>
    have hc := Nat.card_congr e.toEquiv
    rw [hz] at hc
    norm_num at hc
  | g2DerivedTwo e =>
    have hc := (Nat.card_congr e.toEquiv).trans
      Atlas.G2.LieAutomorphismExtensions.card_binaryDerived
    exact (hno (by simp [hc])).elim
  | linearFourTwo e =>
    let ep := projectiveEquivOfCenterless hz e
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 4
    rw [← Nat.card_congr ep.toEquiv] at hc
    norm_num [Fin.prod_univ_succ] at hc
    exact (hno (by simp [hc])).elim
  | linearFiveTwo e =>
    let ep := projectiveEquivOfCenterless hz e
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
    rw [← Nat.card_congr ep.toEquiv] at hc
    norm_num [Fin.prod_univ_succ] at hc
    exact (hno (by simp [hc])).elim

/-- The intrinsic intersection of the complete nonnormal and FF component lists.
The divisibility premise is supplied by `component_three_divides_quotient` in
the ambient application; no field-degree parity restriction is imposed. -/
theorem intrinsic_model_intersection [IsQuasisimple X]
    (hm : NonnormalCComponentModel X) (hf : FFAlternatives.QuasisimpleModel X)
    (hthree : 3 ∣ Nat.card X) :
    (∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSL X 2 (2 ^ n)) ∨ ClassicalGroup.IsPSL X 3 2 := by
  let : IsSimpleGroup (X ⧸ center X) := IsQuasisimple.simple
  have : Nontrivial X := (QuotientGroup.mk'_surjective (center X)).nontrivial
  have hns : ¬ Group.IsSolvable X := Group.IsPerfect.not_isSolvable X
  have hz := ComponentIntersection.CoreNormalization.nonnormalModel_center_eq_bot hm hns
  cases hm with
  | linear_even n hn hm => exact Or.inl ⟨n, hn, hm⟩
  | suzuki m hm iso =>
    obtain ⟨e⟩ := iso
    rw [Nat.card_congr e.toEquiv] at hthree
    exact (BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega) hthree).elim
  | linear_prime p hp ho hm =>
    exact remaining_ff_intersection (Or.inl ⟨p, hp, ho, hm⟩) hns hz hf
  | janko iso =>
    obtain ⟨e⟩ := iso
    exact remaining_ff_intersection
      (Or.inr ((Nat.card_congr e.toEquiv).trans Janko1.card_model)) hns hz hf

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel
