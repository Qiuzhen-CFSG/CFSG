module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveEvenModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveOddModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveSporadicModels
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.SpecificGroups.PSL2.OddPerfectCore
public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryContaining
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BenderSylowOvergroups
public import Theory.GroupTheory.SolvableSylowOvergroups
public import Theory.Alternating.PrimeRank

/-!
# Non-enlargement of a full-Sylow local PSL₂(8)

An SQTK group with Sylow two-subgroups of order at most eight cannot properly
enlarge a local PSL₂(8) inside a C-component. The binary subgroup first makes
the containing component quasisimple. It embeds in that component's simple
radical quotient. The actual Theorem C catalogue, the divisor 504, two-rank
at least three, and the absence of a factor sixteen leave only Bender groups.
Their proper full-Sylow overgroups are solvable, and the central radical
kernel preserves this property. Local component minimality gives equality.

The order calculations specialize the existing A₅-containing calculations
with their numerical premises; they do not assume an A₅ subgroup here.
The actual consumer is `Chapter14/Section02/EightLargeParabolic/Component`.
Source: Aschbacher--Smith A.3.6, A.3.12 and the first paragraph of 14.2.18,
printed pp.43--48,987 in `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.EightSylow
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

private theorem power_dvd {a b : ℕ} (h : 4 ≤ a * b) : 16 ∣ (2 ^ a) ^ b := by
  rw [← pow_mul]
  exact Nat.pow_dvd_pow 2 h

omit [Finite G] in
private theorem not_linear_of_small_twoPart
    (hcard : 504 ∣ Nat.card G) (hsmall : ¬ 16 ∣ Nat.card G)
    {n : ℕ} (hn : 1 ≤ n) (hm : ClassicalGroup.IsPSL G 3 (2 ^ n)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  by_cases hn2 : 2 ≤ n
  · have hd := (Matrix.PSL3.LinearThree.unipotent F).card_subgroup_dvd_card
    rw [Matrix.PSL3.LinearThree.card_unipotent,hF,← Nat.card_congr e.toEquiv] at hd
    exact hsmall ((power_dvd (by omega : 4 ≤ n * 3)).trans hd)
  · have hn1 : n = 1 := by omega
    have hd := hcard
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hF,hn1] at hd
    norm_num at hd

omit [Finite G] in
private theorem not_symplectic_of_small_twoPart
    (hsmall : ¬ 16 ∣ Nat.card G) {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSp G 2 (2 ^ n)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let a := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm
  have hd := (Theory.SpecificGroups.SymplecticFour.unipotent (F := F)).card_subgroup_dvd_card
  rw [Theory.SpecificGroups.SymplecticFour.card_unipotent,hF,
    ← Nat.card_congr a.toEquiv] at hd
  exact hsmall ((power_dvd (by omega : 4 ≤ n * 4)).trans hd)

omit [Finite G] in
private theorem not_g2_of_small_twoPart
    (hsmall : ¬ 16 ∣ Nat.card G) {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassificationModels.IsG2At G (2 ^ n)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  apply hsmall
  rw [Nat.card_congr e.toEquiv,Atlas.G2.card_Model,hF]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
    (power_dvd (by omega : 4 ≤ n * 6)) _) _

omit [Finite G] in
private theorem not_triality_of_small_twoPart
    (hsmall : ¬ 16 ∣ Nat.card G) {n : ℕ} (hn : 1 ≤ n)
    (hm : Triality.Standard.IsTrialityGroupAt (2 ^ n) G) : False := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff G n (by omega)).mp hm
  let P := Triality.Standard.binaryParameters n (by omega : 0 < n)
  have hd := (Triality.Standard.Parabolics.unipotent P).card_subgroup_dvd_card
  rw [Triality.Standard.Parabolics.card_unipotent_binary P rfl] at hd
  change (2 ^ n) ^ 12 ∣ Nat.card (Triality.Standard.BinaryCarrier n _) at hd
  rw [← Nat.card_congr e.toEquiv] at hd
  exact hsmall ((power_dvd (by omega : 4 ≤ n * 12)).trans hd)

omit [Finite G] in
private theorem not_ree_of_small_twoPart (m : ℕ) (hsmall : ¬ 16 ∣ Nat.card G)
    (e : G ≃* ReeF4.Model m) : False := by
  have hd := (ReeF4.Parabolics.unipotent m).card_subgroup_dvd_card
  rw [ReeF4.Parabolics.card_unipotent,← Nat.card_congr e.toEquiv] at hd
  exact hsmall ((power_dvd (by omega : 4 ≤ (2 * m + 1) * 12)).trans hd)

private theorem sixteen_linear {F : Type*} [Field F] [Finite F]
    (ho : Odd (Nat.card F)) : 16 ∣ Nat.card PSL(3,F) := by
  have h2 : 2 ∣ Nat.card F ^ 3 - 1 := by
    have := Nat.odd_iff.mp (ho.pow : Odd (Nat.card F ^ 3))
    omega
  have h16 : 16 ∣ Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
    exact mul_dvd_mul (dvd_mul_of_dvd_right h2 _) (Nat.eight_dvd_sq_sub_one_of_odd ho)
  rw [← PSL3.LinearThree.card_projective_mul_scalar F] at h16
  exact ((by decide : Nat.Coprime 16 3).of_dvd_right
    (Nat.gcd_dvd_left 3 (Nat.card F - 1))).dvd_of_dvd_mul_right h16

private theorem sixteen_unitary {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hc : Nat.card F = p ^ 2) (hj : ∀ x, J.conj x = x ^ p) :
    16 ∣ Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) := by
  have hfix := FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
    (by simpa using hc) (by simpa using hj)
  simp only [pow_one] at hfix
  rw [Representation.SU3.BinaryDegree.card_projective J hc hfix]
  have hg : Nat.gcd 3 (p + 1) ∣ p ^ 2 - 1 := by
    rw [show p ^ 2 - 1 = (p - 1) * (p + 1) by
      simpa [mul_comm] using Nat.sq_sub_sq p 1]
    exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right 3 (p + 1)) _
  have hd := dvd_mul_of_dvd_right hg ((p ^ 3 + 1) * p ^ 3)
  have h2 : 2 ∣ p ^ 3 + 1 := by
    have := Nat.odd_iff.mp (ho.pow : Odd (p ^ 3))
    omega
  have hcop := (by decide : Nat.Coprime 16 3).of_dvd_right (Nat.gcd_dvd_left 3 (p + 1))
  apply hcop.dvd_of_dvd_mul_right
  rw [Nat.div_mul_cancel hd]
  exact mul_dvd_mul (dvd_mul_of_dvd_left h2 _) (Nat.eight_dvd_sq_sub_one_of_odd ho)

private theorem held_sixteen : 16 ∣ Nat.card Held.He := by
  open Held.LocalPairs.SylowGeometry.Calculations in
  obtain ⟨n,hn⟩ := representative_isPGroup.exists_card_eq
  have hl := Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.representative_card_ge_of_orbit_labels
    Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.orbitSizeLabel_eq_card_orbit
  have hn4 : 4 ≤ n := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    exact (by decide : 2 ^ 4 ≤ 1024).trans (hn ▸ hl)
  have hd : 16 ∣ Nat.card Held.LocalPairs.SylowGeometry.Calculations.representative := by
    rw [hn]
    exact pow_dvd_pow 2 hn4
  exact hd.trans (card_subgroup_dvd_card _)

private theorem hs_sixteen : 16 ∣ Nat.card Sporadic.LeechRelated.HS.Carrier := by
  apply dvd_trans (b := Nat.card Sporadic.LeechRelated.HS.EvenLocalCandidates.subgroup)
  · rw [Sporadic.LeechRelated.HS.EvenLocalCandidates.subgroup_card]
    decide
  · exact card_subgroup_dvd_card _


/-- The source catalogue with an elementary Sylow of order eight and a
PSL₂(8) subgroup leaves only the Bender families. -/
theorem bender_of_eight_section (hm : TheoremCModel G)
    (hsmall : ¬ 16 ∣ Nat.card G) (hcard : 504 ∣ Nat.card G)
    (hr : 3 ≤ primeRank 2 G) : ClassificationModels.IsBenderModel G := by
  cases hm with
  | alternating n hn he =>
    let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have hd := hcard
    rw [Nat.card_congr he.some.toEquiv, nat_card_alternatingGroup] at hd
    obtain ⟨hl,hu⟩ := hn
    interval_cases n
    · norm_num [Nat.factorial] at hd
    · norm_num [Nat.factorial] at hd
    · have h := (GLS3.Chapter5.PRank.alternating_hasPRank_two 7).primeRank_eq Nat.prime_two
      rw [primeRank_equiv 2 he.some, h] at hr
      norm_num at hr
    · apply (hsmall _).elim
      rw [Nat.card_congr he.some.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
  | linear_odd p k hp ho hk hs he =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
    have hq : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
      ⟨p,k,hp,ho,by rcases hk with rfl | rfl <;> decide,hF⟩
    let S : Sylow 2 PSL(2,F) := default
    obtain ⟨n,_,⟨d⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hq S
    have hle : primeRank 2 PSL(2,F) ≤ 2 := by
      rw [S.primeRank_eq,primeRank_equiv 2 d]
      exact dihedral_rank_le_two n
    rw [primeRank_equiv 2 e] at hr
    omega
  | three_odd p hp ho un he =>
    apply (hsmall _).elim
    cases un with
    | false =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
      rw [Nat.card_congr e.toEquiv]
      exact sixteen_linear (hF ▸ ho)
    | true =>
      obtain ⟨F,_,_,J,hF,hJ,⟨e⟩⟩ := he
      let : Fact p.Prime := ⟨hp⟩
      rw [Nat.card_congr e.toEquiv]
      exact sixteen_unitary J ho hF hJ
  | rank_one hm => exact hm
  | rank_two hm =>
    apply False.elim
    cases hm with
    | linear n hn hm => exact not_linear_of_small_twoPart hcard hsmall hn hm
    | symplectic n hn hm => exact not_symplectic_of_small_twoPart hsmall hn hm
    | g2 n hn hm => exact not_g2_of_small_twoPart hsmall hn hm
    | triality n hn hm => exact not_triality_of_small_twoPart hsmall hn hm
    | ree m hm he =>
      obtain ⟨e⟩ := (ReeF4.exists_localBlockInput_mulEquiv_iff G m).mp he
      exact not_ree_of_small_twoPart m hsmall e
    | symplectic_derived he =>
      let e := he.some.trans
        Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hcard
      norm_num [Nat.factorial] at hcard
    | g2_derived he =>
      apply hsmall
      rw [Nat.card_congr he.some.toEquiv,
        Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
      decide
    | tits he =>
      apply hsmall
      rw [Nat.card_congr he.some.toEquiv,Tits.parrottGroup_card]
      decide
  | binary_linear n hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    have h := @Atlas.ExceptionalSupport.card_psl_mul F _ n (by rcases hn with rfl | rfl <;> infer_instance) _
    rw [hF] at h
    norm_num at h
    apply (hsmall _).elim
    rw [Nat.card_congr e.toEquiv,h]
    rcases hn with rfl | rfl <;> decide
  | sporadic name hne he =>
    obtain ⟨e⟩ := he
    apply (hsmall _).elim
    rw [Nat.card_congr e.toEquiv]
    cases name with
    | m11 => change 16 ∣ Nat.card Sporadic.Mathieu.M11; rw [Sporadic.Mathieu.m11_order]; decide
    | m12 => change 16 ∣ Nat.card Sporadic.Mathieu.M12; rw [Sporadic.Mathieu.m12_order]; decide
    | m22 => change 16 ∣ Nat.card Sporadic.Mathieu.M22; rw [Sporadic.Mathieu.m22_order]; decide
    | m23 => change 16 ∣ Nat.card Sporadic.Mathieu.M23; rw [Sporadic.Mathieu.m23_order]; decide
    | m24 => change 16 ∣ Nat.card Sporadic.Mathieu.M24; rw [Sporadic.Mathieu.m24_order]; decide
    | j2 => change 16 ∣ Nat.card Sporadic.LeechRelated.J2.Carrier
            rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
            decide
    | j3 => exact (hne rfl).elim
    | j4 => change 16 ∣ Nat.card Janko4.Model; rw [Janko4.Cardinality.model_card]; decide
    | hs => exact hs_sixteen
    | he => exact held_sixteen
    | ru => change 16 ∣ Nat.card Rudvalis.Model; rw [Rudvalis.model_card]; decide
  | janko_one he =>
    rw [Nat.card_congr he.some.toEquiv,Janko1.card_model] at hcard
    norm_num at hcard



/-- A full-Sylow local PSL₂(8) cannot enlarge inside an SQTK group whose
Sylow two-subgroups have order at most eight. -/
theorem containing_eq_of_eight_section
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (S : Sylow 2 G) (hS : Nat.card S ≤ 8)
    {B C : Subgroup G} (hB : B ∈ ChapterA.Section03.localCComponents S)
    (hC : C.IsCComponent) (hBC : B ≤ C)
    (eB : B ≃* Theory.PSL2.BinaryGroup 3) : B = C := by
  have hF : Nat.card (GaloisField 2 3) = 8 := by
    rw [GaloisField.card 2 3 (by decide)]; decide
  have hmodelB : ClassicalGroup.IsPSL B 2 (2^3) :=
    ⟨GaloisField 2 3,inferInstance,inferInstance,hF,⟨eB⟩⟩
  let : IsQuasisimple C := ChapterA.Section03.SourceEmbeddings.binary_containing_component_quasisimple
    hG hO hC hBC (by decide : 1 < 3) hmodelB
  let : IsSimpleGroup (Theory.PSL2.BinaryGroup 3) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hF]; decide)
  let : IsSimpleGroup B := eB.isSimpleGroup
  let : Group.IsPerfect B := by
    let := hB.perfect
    let e := subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup G) from le_sup_left)
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let q := QuotientGroup.mk' (solvableRadical C)
  let f := q.comp (inclusion hBC)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply (inferInstance : f.ker.Normal).eq_bot_or_eq_top.resolve_right
    intro ht
    let j : B →* solvableRadical C := (inclusion hBC).codRestrict _ (by
      intro b
      exact (QuotientGroup.eq_one_iff _).mp
        (show b ∈ f.ker from ht.symm ▸ mem_top b))
    have hj : Function.Injective j := fun x y he =>
      (inclusion_injective hBC) (congrArg Subtype.val he)
    exact Group.IsPerfect.not_isSolvable B
      (Group.isSolvable_of_isSolvable_injective (f := j) hj)
  have hQ := ChapterA.Section03.SourceComponents.GenerationCore.radical_quotient_sqtk
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X)) hG hC
  let : IsSimpleGroup (C ⧸ solvableRadical C) := hC.isSimpleGroup_quotient_solvableRadical
  have hna := hC.not_isMulCommutative_quotient_solvableRadical
  have hm := ChapterA.Section03.SourceComponents.sourceTheoremC_to_local hna
    (ChapterA.Section02.theoremC_knownSimple inferInstance hna hQ.stronglyQuasithin hQ.isKGroup)
  have hsmall : ¬ 16 ∣ Nat.card (C ⧸ solvableRadical C) := by
    intro hd
    have hh := S.pow_dvd_card_of_pow_dvd_card (n := 4)
      (hd.trans ((card_quotient_dvd_card _).trans C.card_subgroup_dvd_card))
    have hl := Nat.le_of_dvd (Nat.card_pos) hh
    omega
  have hcardB : Nat.card B = 504 := by
    rw [Nat.card_congr eB.toEquiv,
      ← Nat.card_congr (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).toEquiv,
      GorensteinWalter.sl2_card_formula,hF]
    norm_num
  have hdiv : 504 ∣ Nat.card (C ⧸ solvableRadical C) := by
    rw [←hcardB]
    exact card_dvd_of_injective f hf
  have hrB : 3 ≤ primeRank 2 B := by
    rw [primeRank_equiv 2 eB]
    exact Theory.PSL2.root_two_rank_ge (GaloisField 2 3) hF
  have hr := hrB.trans (_root_.primeRank_le_of_injective 2 f hf)
  have hmodel := bender_of_eight_section hm hsmall hdiv hr
  apply ChapterA.Section03.SourceEmbeddings.eq_of_solvable_sylow_overgroups S hB hC hBC
  apply SolvableSylowOvergroups.of_central_quotient q (QuotientGroup.mk'_surjective _)
  · rw [QuotientGroup.ker_mk']
    exact IsQuasisimple.solvableRadical_le_center
  · exact ChapterA.Section03.SourceEmbeddings.bender_solvable_proper_sylow_overgroup hmodel



end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.EightSylow
