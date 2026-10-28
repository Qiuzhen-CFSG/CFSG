module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.SolvableContaining
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.RankTwoCubic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SmallAlternating
public import Theory.SpecificGroups.Tits.SolvableSylowOvergroups
public import Theory.SpecificGroups.G2Even.BinaryDerivedSolvableOvergroups
public import Theory.Representation.SU3.BinaryDegree.ProjectiveOrder

/-!
# Small containing quotients and binary rank-one containing models

The literal full-Sylow overgroup calculations force equality of each original
factor with a containing component whose quotient is one of the small models.
The original quotient consequently inherits a cubic divisor, and the proved
three-divisor contradiction excludes the actual pair. Both distinctness and
the divisor premise are discharged here. The binary PSL₃ application includes
q = 2 and combines with the established larger-field argument.

The applications cover binary PSL₂ and PSU₃, A₅ and A₆, perfect central
covers of A₆, the commutator of PSp₄(2), G₂(2)′, and the Tits group. The
unitary cubic is supplied by the order formula in even fixed-field degree
and by the actual cubic rank witness in odd degree. When both containing
quotients are Bender models, equality on both factors contradicts strictness;
this includes Suzuki without assuming its order is divisible by three.

All applications retain the original two factors, half-join and exchanger.
The remaining containing models, three-free enlargement, zero-kernel
binary-three normalizer and final assembly remain with
qt-d-10-nona5-half-sylow-unique. ModuleChoiceAt is supplied independently by
qt-d-10-nona5-point-selection; qt-d-10-nona5-point-control retains its ultimate
discharge. The unconditional source uniqueness theorem is still outstanding.
Source: Aschbacher--Smith A.3.12 and 10.2.6, printed pp.47--48,748--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}

/-- Apply the quotient calculation on either member of the original ordered pair. -/
theorem ContainingPair.impossible_of_solvable_sylow_cubic_model
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {X : Type*} [Group X] (hsol : SolvableSylowOvergroups X) (h3 : 3 ∣ Nat.card X)
    (he : Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* X) ∨ Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* X)) :
    False := by
  rcases he with he | he
  all_goals obtain ⟨e⟩ := he
  · exact C.impossible_of_first_solvable_sylow_cubic_quotient hchoice hmany hn hna
      (SolvableSylowOvergroups.of_equiv e hsol) ((Nat.card_congr e.toEquiv).symm ▸ h3)
  · exact C.impossible_of_second_solvable_sylow_cubic_quotient hchoice hmany hn hna
      (SolvableSylowOvergroups.of_equiv e hsol) ((Nat.card_congr e.toEquiv).symm ▸ h3)

/-- The q = 2 endpoint uses the actual projective binary-three quotient. -/
theorem ContainingPair.impossible_of_binary_three_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    (he : Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* PSL(3,F)) ∨
      Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* PSL(3,F))) : False := by
  apply C.impossible_of_solvable_sylow_cubic_model hchoice hmany hn hna
    (Matrix.PSL3Two.solvableSylowOvergroups_projective_of_card_two hF) _ he
  exact (Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
    (F := F) (i := (0 : Fin 3)) (j := 1) (by decide)).trans (card_subgroup_dvd_card _)

/-- Every binary PSL₃ containing quotient is excluded, including the two-element field. -/
theorem ContainingPair.impossible_of_binary_linear_three_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {n : ℕ} (hnn : 1 ≤ n)
    (he : ClassicalGroup.IsPSL (K₁ ⧸ pCore 2 K₁) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSL (K₂ ⧸ pCore 2 K₂) 3 (2 ^ n)) : False := by
  rcases he with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
  all_goals
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
  · by_cases hn1 : n = 1
    · exact C.impossible_of_binary_three_quotient hchoice hmany hn hna
        (by simpa only [hn1,pow_one] using hF) (Or.inl ⟨e⟩)
    · exact C.impossible_of_first_linear_three_quotient hchoice hmany hn hna (by omega) hF e
  · by_cases hn1 : n = 1
    · exact C.impossible_of_binary_three_quotient hchoice hmany hn hna
        (by simpa only [hn1,pow_one] using hF) (Or.inr ⟨e⟩)
    · exact C.impossible_of_second_linear_three_quotient hchoice hmany hn hna (by omega) hF e

/-- The actual A₅ and A₆ quotients supply both missing premises of pair exclusion. -/
theorem ContainingPair.impossible_of_small_alternating_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {n : ℕ} (hnn : n = 5 ∨ n = 6)
    (he : Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* alternatingGroup (Fin n)) ∨
      Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* alternatingGroup (Fin n))) : False := by
  apply C.impossible_of_solvable_sylow_cubic_model hchoice hmany hn hna _ _ he
  · rcases hnn with rfl | rfl
    · exact fun _ P _ hP => alternatingGroup.isSolvable_subgroup_five_of_ne_top P hP
    · exact AlternatingSix.ProperSylowOvergroups.isSolvable
  · rcases hnn with rfl | rfl <;> rw [nat_card_alternatingGroup] <;> norm_num [Nat.factorial]

/-- Use the actual commutator of the binary projective symplectic group, which is A₆. -/
theorem ContainingPair.impossible_of_binary_symplectic_derived_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (he : Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* commutator (Theory.SpecificGroups.SymplecticFour.Sp (ZMod 2) ⧸ center (Theory.SpecificGroups.SymplecticFour.Sp (ZMod 2)))) ∨
      Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* commutator (Theory.SpecificGroups.SymplecticFour.Sp (ZMod 2) ⧸ center (Theory.SpecificGroups.SymplecticFour.Sp (ZMod 2))))) :
    False := by
  apply C.impossible_of_small_alternating_quotient hchoice hmany hn hna (Or.inr rfl)
  rcases he with he | he
  all_goals obtain ⟨e⟩ := he
  · exact Or.inl ⟨e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix⟩
  · exact Or.inr ⟨e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix⟩

/-- The actual G₂(2)′ carrier has solvable proper full-Sylow overgroups and a cubic divisor. -/
theorem ContainingPair.impossible_of_binary_g2_derived_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (he : Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* commutator (Atlas.G2.Model (ZMod 2))) ∨
      Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* commutator (Atlas.G2.Model (ZMod 2)))) : False := by
  apply C.impossible_of_solvable_sylow_cubic_model hchoice hmany hn hna
    Atlas.G2.binaryDerived_solvableSylowOvergroups _ he
  rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
  norm_num

/-- The Tits quotient is excluded on either original containing component. -/
theorem ContainingPair.impossible_of_tits_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (he : Nonempty ((K₁ ⧸ pCore 2 K₁) ≃* Tits.ParrottGroup) ∨
      Nonempty ((K₂ ⧸ pCore 2 K₂) ≃* Tits.ParrottGroup)) : False := by
  apply C.impossible_of_solvable_sylow_cubic_model hchoice hmany hn hna
    Tits.ProperSylowOvergroups.solvableSylowOvergroups _ he
  rw [Nat.card_congr Tits.parrottFiniteImageEquiv.toEquiv]
  by_contra hd
  have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hd
  have hr := Tits.ThreeRank.rank_two_le
  omega

/-- Both Bender containing quotients force equality, including the three-free Suzuki row. -/
theorem ContainingPair.impossible_of_bender_quotients
    (C : ContainingPair D H t K₁ K₂)
    (hfirst : ClassificationModels.IsBenderModel (K₁ ⧸ pCore 2 K₁))
    (hsecond : ClassificationModels.IsBenderModel (K₂ ⧸ pCore 2 K₂)) : False :=
  C.impossible_of_solvable_sylow_quotients
    (ChapterA.Section03.SourceEmbeddings.bender_solvable_proper_sylow_overgroup hfirst)
    (ChapterA.Section03.SourceEmbeddings.bender_solvable_proper_sylow_overgroup hsecond)

private theorem cubic_binary_unitary {F : Type*} [Field F] [Finite F]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F) {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hc : ∀ x, J.conj x = x ^ (2 ^ n)) :
    3 ∣ Nat.card (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  by_cases he : Even n
  · have hmod : 2 ^ n % 3 = 1 := by
      rw [Nat.BinaryTorusParity.two_pow_mod_three,if_pos (Nat.even_iff.mp he)]
    have hgcd : Nat.gcd 3 (2 ^ n + 1) = 1 := by
      rw [Nat.gcd_rec,show (2 ^ n + 1) % 3 = 2 by omega]
      decide
    rw [Representation.SU3.BinaryDegree.card_projective J hF
      (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hF hc),hgcd,Nat.div_one]
    apply dvd_mul_of_dvd_right
    apply Nat.dvd_of_mod_eq_zero
    have hm : (2 ^ n) ^ 2 % 3 = 1 := by simp [Nat.pow_mod,hmod]
    have hp : 0 < (2 ^ n) ^ 2 := pow_pos (pow_pos (by decide) _) _
    omega
  · have hr := Theory.SpecificGroups.SignedThreeCubicRank.unitary_projective
      J hn hF hc (Nat.not_even_iff_odd.mp he)
    by_contra hd
    have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hd
    omega

private theorem nonsuzuki_bender_cubic {X : Type*} [Group X] [Finite X]
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL X 2 (2 ^ n) ∨ ClassicalGroup.IsPSU X 3 (2 ^ n)) :
    SolvableSylowOvergroups X ∧ 3 ∣ Nat.card X := by
  refine ⟨ChapterA.Section03.SourceEmbeddings.bender_solvable_proper_sylow_overgroup
    (hm.elim (ClassificationModels.IsBenderModel.linear n hn)
      (ClassificationModels.IsBenderModel.unitary n hn)),?_⟩
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,J,hF,hc,⟨e⟩⟩
  · let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    rw [Nat.card_congr e.toEquiv]
    exact (Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
      (F := F) (i := (0 : Fin 2)) (j := 1) (by decide)).trans (card_subgroup_dvd_card _)
  · rw [Nat.card_congr e.toEquiv]
    exact cubic_binary_unitary J (by omega) hF hc

/-- Either binary PSL₂ or PSU₃ containing quotient gives the complete pair contradiction. -/
theorem ContainingPair.impossible_of_nonsuzuki_bender_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    {n : ℕ} (hnn : 2 ≤ n)
    (he : (ClassicalGroup.IsPSL (K₁ ⧸ pCore 2 K₁) 2 (2 ^ n) ∨
      ClassicalGroup.IsPSU (K₁ ⧸ pCore 2 K₁) 3 (2 ^ n)) ∨
      (ClassicalGroup.IsPSL (K₂ ⧸ pCore 2 K₂) 2 (2 ^ n) ∨
      ClassicalGroup.IsPSU (K₂ ⧸ pCore 2 K₂) 3 (2 ^ n))) : False := by
  rcases he with he | he
  · obtain ⟨hs,h3⟩ := nonsuzuki_bender_cubic hnn he
    exact C.impossible_of_first_solvable_sylow_cubic_quotient hchoice hmany hn hna hs h3
  · obtain ⟨hs,h3⟩ := nonsuzuki_bender_cubic hnn he
    exact C.impossible_of_second_solvable_sylow_cubic_quotient hchoice hmany hn hna hs h3

/-- Perfect central covers of A₆ are excluded on either original pair member.
The central-cover property and the actual center quotient both come from the model. -/
theorem ContainingPair.impossible_of_central_six_quotient
    (C : ContainingPair D H t K₁ K₂)
    (hchoice : Selection.ModuleChoiceAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (he : Section02.LocalModels.IsAlternatingCover (K₁ ⧸ pCore 2 K₁) 6 ∨
      Section02.LocalModels.IsAlternatingCover (K₂ ⧸ pCore 2 K₂) 6) : False := by
  have data {X : Type u} [Group X] [Finite X]
      (hm : Section02.LocalModels.IsAlternatingCover X 6) :
      SolvableSylowOvergroups X ∧ 3 ∣ Nat.card X := by
    obtain ⟨hq,_,⟨e⟩⟩ := hm
    let := hq
    refine ⟨SolvableSylowOvergroups.of_central_quotient (QuotientGroup.mk' (center X))
      (QuotientGroup.mk'_surjective _) (by simp)
      (SolvableSylowOvergroups.of_equiv e AlternatingSix.ProperSylowOvergroups.isSolvable),?_⟩
    have hd : 3 ∣ Nat.card (X ⧸ center X) := by
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    exact hd.trans (card_quotient_dvd_card _)
  rcases he with he | he
  · obtain ⟨hs,h3⟩ := data he
    exact C.impossible_of_first_solvable_sylow_cubic_quotient hchoice hmany hn hna hs h3
  · obtain ⟨hs,h3⟩ := data he
    exact C.impossible_of_second_solvable_sylow_cubic_quotient hchoice hmany hn hna hs h3

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
