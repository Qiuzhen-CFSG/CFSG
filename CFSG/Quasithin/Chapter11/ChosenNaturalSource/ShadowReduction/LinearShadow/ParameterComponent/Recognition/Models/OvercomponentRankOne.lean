module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.OvercomponentBender
public import Theory.SpecificGroups.PSL3.BorelTwoParabolics
public import Theory.SpecificGroups.SymplecticFour.Sylow

/-!
# The remaining Bender containing-model comparisons

Every Bender group has a unique maximal overgroup of a prescribed full
Sylow two-subgroup. The genuine point/line parabolics of PSL₃ and
point/plane parabolics of Sp₄ contradict this: both are proper, contain
the same full Sylow, and generate the whole group. This excludes all
Bender containing quotients for the linear-three and symplectic-four
seed rows, independently of the containing field exponent.

The preceding non-enlargement theorem identifies the actual local
components whenever the containing two-core quotient is Bender. Its
simplicity then makes the original star projection an isomorphism.
Divisibility by three separates every Suzuki quotient from PSU₃, and
the exact unitary two-rank identifies the field exponent in the remaining
unitary containing row. No generation parameter is substituted for a
model exponent.

The final theorem applies these comparisons to the original component
catalogue, preserving its actual Sylow, relative normality, star map,
maximal faithful overcomponent and chosen module. It does not exclude
the surviving Suzuki-in-Suzuki or unitary-in-unitary cases, or the
non-Bender containing models. Their FF exclusions, elementary full-root
lifting, recognition at n(H), and the paired/doubled assembly remain
with the parameter-component owner. The preceding-source discharge stays
with qt-d-1222-shadow-linear-geometry.

Source: Aschbacher--Smith, A.3.12, pp.47--48, F.1.3(1), pp.259--260,
and 11.3.5(1), pp.771--772 (combined manuscript, 1 March 2004).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models
open ChapterF.Source BenderSuzuki.MatrixGroups
variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
private theorem bender_simple (hm : ClassificationModels.IsBenderModel X) :
    IsSimpleGroup X := by
  cases hm with
  | linear f hf hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
      (hF ▸ Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hf)
    exact e.isSimpleGroup
  | unitary f hf hm =>
    obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
    have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 f
      (by omega) hF hconj
    let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
      BenderSuzuki.External.huppert_II_10_13 J (2 ^ f)
        ((by decide : 2 < 2 ^ 2).trans_le
          (Nat.pow_le_pow_right (by decide) hf)) hF hfixed
    exact e.isSimpleGroup
  | suzuki m hm he =>
    let : IsSimpleGroup (SuzukiMatrixGroup m) :=
      (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
    exact he.some.isSimpleGroup

private theorem bender_sylow_facts (hm : ClassificationModels.IsBenderModel X)
    (P : Sylow 2 X) : RankOneSylowFacts P := by
  cases hm with
  | linear f hf hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    exact rankOneSylowFacts_of_equiv P e (rankOneSylowFacts_psl2 F f (by omega) hF _)
  | unitary f hf hm =>
    obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
    exact rankOneSylowFacts_of_equiv P e (rankOneSylowFacts_psu3 J f (by omega) hF hconj _)
  | suzuki m _ he =>
    exact rankOneSylowFacts_of_equiv P he.some (suzuki_rankOneSylowFacts m _)

private theorem not_bender_of_parabolics (P : Sylow 2 X)
    (A B : Subgroup X) (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (hPA : (P : Subgroup X) ≤ A) (hPB : (P : Subgroup X) ≤ B)
    (hgen : A ⊔ B = ⊤) : ¬ ClassificationModels.IsBenderModel X := by
  intro hm
  have h := bender_sylow_facts hm P
  apply h.proper.ne
  apply top_unique
  rw [←hgen]
  exact sup_le (h.unique_maximal A hPA (lt_top_iff_ne_top.mpr hA))
    (h.unique_maximal B hPB (lt_top_iff_ne_top.mpr hB))

omit [Finite X] in
private theorem linear_three_not_bender {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL X 3 (2 ^ n)) :
    ¬ ClassificationModels.IsBenderModel X := by
  intro hb
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hb := hb.of_mulEquiv e.symm
  apply not_bender_of_parabolics (Matrix.PSL3.LinearThree.unipotentSylow F hn hF)
    (Matrix.PSL3.LinearThree.pointParabolic F) (Matrix.PSL3.LinearThree.lineParabolic F)
    (Matrix.PSL3.LinearThree.projective_parabolics_isCoatom F).1.ne_top
    (Matrix.PSL3.LinearThree.projective_parabolics_isCoatom F).2.ne_top
    _ _ (Matrix.PSL3.LinearThree.parabolics_sup_eq_top F) hb
  · exact (Matrix.PSL3.LinearThree.unipotent_le_borel F).trans
      ((Matrix.PSL3.LinearThree.projective_parabolics_inf F) ▸ inf_le_left)
  · exact (Matrix.PSL3.LinearThree.unipotent_le_borel F).trans
      ((Matrix.PSL3.LinearThree.projective_parabolics_inf F) ▸ inf_le_right)

omit [Finite X] in
private theorem symplectic_four_not_bender {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSp X 2 (2 ^ n)) :
    ¬ ClassificationModels.IsBenderModel X := by
  intro hb
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hb := hb.of_mulEquiv
    ((Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).trans e.symm)
  exact not_bender_of_parabolics (Theory.SpecificGroups.SymplecticFour.unipotentSylow hF hn)
    _ _ Theory.SpecificGroups.SymplecticFour.pointParabolic_ne_top
    Theory.SpecificGroups.SymplecticFour.planeParabolic_ne_top
    (Theory.SpecificGroups.SymplecticFour.unipotent_le_borel.trans inf_le_left)
    (Theory.SpecificGroups.SymplecticFour.unipotent_le_borel.trans inf_le_right)
    Theory.SpecificGroups.SymplecticFour.parabolics_sup_eq_top hb

omit [Finite X] in
private theorem unitary_three_dvd_card {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSU X 3 (2 ^ n)) : 3 ∣ Nat.card X := by
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hF hconj
  rw [Nat.card_congr e.toEquiv, Representation.SU3.BinaryDegree.card_projective J hF hfixed]
  let q := 2 ^ n
  have hnon : ¬ 3 ∣ q := fun hd =>
    (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  have hrem : q % 3 = 1 ∨ q % 3 = 2 := by
    have hr := Nat.mod_lt q (by decide : 0 < 3)
    have hn := Nat.dvd_iff_mod_eq_zero.not.mp hnon
    omega
  have hs : 3 ∣ q ^ 2 - 1 := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    have hsq : q ^ 2 % 3 = 1 := by
      rcases hrem with h | h <;> rw [Nat.pow_mod,h]
    omega
  have hg : Nat.gcd 3 (q + 1) = 1 ∨ Nat.gcd 3 (q + 1) = 3 :=
    (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 (q + 1))
  change 3 ∣ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1)
  rcases hg with hg | hg
  · rw [hg,Nat.div_one]
    exact dvd_mul_of_dvd_right hs _
  · have hd : 3 ∣ q + 1 := hg ▸ Nat.gcd_dvd_right 3 (q + 1)
    have hr : q % 3 = 2 := by
      have hr := Nat.dvd_iff_mod_eq_zero.mp hd
      rw [Nat.add_mod] at hr
      omega
    have hc : 3 ∣ q ^ 3 + 1 := by
      apply Nat.dvd_iff_mod_eq_zero.mpr
      rw [Nat.add_mod,Nat.pow_mod,hr]
    rw [hg,Nat.mul_div_assoc _ hs]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hc _) _

private theorem unitary_three_two_rank {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSU X 3 (2 ^ n)) : primeRank 2 X = n := by
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
  rw [primeRank_equiv 2 e]
  exact HermitianForm.EvenTwoRank.two_rank J hn hF hconj

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K J : Subgroup G}

/-- A Bender model on the seed's own two-core quotient descends unchanged
through every nontrivial original star projection. -/
theorem ComponentSeed.bender_star_model_of_bender_model (s : ComponentSeed T H K)
    (R : Subgroup H) [R.Normal] (hR : pCore 2 H ≤ R)
    [Nontrivial ((K.subgroupOf H).map (QuotientGroup.mk' R))]
    (hm : ClassificationModels.IsBenderModel (K ⧸ pCore 2 K)) :
    ClassificationModels.IsBenderModel ((K.subgroupOf H).map (QuotientGroup.mk' R)) := by
  let B := K.subgroupOf H
  have hmodel := hm.of_mulEquiv s.intrinsicQuotientEquiv.symm
  let : IsSimpleGroup (B ⧸ pCore 2 B) := Models.bender_simple hmodel
  let q := Models.starProjection B R s.component.2 hR
  have hq := Models.starProjection_surjective B R s.component.2 hR
  let e := MulEquiv.ofBijective q ⟨q.injective_of_surjective_of_simple hq,hq⟩
  exact hmodel.of_mulEquiv e.symm

/-- The two genuine parabolics of a linear-three or symplectic-four star
image exclude every Bender containing quotient, at every field degree. -/
theorem ComponentSeed.not_bender_overcomponent_of_rank_two_image
    (s : ComponentSeed T H K) (h : Hypothesis1131At D S U₁ H)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : K ≤ J)
    (R : Subgroup H) [R.Normal] (hR : pCore 2 H ≤ R)
    [Nontrivial ((K.subgroupOf H).map (QuotientGroup.mk' R))]
    {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL ((K.subgroupOf H).map (QuotientGroup.mk' R)) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSp ((K.subgroupOf H).map (QuotientGroup.mk' R)) 2 (2 ^ n)) :
    ¬ ClassificationModels.IsBenderModel (J ⧸ pCore 2 J) := by
  intro hb
  have he := s.eq_overcomponent_of_bender_twoCore h hJ hKJ hb
  have hbK : ClassificationModels.IsBenderModel (K ⧸ pCore 2 K) := he.symm ▸ hb
  have hbI := s.bender_star_model_of_bender_model R hR hbK
  rcases hm with hm | hm
  · exact Models.linear_three_not_bender hn hm hbI
  · exact Models.symplectic_four_not_bender hn hm hbI

/-- A Suzuki seed cannot have a unitary-three containing quotient.
The field exponents are independent; divisibility by three separates them. -/
theorem ComponentSeed.not_unitary_overcomponent_of_suzuki
    (s : ComponentSeed T H K) (h : Hypothesis1131At D S U₁ H)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : K ≤ J)
    {m : ℕ} (hm : 1 ≤ m)
    (he : Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    ∀ f : ℕ, 2 ≤ f → ¬ ClassicalGroup.IsPSU (J ⧸ pCore 2 J) 3 (2 ^ f) := by
  intro f hf huni
  have hsame := s.eq_overcomponent_of_bender_twoCore h hJ hKJ (.unitary f hf huni)
  have hd := Models.unitary_three_dvd_card (by omega : 0 < f) huni
  rw [←hsame,Nat.card_congr he.some.toEquiv] at hd
  exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega) hd

/-- A higher-rank star image excludes all Suzuki containing quotients.
The unitary case uses the actual quotient map, so no central-cover
identification is assumed. -/
theorem ComponentSeed.not_suzuki_overcomponent_of_higher_rank_image
    (s : ComponentSeed T H K) (h : Hypothesis1131At D S U₁ H)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : K ≤ J)
    (R : Subgroup H) [R.Normal] (hR : pCore 2 H ≤ R)
    [Nontrivial ((K.subgroupOf H).map (QuotientGroup.mk' R))]
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSU ((K.subgroupOf H).map (QuotientGroup.mk' R)) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSL ((K.subgroupOf H).map (QuotientGroup.mk' R)) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSp ((K.subgroupOf H).map (QuotientGroup.mk' R)) 2 (2 ^ n)) :
    ∀ m : ℕ, 1 ≤ m → ¬ Nonempty
      ((J ⧸ pCore 2 J) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  intro m hmpos he
  have hsame := s.eq_overcomponent_of_bender_twoCore h hJ hKJ (.suzuki m hmpos he)
  rcases hm with huni | htwo
  · let B := K.subgroupOf H
    let q := Models.starProjection B R s.component.2 hR
    have hd := (Models.unitary_three_dvd_card (by omega : 0 < n) huni).trans
      (card_dvd_of_surjective q (Models.starProjection_surjective B R s.component.2 hR))
    rw [←Nat.card_congr s.intrinsicQuotientEquiv.toEquiv,hsame,
      Nat.card_congr he.some.toEquiv] at hd
    exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega) hd
  · exact s.not_bender_overcomponent_of_rank_two_image h hJ hKJ R hR
      (by omega) htwo (.suzuki m hmpos he)

/-- In the unitary seed row, a Bender overcomponent is the same component
and has the seed's actual field exponent. This does not identify that
exponent with the generation minimum. -/
theorem ComponentSeed.unitary_overcomponent_of_bender
    (s : ComponentSeed T H K) (h : Hypothesis1131At D S U₁ H)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : K ≤ J)
    (R : Subgroup H) [R.Normal] (hR : pCore 2 H ≤ R)
    [Nontrivial ((K.subgroupOf H).map (QuotientGroup.mk' R))]
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSU ((K.subgroupOf H).map (QuotientGroup.mk' R)) 3 (2 ^ n))
    (hb : ClassificationModels.IsBenderModel (J ⧸ pCore 2 J)) :
    K = J ∧ ClassicalGroup.IsPSU (J ⧸ pCore 2 J) 3 (2 ^ n) := by
  have hsame := s.eq_overcomponent_of_bender_twoCore h hJ hKJ hb
  refine ⟨hsame,?_⟩
  cases hb with
  | linear f hf hlin =>
    exact (s.not_linear_overcomponent_of_higher_rank_image h hJ hKJ R hR hn
      (.inl hm) f hf hlin).elim
  | suzuki m hmpos he =>
    exact (s.not_suzuki_overcomponent_of_higher_rank_image h hJ hKJ R hR hn
      (.inl hm) m hmpos he).elim
  | unitary f hf huni =>
    have huniK : ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 (2 ^ f) := hsame.symm ▸ huni
    let B := K.subgroupOf H
    have hmodel := huniK.of_mulEquiv s.intrinsicQuotientEquiv.symm
    let : IsSimpleGroup (B ⧸ pCore 2 B) := Models.bender_simple (.unitary f hf hmodel)
    let q := Models.starProjection B R s.component.2 hR
    have hq := Models.starProjection_surjective B R s.component.2 hR
    let e := MulEquiv.ofBijective q ⟨q.injective_of_surjective_of_simple hq,hq⟩
    have hstar := hmodel.of_mulEquiv e.symm
    have heq : n = f := (Models.unitary_three_two_rank (by omega) hm).symm.trans
      (Models.unitary_three_two_rank (by omega) hstar)
    rwa [←heq] at huni

/-- The original catalogue with the Bender containing-model comparisons
discharged. The rank-two rows admit no Bender overcomponent; a unitary
row can only retain itself at the same literal field exponent; a Suzuki
row excludes both linear and unitary containing quotients. -/
theorem exists_componentSeed_with_bender_overcomponent_sieve
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary) :
    let P := T.subtype h.outside.1.1.2
    let hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
    ∃ K J : Subgroup G, ComponentSeed T H K ∧ K ≤ J ∧
      J ∈ Chapter1.LStar G (T : Subgroup G) ∧
      J ∈ MainForward.faithfulLocalComponents T ∧
      ¬ J ≤ normalizer (L : Set G) ∧ ⁅sourceZ T,J⁆ ≠ ⊥ ∧
      (((∃ f : ℕ, 2 ≤ f ∧ ChapterE.generationParameter H ≤ f ∧
          ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) ∧
          solvableRadical H = pCore 2 H) ∨
        (Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
          (∀ f : ℕ, 2 ≤ f → ¬ ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 2 (2 ^ f)) ∧
          (((∃ m : ℕ, 1 ≤ m ∧ ChapterE.generationParameter H ≤ 2 * m + 1 ∧
              Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ∧
              solvableRadical H = pCore 2 H ∧
              (∀ f : ℕ, 2 ≤ f → ¬ ClassicalGroup.IsPSU (J ⧸ pCore 2 J) 3 (2 ^ f))) ∨
            ((K.subgroupOf H).Normal ∧ (T : Subgroup G) ≤ normalizer (J : Set G) ∧
              (∃ W : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T J W)) ∧
              (let I := (K.subgroupOf H).map (QuotientGroup.mk' (ChapterB.minimalParabolicCore P hP))
               ∃ f : ℕ, 2 ≤ f ∧ ChapterE.generationParameter H ≤ f ∧
                 ((ClassicalGroup.IsPSU I 3 (2 ^ f) ∧
                    (∀ m : ℕ, 1 ≤ m → ¬ Nonempty
                      ((J ⧸ pCore 2 J) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ∧
                    (ClassificationModels.IsBenderModel (J ⧸ pCore 2 J) →
                      K = J ∧ ClassicalGroup.IsPSU (J ⧸ pCore 2 J) 3 (2 ^ f))) ∨
                  ((ClassicalGroup.IsPSL I 3 (2 ^ f) ∨ ClassicalGroup.IsPSp I 2 (2 ^ f)) ∧
                    ¬ ClassificationModels.IsBenderModel (J ⧸ pCore 2 J)))))))) := by
  obtain ⟨K,J,s,hKJ,hJ,hfaith,ho,hm,hcases⟩ :=
    exists_componentSeed_with_non_linear_overcomponent_models h pr hc hs
  refine ⟨K,J,s,hKJ,hJ,hfaith,ho,hm,?_⟩
  rcases hcases with hlin | ⟨hsource,hnlin,hcases⟩
  · exact .inl hlin
  refine .inr ⟨hsource,hnlin,?_⟩
  rcases hcases with ⟨⟨m,hm,hbound,he⟩,hrad⟩ | ⟨hn,hTJ,hchosen,n,hnn,hbound,hmodels⟩
  · exact .inl ⟨⟨m,hm,hbound,he⟩,hrad,s.not_unitary_overcomponent_of_suzuki h hJ.1 hKJ hm he⟩
  · let P := T.subtype h.outside.1.1.2
    let hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
    let R := ChapterB.minimalParabolicCore P hP
    let : IsSimpleGroup ((K.subgroupOf H).map (QuotientGroup.mk' R)) :=
      (ChapterE.Structure.source_component_simple_image P hP
        (counterexample_not_solvable h pr hc hs) (K.subgroupOf H) s.component.2
        (s.intrinsic_supplement h.outside.1.1.2)).1
    have hR := ChapterB.minimalParabolicTwoCore_le_core P hP
    refine .inr ⟨hn,hTJ,hchosen,n,hnn,hbound,?_⟩
    rcases hmodels with huni | htwo
    · exact .inl ⟨huni,
        s.not_suzuki_overcomponent_of_higher_rank_image h hJ.1 hKJ R hR hnn (.inl huni),
        s.unitary_overcomponent_of_bender h hJ.1 hKJ R hR hnn huni⟩
    · exact .inr ⟨htwo,s.not_bender_overcomponent_of_rank_two_image h hJ.1 hKJ R hR
        (by omega) htwo⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
