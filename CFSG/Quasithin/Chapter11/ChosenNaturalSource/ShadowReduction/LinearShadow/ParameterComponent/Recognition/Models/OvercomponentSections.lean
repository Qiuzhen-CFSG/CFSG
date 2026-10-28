module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.OvercomponentRanks
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.TwoRank
public import CFSG.Quasithin.ChapterA.Section01.RankActions.PerfectActions.LinearRecognition
public import Theory.GroupTheory.CComponent.SimpleImageKernel
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.SpecificGroups.PSL2.PrimeFieldTwoRank
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.SpecificGroups.SU3.EvenTwoRank
public import Theory.SpecificGroups.Suzuki.TwoRank
public import Theory.Representation.SU3.BinaryDegree.ProjectiveOrder
public import Theory.SpecificGroups.SL2.OddOrderDivisibility

/-!
# Simple sections force quasisimple containing quotients

Suppose a local overcomponent J has nonquasisimple quotient J/O₂(J).
The noncentral-Fitting theorem identifies its Fitting quotient with SL₂(p)
for a prime p > 3. The original C-component K maps to this group with
solvable kernel. Perfect-subgroup recognition and radical-quotient transport
then identify every simple quotient of K with PSL₂(r) for a prime r > 3.

This contradicts two-rank at least three in a linear-three, sufficiently
large unitary-three, or Suzuki simple image. The remaining PSU₃(4) image
has order 62400, which differs from every prime-field PSL₂ order. Thus
both signed-three field parities and Suzuki supply the same actual
quasisimple containing quotient. In the normal higher-rank rows this
completes the hypotheses of the previously constructed chosen module.

The final theorem applies the obstruction to the original catalogue,
constructing the unitary simple-image premise from the literal minimal-
parabolic projection. It preserves the original seed, overcomponent,
relative normality, model exponent, and generation-parameter bound.
Together with the cubic-rank symplectic result, all non-PSL₂ rows now
supply the 12.2.3 source hypotheses on their actual maximal overcomponent.

Embedding/FF exclusions, elementary full-root lifting, recognition at
n(H), and the paired/doubled-SL₃ assembly remain necessary for 11.3.5--6.
No such conclusion is assumed or asserted here. The preceding-source
inputs retain their final discharge with qt-d-1222-shadow-linear-geometry.
Source: Aschbacher--Smith, 11.3.5(1), pp.771--772; A.1.29(1), p.27;
A.3.3 and A.3.6, pp.42--45 (combined manuscript, 1 March 2004).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models

private theorem prime_linear_simple_image {A I : Type*} [Group A] [Finite A]
    [Group I] [Finite I] [IsSimpleGroup I]
    (hA : (⊤ : Subgroup A).IsCComponent)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (f : A →* SL(2,ZMod p)) [Group.IsSolvable f.ker]
    (g : A →* I) (hg : Function.Surjective g) :
    ∃ r : ℕ, r.Prime ∧ 3 < r ∧ Nonempty (I ≃* PSL(2,ZMod r)) := by
  let : Group.IsPerfect A := Group.IsPerfect.top_iff.mp hA.perfect
  let : Group.IsPerfect f.range := Group.IsPerfect.ofSurjective f.rangeRestrict_surjective
  let : Nontrivial f.range := by
    by_contra hn
    have hsub : Subsingleton f.range := not_nontrivial_iff_subsingleton.mp hn
    let := hsub
    let : Group.IsSolvable f.range := Group.isSolvable_of_comm (fun a b => Subsingleton.elim _ _)
    let : Group.IsSolvable A := Group.isSolvable_of_ker_le_range f.ker.subtype
      f.rangeRestrict (by simp)
    exact hA.not_isSolvable inferInstance
  let : Group.IsSolvable f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    infer_instance
  let a : A ⧸ solvableRadical A ≃* I :=
    (QuotientGroup.quotientMulEquivOfEq
      (kernel_eq_solvableRadical_of_top_isCComponent hA g hg).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg)
  let b := solvableRadicalQuotientEquiv f.rangeRestrict f.rangeRestrict_surjective
  have step {r : ℕ} [Fact r.Prime] (hr : 3 < r)
      (e : f.range ≃* SL(2,ZMod r)) : Nonempty (I ≃* PSL(2,ZMod r)) :=
    ⟨a.symm.trans (b.trans
      (Theory.SpecificGroups.SL2.ResidualTwoExtension.radicalQuotientEquiv
        (by simpa using hr) e))⟩
  rcases ChapterA.RankActions.primePerfectSL2Recognition p hp f.range
      inferInstance inferInstance with hfull | hsmall
  · obtain ⟨e⟩ := hfull
    exact ⟨p,Fact.out,hp,step hp e⟩
  · obtain ⟨_,⟨e⟩⟩ := hsmall
    exact ⟨5,by decide,by decide,step (by decide) e⟩

private theorem nonquasisimple_simple_section
    {X A I : Type*} [Group X] [Finite X] [Group A] [Finite A]
    [Group I] [Finite I] [IsSimpleGroup I] {κ : GroupClass}
    (hX : IsSQTK κ X) (hO : pCore 2 X = ⊥)
    (hC : (⊤ : Subgroup X).IsCComponent) (hn : ¬ IsQuasisimple X)
    (hA : (⊤ : Subgroup A).IsCComponent)
    (i : A →* X) [Group.IsSolvable i.ker]
    (g : A →* I) (hg : Function.Surjective g) :
    ∃ r : ℕ, r.Prime ∧ 3 < r ∧ Nonempty (I ≃* PSL(2,ZMod r)) := by
  have hfit : ¬ fittingSubgroup (⊤ : Subgroup X) ≤ center (⊤ : Subgroup X) := by
    intro hc
    let : Group.IsSolvable (center (⊤ : Subgroup X)) :=
      Group.isSolvable_of_comm (fun a b =>
        Subtype.ext (mem_center_iff.mp a.property b).symm)
    have hr : solvableRadical (⊤ : Subgroup X) = center (⊤ : Subgroup X) :=
      le_antisymm (solvableRadical_le_center_of_fitting_le_center hc)
        (le_solvableRadical _ inferInstance inferInstance)
    let := hC.perfect
    let := hC.isSimpleGroup_quotient_solvableRadical
    let : IsQuasisimple (⊤ : Subgroup X) :=
      ⟨(QuotientGroup.quotientMulEquivOfEq hr).symm.isSimpleGroup⟩
    exact hn (IsQuasisimple.of_mulEquiv topEquiv)
  obtain ⟨r,hr,hr3,⟨e⟩⟩ :=
    ChapterA.Section03.NoncentralFitting.primeSL2FittingQuotient_of_noncentral
      ChapterA.RankActions.primeSL2CoverRigidity hX hO hC hfit
  let : Fact r.Prime := ⟨hr⟩
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (fittingSubgroup (⊤ : Subgroup X)))
  let j := (topEquiv (G := X)).symm.toMonoidHom.comp i
  let : Group.IsSolvable j.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ (topEquiv (G := X)).symm.injective]
    infer_instance
  let : Group.IsSolvable q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    infer_instance
  let : Group.IsSolvable (q.comp j).ker := by
    change Group.IsSolvable (q.ker.comap j)
    exact isSolvable_comap_of_solvable_ker j q.ker
  exact prime_linear_simple_image hA hr3 (q.comp j) g hg

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Models
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K J : Subgroup G}

/-- A simple quotient of the original seed rules out a nonquasisimple
containing head unless that same quotient is prime-field PSL₂. -/
theorem ComponentSeed.overcomponent_quasisimple_of_simple_quotient
    (s : ComponentSeed T H K) (S : D.NonbinaryNaturalInput)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : K ≤ J)
    {I : Type*} [Group I] [Finite I] [IsSimpleGroup I]
    (g : K →* I) (hg : Function.Surjective g)
    (hexclude : ∀ r : ℕ, r.Prime → 3 < r → ¬ Nonempty (I ≃* PSL(2,ZMod r))) :
    IsQuasisimple (J ⧸ pCore 2 J) := by
  have hlocal := (Chapter1.Section02.Adequate.mem_L_iff_mainForward T J).mp hJ
  obtain ⟨_,_,_,_,hsq⟩ := MainForward.localComponents_local_setup
    S.source.simpleQTKE T hlocal
  let j := inclusion (show J ≤ J ⊔ (T : Subgroup G) from le_sup_left)
  have hsqJ : IsSQTK KnownSimple.IsKnownSimple J :=
    ⟨hsq.stronglyQuasithin.of_injective j (inclusion_injective le_sup_left),
      hsq.isKGroup.of_injective j (inclusion_injective le_sup_left)⟩
  have htop : (⊤ : Subgroup J).IsCComponent := by
    simpa only [subgroupOf_self] using hJ.1.subgroupOf_of_le le_rfl le_sup_left
  let X := J ⧸ pCore 2 J
  let q := QuotientGroup.mk' (pCore 2 J)
  let : Group.IsNilpotent (pCore 2 J) := pCore_isPGroup.isNilpotent
  have htopX : (⊤ : Subgroup X).IsCComponent := by
    have hh := htop.map_quotient (pCore 2 J)
    rw [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let k := inclusion hKJ
  let i := q.comp k
  let : Group.IsSolvable k.ker := by
    rw [k.ker_eq_bot (inclusion_injective hKJ)]
    infer_instance
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  let : Group.IsSolvable i.ker := by
    change Group.IsSolvable (q.ker.comap k)
    exact isSolvable_comap_of_solvable_ker k q.ker
  have hKtop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using s.component.2.subgroupOf_of_le le_rfl s.component.1
  by_contra hn
  obtain ⟨r,hr,hr3,he⟩ := Models.nonquasisimple_simple_section
    (ChapterE.Structure.sqtk_two_quotient hsqJ (pCore 2 J) pCore_isPGroup)
    (pCore_quotient_pCore_eq_bot 2) htopX hn hKtop i g hg
  exact hexclude r hr hr3 he

/-- Two-rank greater than two in a simple quotient is an obstruction to
all the prime-field sections in the noncentral-Fitting alternatives. -/
theorem ComponentSeed.overcomponent_quasisimple_of_simple_quotient_two_rank
    (s : ComponentSeed T H K) (S : D.NonbinaryNaturalInput)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : K ≤ J)
    {I : Type*} [Group I] [Finite I] [IsSimpleGroup I]
    (g : K →* I) (hg : Function.Surjective g) (hrank : 3 ≤ primeRank 2 I) :
    IsQuasisimple (J ⧸ pCore 2 J) := by
  apply s.overcomponent_quasisimple_of_simple_quotient S hJ hKJ g hg
  intro r hr hr3 he
  let : Fact r.Prime := ⟨hr⟩
  obtain ⟨e⟩ := he
  rw [primeRank_equiv 2 e,Theory.PSL2.primeField_two_rank hr3] at hrank
  omega

/-- Every nonbinary linear-three star image, of either field parity,
constructs the same full chosen-overcomponent setup. -/
theorem ComponentSeed.chosen_overcomponent_of_linear_image
    (s : ComponentSeed T H K) (h : Hypothesis1131At D S U₁ H)
    (hn : (K.subgroupOf H).Normal)
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : K ≤ J)
    (R : Subgroup H) [R.Normal] {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL ((K.subgroupOf H).map (QuotientGroup.mk' R)) 3 (2 ^ f)) :
    Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
      (T : Subgroup G) ≤ normalizer (J : Set G) ∧
      ∃ W : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T J W) := by
  let I := (K.subgroupOf H).map (QuotientGroup.mk' R)
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hm
  let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup I := e.isSimpleGroup
  let a := (subgroupOfEquivOfLe s.component.1).symm
  let g := ((QuotientGroup.mk' R).subgroupMap (K.subgroupOf H)).comp a.toMonoidHom
  have hg : Function.Surjective g :=
    ((QuotientGroup.mk' R).subgroupMap_surjective _).comp a.surjective
  have hrank : 3 ≤ primeRank 2 I := by
    rw [primeRank_equiv 2 e,Matrix.PSL3Even.two_rank F (by omega) hcard]
    omega
  exact s.chosen_overcomponent_of_normal h hn hJ hKJ
    (s.overcomponent_quasisimple_of_simple_quotient_two_rank S hJ.1 hKJ g hg hrank)


private theorem unitary_not_prime_linear {I : Type*} [Group I] [Finite I]
    {f : ℕ} (hf : 2 ≤ f) (hm : ClassicalGroup.IsPSU I 3 (2 ^ f))
    (r : ℕ) (hr : r.Prime) (hr3 : 3 < r) :
    ¬ Nonempty (I ≃* PSL(2,ZMod r)) := by
  let : Fact r.Prime := ⟨hr⟩
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
  rintro ⟨a⟩
  by_cases hf3 : 3 ≤ f
  · have htwo := BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank.two_rank
      J (by omega : 0 < f) hcard hconj
    rw [← primeRank_equiv 2 e,primeRank_equiv 2 a,
      Theory.PSL2.primeField_two_rank hr3] at htwo
    omega
  · have he : f = 2 := by omega
    subst f
    have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 2
      (by decide) hcard hconj
    have hord : Nat.card I = 62400 := by
      rw [Nat.card_congr e.toEquiv,
        Representation.SU3.BinaryDegree.card_projective J hcard hfixed]
      norm_num
    have hodd : Odd (Nat.card (ZMod r)) := by
      simpa using hr.odd_of_ne_two (by omega)
    have hp := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := ZMod r) hodd
    rw [← Nat.card_congr a.toEquiv,hord,Nat.card_zmod] at hp
    by_cases hsmall : r ≤ 49
    · have hb : r ^ 2 - 1 ≤ 2400 :=
        Nat.sub_le_sub_right (Nat.pow_le_pow_left hsmall 2) 1
      have hc := Nat.mul_le_mul hsmall hb
      omega
    · have hb : 2499 ≤ r ^ 2 - 1 :=
        Nat.sub_le_sub_right (Nat.pow_le_pow_left (show 50 ≤ r by omega) 2) 1
      have hc := Nat.mul_le_mul (show 50 ≤ r by omega) hb
      omega

/-- Both unitary field parities give a quasisimple containing quotient.
The degree-two exception is separated by its actual order 62400. -/
theorem ComponentSeed.chosen_overcomponent_of_unitary_image
    (s : ComponentSeed T H K) (h : Hypothesis1131At D S U₁ H)
    (hn : (K.subgroupOf H).Normal)
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : K ≤ J)
    (R : Subgroup H) [R.Normal]
    [IsSimpleGroup ((K.subgroupOf H).map (QuotientGroup.mk' R))]
    {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSU ((K.subgroupOf H).map (QuotientGroup.mk' R)) 3 (2 ^ f)) :
    Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
      (T : Subgroup G) ≤ normalizer (J : Set G) ∧
      ∃ W : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T J W) := by
  let a := (subgroupOfEquivOfLe s.component.1).symm
  let g := ((QuotientGroup.mk' R).subgroupMap (K.subgroupOf H)).comp a.toMonoidHom
  have hg : Function.Surjective g :=
    ((QuotientGroup.mk' R).subgroupMap_surjective _).comp a.surjective
  exact s.chosen_overcomponent_of_normal h hn hJ hKJ
    (s.overcomponent_quasisimple_of_simple_quotient S hJ.1 hKJ g hg
      (unitary_not_prime_linear hf hm))

/-- A Suzuki quotient also forces the actual overcomponent quotient to be
quasisimple, without requiring normality of the seed in H. -/
theorem ComponentSeed.overcomponent_source_of_suzuki
    (s : ComponentSeed T H K) (h : Hypothesis1131At D S U₁ H)
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : K ≤ J)
    {m : ℕ} (hm : 1 ≤ m)
    (he : Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J := by
  obtain ⟨e⟩ := he
  let : IsSimpleGroup (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
  let : IsSimpleGroup (K ⧸ pCore 2 K) := e.isSimpleGroup
  have hr : 3 ≤ primeRank 2 (K ⧸ pCore 2 K) := by
    rw [primeRank_equiv 2 e,BenderSuzuki.MatrixGroups.suzuki_two_rank m (by omega)]
    omega
  exact s.overcomponent_source_of_quasisimple h hJ hKJ
    (s.overcomponent_quasisimple_of_simple_quotient_two_rank S hJ.1 hKJ
      (QuotientGroup.mk' (pCore 2 K)) (QuotientGroup.mk'_surjective _) hr)

/-- The actual non-rank-one catalogue has quasisimple maximal
containing quotients, including both signed-three field parities. -/
theorem exists_componentSeed_with_quasisimple_higher_rank_source
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
          ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) ∨
        (Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
          ∃ m : ℕ, 1 ≤ m ∧ ChapterE.generationParameter H ≤ 2 * m + 1 ∧
          Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))) ∧
          solvableRadical H = pCore 2 H ∨
        (K.subgroupOf H).Normal ∧ (T : Subgroup G) ≤ normalizer (J : Set G) ∧
          (∃ W : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T J W)) ∧
          Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
          (let I := (K.subgroupOf H).map (QuotientGroup.mk' (ChapterB.minimalParabolicCore P hP))
           ∃ f : ℕ, 2 ≤ f ∧ ChapterE.generationParameter H ≤ f ∧
             (ClassicalGroup.IsPSU I 3 (2 ^ f) ∨ ClassicalGroup.IsPSL I 3 (2 ^ f) ∨
               ClassicalGroup.IsPSp I 2 (2 ^ f)))) := by
  obtain ⟨K,J,s,hKJ,hJ,hfaith,ho,hm,hcases⟩ :=
    exists_componentSeed_with_normalized_higher_rank_models h pr hc hs
  refine ⟨K,J,s,hKJ,hJ,hfaith,ho,hm,?_⟩
  rcases hcases with ⟨hlow,hrad⟩ | ⟨hn,hTJ,hchosen,f,hf,hbound,hmodels⟩
  · refine .inl ⟨?_,hrad⟩
    rcases hlow with hlin | ⟨m,hm,hbound,he⟩
    · exact .inl hlin
    · exact .inr ⟨s.overcomponent_source_of_suzuki h hJ hKJ hm he,m,hm,hbound,he⟩
  · let P := T.subtype h.outside.1.1.2
    let hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
    let R := ChapterB.minimalParabolicCore P hP
    let : IsSimpleGroup ((K.subgroupOf H).map (QuotientGroup.mk' R)) :=
      (ChapterE.Structure.source_component_simple_image P hP
        (counterexample_not_solvable h pr hc hs) (K.subgroupOf H) s.component.2
        (s.intrinsic_supplement h.outside.1.1.2)).1
    have hsource : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J := by
      rcases hmodels with huni | hlin | hsp
      · exact (s.chosen_overcomponent_of_unitary_image h hn hJ hKJ R hf huni).1
      · exact (s.chosen_overcomponent_of_linear_image h hn hJ hKJ R hf hlin).1
      · exact (s.chosen_overcomponent_of_symplectic_image h hn hJ hKJ R hsp).1
    exact .inr ⟨hn,hTJ,hchosen,hsource,f,hf,hbound,hmodels⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
