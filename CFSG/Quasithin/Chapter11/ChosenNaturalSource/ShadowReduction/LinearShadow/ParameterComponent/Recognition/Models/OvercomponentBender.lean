module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.OvercomponentSections
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Bender
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryIntrinsicQuotients
public import Theory.GroupTheory.CComponent.LocalImageEquality
public import Theory.SpecificGroups.Suzuki.LinearSeparation
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Nonabelian
public import Theory.SpecificGroups.PSL2.BinarySylowEmbedding
public import Theory.GroupTheory.SimpleSectionSolvableReduction

/-!
# Bender non-enlargement and the binary PSL₂ containing-row exclusion

Intersect the original full Sylow with a local overcomponent J and project
through J/O₂(J). If that quotient is a Bender model, every proper overgroup
of the projected Sylow is solvable. The nonsolvable local seed therefore
fills the quotient, and local C-component minimality lifts equality to K=J.
No normality of K in the ambient group or in H is imposed by this argument.

Consequently a binary PSL₂ containing quotient would give the same model
on K/O₂(K). Its simple quotient then identifies the literal star image
through the original projection. The linear-three and unitary-three rows
are incompatible with elementary abelian Sylow two-subgroups; in the
unitary row the root Sylow has order 2^(3n), while the two-rank is n.
The symplectic-four row has cubic rank two, and Suzuki has order prime to
three. These comparisons exclude every binary PSL₂ containing quotient,
at any field degree, in all non-PSL₂ source rows.

The final theorem applies this exclusion to the original component
catalogue, retaining its maximal overcomponent, chosen module, literal
quotients and independent field exponents. Other containing models,
FF exclusions, full-root lifting and recognition at n(H) remain necessary
for 11.3.5; the paired/doubled assembly still belongs to this owner.
The preceding-source discharge remains with qt-d-1222-shadow-linear-geometry.
This module does not assert unconditional 11.3.5 or 11.3.6.
Source: Aschbacher--Smith, A.3.12, pp.47--48, and 11.3.5(1), pp.771--772,
combined manuscript, 1 March 2004 (refs/quasithin.pdf).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
private theorem local_eq_of_bender_twoCore {X : Type*} [Group X] [Finite X]
    (T : Sylow 2 X) {B J : Subgroup X}
    (hB : B ∈ localCComponents T) (hJ : J ∈ localCComponents T) (hBJ : B ≤ J)
    (hm : ClassificationModels.IsBenderModel (J ⧸ pCore 2 J)) : B = J := by
  obtain ⟨P,_,hlocal⟩ := BinaryIntrinsic.local_in_local_overgroup T hB hJ hBJ
  have htop : (⊤ : Subgroup J).IsCComponent := by
    simpa only [subgroupOf_self] using hJ.subgroupOf_of_le le_rfl le_sup_left
  let q := QuotientGroup.mk' (pCore 2 J)
  let : Group.IsNilpotent (pCore 2 J) := pCore_isPGroup.isNilpotent
  have htopq : (⊤ : Subgroup (J ⧸ pCore 2 J)).IsCComponent := by
    have hh := htop.map_quotient (pCore 2 J)
    rw [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  have himage := Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal q
  have he := eq_of_bender_containing_component
    (P.mapSurjective (QuotientGroup.mk'_surjective _)) himage htopq le_top
    (hm.of_mulEquiv topEquiv)
  have hfull : B.subgroupOf J = ⊤ := by
    apply local_cComponent_eq_of_map_eq hlocal htop le_top q
    · rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup.le_sylow_of_normal P
    · simpa only [map_top_of_surjective q (QuotientGroup.mk'_surjective _)] using he
  exact le_antisymm hBJ (subgroupOf_eq_top.mp hfull)


private theorem elementary_sylow_of_binary_linear
    {X : Type*} [Group X] [Finite X] {f : ℕ}
    (hm : ClassicalGroup.IsPSL X 2 (2 ^ f)) (P : Sylow 2 X) :
    IsElementaryAbelian 2 P := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : IsElementaryAbelian 2 (Multiplicative F) :=
    { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
        intro x
        rw [pow_two]
        change x.toAdd + x.toAdd = 0
        exact CharTwo.add_self_eq_zero _) }
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨a⟩ := BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hF Q
  let b : P ≃* Q := (P : Subgroup X).equivMapOfInjective e.toMonoidHom e.injective
  exact IsElementaryAbelian.of_injective (a.symm.toMonoidHom.comp b.toMonoidHom)
    (a.symm.injective.comp b.injective)

private theorem linear_three_not_binary_linear
    {X : Type*} [Group X] [Finite X] {n f : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL X 3 (2 ^ n)) :
    ¬ ClassicalGroup.IsPSL X 2 (2 ^ f) := by
  intro hlin
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let P : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) := Classical.choice inferInstance
  let := elementary_sylow_of_binary_linear (hlin.of_mulEquiv e.symm) P
  exact Matrix.PSL3.LinearThree.sylow_not_isMulCommutative F hn hF P inferInstance

open BenderSuzuki.MatrixGroups in
private theorem unitary_three_not_binary_linear
    {X : Type*} [Group X] [Finite X] {n f : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSU X 3 (2 ^ n)) :
    ¬ ClassicalGroup.IsPSL X 2 (2 ^ f) := by
  intro hlin
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hF hconj
  obtain ⟨a⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2 ^ n) hF hfixed
  let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    Finite.of_equiv X (e.trans a).toEquiv
  let P := HermitianForm.EvenTwoRank.rootSylow J₀ rfl hn hF hfixed
  let := elementary_sylow_of_binary_linear (hlin.of_mulEquiv (e.trans a).symm) P
  have hc : Nat.card P = 2 ^ (n * 3) := by
    change Nat.card (HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage.rootGroup J₀ rfl) = _
    rw [HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage.rootGroup_card J₀ rfl
      (2 ^ n) hF hfixed, pow_mul]
  have hr := IsElementaryAbelian.primeRank_ge_of_card (p := 2) (n := n * 3)
    (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J₀)) hc
  have ht := HermitianForm.EvenTwoRank.standard_two_rank J₀ rfl hn hF hfixed
  omega

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K J : Subgroup G}

/-- A Bender containing quotient forces equality of the actual ambient
local components, through the original two-core quotient and Sylow. -/
theorem ComponentSeed.eq_overcomponent_of_bender_twoCore (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : K ≤ J)
    (hm : ClassificationModels.IsBenderModel (J ⧸ pCore 2 J)) : K = J :=
  local_eq_of_bender_twoCore T (s.mem_local_family h).1 hJ.1 hKJ hm

/-- The original seed inherits the binary linear containing model at its
literal exponent because the actual components are equal. -/
theorem ComponentSeed.linear_model_of_overcomponent (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : K ≤ J)
    {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 2 (2 ^ f)) :
    ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f) := by
  have he := s.eq_overcomponent_of_bender_twoCore h hJ hKJ (.linear f hf hm)
  subst J
  exact hm


/-- A simple binary linear component has the same model on every nontrivial
star image through the original projection. -/
theorem ComponentSeed.linear_star_model_of_linear_model (s : ComponentSeed T H K)
    (R : Subgroup H) [R.Normal] (hR : pCore 2 H ≤ R)
    [Nontrivial ((K.subgroupOf H).map (QuotientGroup.mk' R))]
    {f : ℕ} (hf : 2 ≤ f)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ f)) :
    ClassicalGroup.IsPSL ((K.subgroupOf H).map (QuotientGroup.mk' R)) 2 (2 ^ f) := by
  let B := K.subgroupOf H
  have hmodel := hm.of_mulEquiv s.intrinsicQuotientEquiv.symm
  have hsimple : IsSimpleGroup (B ⧸ pCore 2 B) := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
    have hfour : 4 ≤ Nat.card F := by
      rw [hF]
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hf
    let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hfour
    exact e.isSimpleGroup
  let := hsimple
  let q := Models.starProjection B R s.component.2 hR
  have hq := Models.starProjection_surjective B R s.component.2 hR
  let e := MulEquiv.ofBijective q ⟨q.injective_of_surjective_of_simple hq,hq⟩
  exact hmodel.of_mulEquiv e.symm

/-- The binary PSL₂ containing quotient cannot contain the original Suzuki
seed, even at a different field parameter. -/
theorem ComponentSeed.not_linear_overcomponent_of_suzuki
    (s : ComponentSeed T H K) (h : Hypothesis1131At D S U₁ H)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : K ≤ J)
    {m : ℕ} (hm : 1 ≤ m)
    (he : Nonempty ((K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    ∀ f : ℕ, 2 ≤ f → ¬ ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 2 (2 ^ f) := by
  intro f hf hlin
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := s.linear_model_of_overcomponent h hJ hKJ hf hlin
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact BenderSuzuki.MatrixGroups.not_nonempty_psl2_char_two_equiv_suzuki F
    (by omega) ⟨e.symm.trans he.some⟩

/-- The higher-rank star rows exclude every binary PSL₂ containing quotient.
The proof passes through the same original star projection, retaining a
possible central kernel until the binary containing model removes it. -/
theorem ComponentSeed.not_linear_overcomponent_of_higher_rank_image
    (s : ComponentSeed T H K) (h : Hypothesis1131At D S U₁ H)
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : K ≤ J)
    (R : Subgroup H) [R.Normal] (hR : pCore 2 H ≤ R)
    [Nontrivial ((K.subgroupOf H).map (QuotientGroup.mk' R))]
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSU ((K.subgroupOf H).map (QuotientGroup.mk' R)) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSL ((K.subgroupOf H).map (QuotientGroup.mk' R)) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSp ((K.subgroupOf H).map (QuotientGroup.mk' R)) 2 (2 ^ n)) :
    ∀ f : ℕ, 2 ≤ f → ¬ ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 2 (2 ^ f) := by
  intro f hf hlin
  have hs := s.linear_star_model_of_linear_model R hR hf
    (s.linear_model_of_overcomponent h hJ hKJ hf hlin)
  rcases hm with huni | hthree | hsp
  · exact unitary_three_not_binary_linear (by omega) huni hs
  · exact linear_three_not_binary_linear (by omega) hthree hs
  · have hlo := Models.odd_rank_of_binary_linear (by omega) hs 3 (by decide) (by decide)
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hsp
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    have hhi := Theory.SpecificGroups.SymplecticFour.OddFieldActors.cubic_rank (F := F)
    rw [primeRank_equiv 3 (e.trans
      (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm)] at hlo
    omega

/-- The source catalogue excludes binary PSL₂ containing quotients in every
non-PSL₂ row, using the actual inclusion of the original seed. -/
theorem exists_componentSeed_with_non_linear_overcomponent_models
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
              solvableRadical H = pCore 2 H) ∨
            ((K.subgroupOf H).Normal ∧ (T : Subgroup G) ≤ normalizer (J : Set G) ∧
              (∃ W : Subgroup G, Nonempty (Chapter12.Section02.ChosenModule T J W)) ∧
              (let I := (K.subgroupOf H).map (QuotientGroup.mk' (ChapterB.minimalParabolicCore P hP))
               ∃ f : ℕ, 2 ≤ f ∧ ChapterE.generationParameter H ≤ f ∧
                 (ClassicalGroup.IsPSU I 3 (2 ^ f) ∨ ClassicalGroup.IsPSL I 3 (2 ^ f) ∨
                   ClassicalGroup.IsPSp I 2 (2 ^ f))))))) := by
  obtain ⟨K,J,s,hKJ,hJ,hfaith,ho,hm,hcases⟩ :=
    exists_componentSeed_with_quasisimple_higher_rank_source h pr hc hs
  refine ⟨K,J,s,hKJ,hJ,hfaith,ho,hm,?_⟩
  rcases hcases with ⟨hlow,hrad⟩ | ⟨hn,hTJ,hchosen,hsource,n,hnn,hbound,hmodels⟩
  · rcases hlow with hlin | ⟨hsource,m,hm,hbound,he⟩
    · exact .inl ⟨hlin,hrad⟩
    · exact .inr ⟨hsource,s.not_linear_overcomponent_of_suzuki h hJ.1 hKJ hm he,
        .inl ⟨⟨m,hm,hbound,he⟩,hrad⟩⟩
  · let P := T.subtype h.outside.1.1.2
    let hP := outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h pr hc)
    let R := ChapterB.minimalParabolicCore P hP
    let : IsSimpleGroup ((K.subgroupOf H).map (QuotientGroup.mk' R)) :=
      (ChapterE.Structure.source_component_simple_image P hP
        (counterexample_not_solvable h pr hc hs) (K.subgroupOf H) s.component.2
        (s.intrinsic_supplement h.outside.1.1.2)).1
    exact .inr ⟨hsource,s.not_linear_overcomponent_of_higher_rank_image h hJ.1 hKJ R
      (ChapterB.minimalParabolicTwoCore_le_core P hP) hnn hmodels,
      .inr ⟨hn,hTJ,hchosen,n,hnn,hbound,hmodels⟩⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
