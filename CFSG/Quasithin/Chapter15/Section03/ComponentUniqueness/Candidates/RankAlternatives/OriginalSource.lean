module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.ThreePart

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.DiagonalExclusion
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.ExtensionModels.LinearPlacement
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.ModelIntersection.Basic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.RankOneAction.ActionKernel
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.Catalogue
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
public import Theory.SpecificGroups.PSL3Three.OuterTwo
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.AbelianOuter
public import Theory.SpecificGroups.SU3.NormalizedRootCentralizers.ResidualAction
public import Theory.SpecificGroups.SU3.EvenSemilinear.CyclicOuter
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.RankOneAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.RankOneModels
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SuzukiExclusion
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure.OriginalSource
public import CFSG.Quasithin.Chapter1.Section01.ModelActions115.Transport
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.OriginalOrbit
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.SourceBorel.OriginalSource
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.OrthogonalImage.FixedVectors

/-!
# The marked 1.1.5 catalogue outside signed degree three

All models in the actual marked catalogue have abelian or two-group outer
quotient except binary PSL₃, binary PSU₃, and central two-covers of PSL₃(4).
The source rank-two action kills the first two outer types. This isolates
only the actual signed matrix families for the diagonal-action calculation,
without invoking the universal A.3.18 interface.

Source: Aschbacher–Smith, 1.1.5(3) and the proof of 15.3.37, pp.501–503,
1135; the outer calculations use GLS3, Theorem 2.5.12.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.RankTwoSource
open ComponentStructure SignedReduction ModelIntersection
open ClassificationModels Chapter1.Section02.LocalModels Chapter1.XiEmbedding.OuterModels
variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]

private theorem commutative_of_equiv {A B : Type*} [Group A] [Group B]
    [IsMulCommutative B] (e : A ≃* B) : IsMulCommutative A := by
  apply IsMulCommutative.of_comm
  intro a b
  apply e.injective
  simp only [map_mul, mul_comm]

private theorem alternating_outer_two (n : ℕ) (hn : 5 ≤ n) :
    IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin n))) := by
  by_cases he : n = 6
  · subst n
    exact IsPGroup.of_card (n := 2) AlternatingSix.ShadowLocal.outer_card
  let A := alternatingGroup (Fin n)
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hcard : Nat.card (Equiv.Perm (Fin n) ⧸ A) = 2 ^ 1 := by
    rw [← A.index_eq_card]
    exact alternatingGroup.index_eq_two
  apply (IsPGroup.of_card hcard).of_surjective (MulAut.outerAction A)
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
  obtain ⟨σ, rfl⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn he).surjective a
  exact ⟨QuotientGroup.mk' A σ, rfl⟩

private theorem g2_outer {K : Type*} [Group K] {n : ℕ} (hn : 2 ≤ n)
    (hm : IsG2At K (2 ^ n)) : IsMulCommutative (MulAut.Outer K) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn
    norm_num at hh
    omega
  let := g2_outer_isCyclic_of_coverage
    (Atlas.G2.LieAutomorphismExtensions.semilinearAction_surjective (F := F) hlarge)
  exact commutative_of_equiv (MulAut.outerCongr e)

/-- The literal catalogue reduces outer-action work to signed degree three. -/
theorem abelian_or_two_or_degreeThree_of_modelAction115
    (hz : center L = pCore 2 L) (ho : pPrimeCore 2 L = ⊥)
    {α : MulAut L} (hm : ModelAction115 L α) :
    IsMulCommutative (MulAut.Outer L) ∨ IsPGroup 2 (MulAut.Outer L) ∨
      (IsSimpleGroup L ∧ ∃ n : ℕ, 1 ≤ n ∧ ClassicalGroup.IsPSL L 3 (2 ^ n)) ∨
      (IsSimpleGroup L ∧ ∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSU L 3 (2 ^ n)) ∨
      ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 4 := by
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let eqc : (L ⧸ center L) ≃* (L ⧸ pCore 2 L) :=
    QuotientGroup.quotientMulEquivOfEq hz
  cases hm with
  | lie hs hm _ =>
    let := hs
    let e : (L ⧸ pCore 2 L) ≃* L :=
      (QuotientGroup.quotientMulEquivOfEq twoCore_eq_bot_of_simple).trans QuotientGroup.quotientBot
    rcases hm with hb | ht | ⟨n, hn, he⟩
    · cases hb with
      | linear n hn he =>
        let := psl2_binary_model_outer_isMulCommutative n hn he
        exact Or.inl inferInstance
      | unitary n hn he => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨inferInstance, n, hn, he⟩)))
      | suzuki m hm he =>
        let := suzuki_outer_isCyclic m hm
        exact Or.inl
          (commutative_of_equiv (MulAut.outerCongr he.some))
    · cases ht with
      | linear n hn he => exact Or.inr (Or.inr (Or.inl ⟨inferInstance, n, hn, he⟩))
      | symplectic n hn he =>
        obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := he
        let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
        let := Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.outer_isCyclic_of_card
          hF (by omega : 1 < n)
          Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram
        exact Or.inl (commutative_of_equiv
          (MulAut.outerCongr (eF.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)))
      | g2 n hn he => exact Or.inl (g2_outer hn he)
      | triality n hn he =>
        obtain ⟨P, hq, ⟨eP⟩⟩ := he
        let : IsSimpleGroup (Triality.Standard.Carrier P) := eP.symm.isSimpleGroup
        let : Group.IsPerfect (Triality.Standard.Carrier P) :=
          Group.IsPerfect.ofSurjective (f := eP.toMonoidHom) eP.surjective
        let := Triality.Standard.OuterOdd.outer_isCyclic P n hn hq
        exact Or.inl
          (commutative_of_equiv (MulAut.outerCongr eP))
      | ree m hm he =>
        obtain ⟨b, ⟨eb⟩⟩ := he
        let : IsSimpleGroup b.fixedGroup := eb.symm.isSimpleGroup
        let : Group.IsPerfect b.fixedGroup :=
          Group.IsPerfect.ofSurjective (f := eb.toMonoidHom) eb.surjective
        let := ReeF4.LocalBlockInput.outer_isCyclic hm b
        exact Or.inl
          (commutative_of_equiv (MulAut.outerCongr eb))
      | symplectic_derived he =>
        let := AlternatingSix.ShadowLocal.outer_isMulCommutative
        exact Or.inl (commutative_of_equiv
          (MulAut.outerCongr (he.some.trans
            Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)))
      | g2_derived he =>
        let := g2_derived_outer_isCyclic_of_coverage
          Atlas.G2.LieAutomorphismExtensions.binaryConjugation_surjective
        exact Or.inl
          (commutative_of_equiv (MulAut.outerCongr he.some))
      | tits he => exact Or.inr ∘ Or.inl <|
          (Tits.OuterOddSubgroups.parrott_outer_isPGroup.of_equiv (MulAut.outerCongr he.some).symm)
    · obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := he
      let : Fintype F := Fintype.ofFinite F
      let e₂ : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
        simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
      let := BinaryLinear.OuterCyclic.psl_outer_isCyclic hn
      exact Or.inl
        (commutative_of_equiv (MulAut.outerCongr (eF.trans (Atlas.fieldEquivPSL n e₂))))
  | two_cover _ _ hm _ =>
    rcases hm with hm | hm
    · exact Or.inr (Or.inr (Or.inr (Or.inr hm)))
    · let := g2_outer (n := 2) (by decide) hm
      exact Or.inl (MulAut.outer_isMulCommutative_of_centralQuotient eqc)
  | six σ _ ha =>
    obtain ⟨e⟩ := alternating_model_of_action ho ha
    exact Or.inr ∘ Or.inl <| ((alternating_outer_two 6 (by decide)).of_equiv (MulAut.outerCongr e).symm)
  | seven σ _ ha =>
    obtain ⟨e⟩ := alternating_model_of_action ho ha
    exact Or.inr ∘ Or.inl <| ((alternating_outer_two 7 (by decide)).of_equiv (MulAut.outerCongr e).symm)
  | odd hm _ =>
    rcases hm with hm | ⟨p, hp, hm⟩
    · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
      let : Fintype F := Fintype.ofFinite F
      let e₃ : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq (by
        simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
      exact Or.inr ∘ Or.inl <| (Matrix.PSL3Three.outer_isTwoGroup.of_equiv
        (MulAut.outerCongr (e.trans (Atlas.fieldEquivPSL 3 e₃))).symm)
    · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
      let := Theory.PSL2.OuterSolvable.prime_outer_isCyclic hp.1 hF
      exact Or.inl
        (commutative_of_equiv (MulAut.outerCongr e))
  | sporadic name hne he _ =>
    let : IsSimpleGroup (L ⧸ pCore 2 L) := twoCore_quotient_simple ho
    let es := eqc.trans he.some
    have houter : IsMulCommutative (MulAut.Outer L) ∨ IsPGroup 2 (MulAut.Outer L) := by
      have two {K : Type} [Group K] (e : (L ⧸ center L) ≃* K)
          (ht : IsPGroup 2 (MulAut.Outer K)) :
          IsMulCommutative (MulAut.Outer L) ∨ IsPGroup 2 (MulAut.Outer L) :=
        Or.inr (ht.of_injective (MulAut.centralQuotientOuter e)
          (MulAut.centralQuotientOuter_injective e))
      cases name with
      | m11 => exact two es Sporadic.Mathieu.m11_outer_isPGroup_two
      | m12 => exact two es (m12_outer_isPGroup_two_of_sylow_aut
          Sporadic.Mathieu.M12SmallPair.SylowAutomorphismGroup.isPGroup_two)
      | m22 => exact two es (m22_outer_isPGroup_two_of_coverage
          Sporadic.Mathieu.m22DesignAutToAut_surjective)
      | m23 => exact two es Sporadic.Mathieu.m23_outer_isTwoGroup
      | m24 => exact two es Sporadic.Mathieu.M24OuterRestriction.outer_isPGroup_two
      | j2 => exact two es JankoTwo.outer_isPGroup_two
      | hs => exact two es (Sporadic.LeechRelated.HS.outer_isPGroup_two_of_pointStabilizer_map
          Sporadic.LeechRelated.HS.pointStabilizer_map Sporadic.LeechRelated.HS.normalizer_relIndex_dvd_two_pow)
      | ru =>
        let eRu : (L ⧸ center L) ≃* Rudvalis.Model := es
        let : IsSimpleGroup Rudvalis.Model := eRu.symm.isSimpleGroup
        let := rudvalis_outer_subsingleton
        let : IsMulCommutative (MulAut.Outer Rudvalis.Model) := ⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩
        exact Or.inl (MulAut.outer_isMulCommutative_of_centralQuotient eRu)
      | j3 => exact (hne rfl).elim
      | he => exact two es (Subgroup.isPGroup_outer_of_normalizer
          Held.permutationGroup 2 Held.Realization.normalizer_surjective Held.isPGroup_permutationNormalizerQuotient)
      | j4 => exact two es Janko4.AdequateLocal.outer_isPGroup_two
    exact houter.elim Or.inl (Or.inr ∘ Or.inl)


section Ambient
variable {G : Type*} [Group G] [Finite G]
variable {Y S M I L : Subgroup G}

omit [Finite G] in
private theorem componentOrbit_eq_localSpan (L S : Subgroup G) :
    componentOrbit L S = localSpan L S :=
  le_antisymm (iSup_conjugates_le_of_le_normalizer L S _
    (le_conjugateSpanBy L S) (le_normalizer_conjugateSpanBy L S))
    (conjugateSpanBy_le (le_componentOrbit L S) (le_normalizer_componentOrbit L S))

/-- The genuine singleton-orbit hypotheses in the rank-two paragraph. -/
structure Setup (Y S M I L : Subgroup G) : Prop where
  component_le : L ≤ I
  component : IsComponent I (L.subgroupOf I)
  odd_core : pPrimeCore 2 I = ⊥
  theta_eq : theta (M ⊓ I) = Y
  rank_component : 2 ≤ primeRank 3 L
  rank_overgroup : primeRank 3 I ≤ 2
  orbit_eq : L = localSpan L S
  orbit_bound : (normalizer (L : Set G)).relIndex I ≤ 2
  shadow : RankTwo.RankTwoShadow Y S

variable (h : Setup Y S M I L)
include h

private theorem Setup.twoPerfect : IsPPerfect 2 Y :=
  h.theta_eq ▸ ComponentIntersection.theta_isPPerfect (M ⊓ I)

private theorem Setup.normalizes : Y ⊔ S ≤ normalizer (L : Set G) := by
  apply sup_le
  · exact ComponentIntersection.normalizes_of_index_le_two
      (h.theta_eq ▸ (theta_le _).trans inf_le_right) h.twoPerfect h.orbit_bound
  · rw [h.orbit_eq]
    exact le_normalizer_conjugateSpanBy L S

private theorem Setup.le_of_inner
    (hi : ComponentIntersection.InducesInnerOnTwoCoreQuotient Y L) : Y ≤ L := by
  by_contra hn
  obtain ⟨y, hy, hyMI, hy3, hyL⟩ := exists_order_three_outside_of_local h.theta_eq hn
  let := h.component.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe h.component_le)
  exact not_section_inner_of_order_three_outside
    (local_center_eq_twoCore h.component_le h.component h.odd_core).ge
    h.component_le hyMI.2 hy3 hyL
    (local_centralizer_three_coprime h.component_le h.component h.odd_core
      h.rank_component h.rank_overgroup) (hi y hy)

private theorem Setup.le_of_abelian_outer
    (ho : IsMulCommutative (MulAut.Outer L)) : Y ≤ L := by
  let := ho
  apply h.le_of_inner
  intro y hy
  apply RankOneAction.inner_witness_of_conjugation_inner (h.normalizes (mem_sup_left hy))
  let a : (Y ⊔ S : Subgroup G) →* MulAut L :=
    L.normalizerMonoidHom.comp (inclusion h.normalizes)
  let f := (QuotientGroup.mk' (MulAut.innerSubgroup L)).comp a
  exact (QuotientGroup.eq_one_iff _).mp
    (RankTwo.abelian_action_trivial h.shadow h.twoPerfect f ⟨y, hy⟩)

private theorem Setup.le_of_outer_two
    (ho : IsPGroup 2 (MulAut.Outer L)) : Y ≤ L :=
  h.le_of_inner (RankOneAction.inner_of_twoPerfect_of_outer_twoGroup
    (le_sup_left.trans h.normalizes) h.twoPerfect ho)

private theorem Setup.linear_action_range
    {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 0 < n)
    (hcard : Nat.card F = 2 ^ n) (e : (L ⧸ pCore 2 L) ≃* PSL(3,F))
    {y : G} (hy : y ∈ Y) :
    LinearCore.quotientAction (Yplus := normalizer (L : Set G)) le_rfl e
      ⟨y, h.normalizes (mem_sup_left hy)⟩ ∈
        (Matrix.PSL3.OuterSolvable.linearConj F).range := by
  let a := LinearCore.quotientAction h.normalizes e
  let q := QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))
  let N := Matrix.PSL3.OuterSolvable.innerDiagonalOuter F
  have hcover := Matrix.PSL3.OuterSolvable.standard_eq_top_of_two_power_card F hn hcard
  let : N.Normal := Matrix.PSL3.OuterSolvable.innerDiagonalOuter_normal_of_coverage F hcover
  let := Matrix.PSL3.OuterSolvable.outerDiagonalQuotient_isMulCommutative_of_coverage F hcover
  let f := (QuotientGroup.mk' N).comp (q.comp a)
  have he := RankTwo.abelian_action_trivial h.shadow h.twoPerfect f ⟨y, hy⟩
  have hm : q (a (inclusion le_sup_left ⟨y, hy⟩)) ∈ N :=
    (QuotientGroup.eq_one_iff _).mp he
  have hc : N.comap q = (Matrix.PSL3.OuterSolvable.linearConj F).range := by
    change (Matrix.PSL3.OuterSolvable.innerDiagonalOuter F).comap q =
      Matrix.PSL3.OuterSolvable.innerDiagonal F
    rw [← Matrix.PSL3.OuterSolvable.innerDiagonal_map_outer,
      comap_map_eq, QuotientGroup.ker_mk']
    exact sup_eq_left.mpr (Matrix.PSL3.OuterSolvable.inner_le_innerDiagonal F)
  have ha : a (inclusion le_sup_left ⟨y, hy⟩) ∈
      (Matrix.PSL3.OuterSolvable.linearConj F).range := hc ▸ hm
  convert ha using 1
  rfl

private theorem Setup.unitary_action_range
    {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {n : ℕ} (hn : 1 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x : F, J.conj x = x ^ (2 ^ n))
    (e : (L ⧸ pCore 2 L) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    {y : G} (hy : y ∈ Y) :
    LinearCore.quotientAction (Yplus := normalizer (L : Set G)) le_rfl e
      ⟨y, h.normalizes (mem_sup_left hy)⟩ ∈ J.unitaryConjHom.range := by
  have hcover := HermitianForm.EvenSemilinear.semilinear_coverage J hJ
    (by omega : 2 ≤ n) hcard hconj
  let N := J.unitaryOuterHom.range
  let : N.Normal := J.unitaryOuterHom_range_normal_of_semilinear_coverage hJ hcover
  let := J.outer_mod_unitary_isCyclic_of_semilinear_coverage hJ hcover
  let a := LinearCore.quotientAction h.normalizes e
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
  let f := (QuotientGroup.mk' N).comp (q.comp a)
  have he := RankTwo.abelian_action_trivial h.shadow h.twoPerfect f ⟨y, hy⟩
  have hm : q (a (inclusion le_sup_left ⟨y, hy⟩)) ∈ N :=
    (QuotientGroup.eq_one_iff _).mp he
  have hc : N.comap q = J.unitaryConjHom.range := by
    change J.unitaryOuterHom.range.comap q = _
    rw [HermitianForm.unitaryOuterHom, MonoidHom.range_comp, comap_map_eq, QuotientGroup.ker_mk']
    exact sup_eq_left.mpr (HermitianForm.NormalizedRootCentralizers.inner_le_unitary J)
  have ha : a (inclusion le_sup_left ⟨y, hy⟩) ∈ J.unitaryConjHom.range := hc ▸ hm
  convert ha using 1
  rfl

private theorem Setup.linear_diagonal
    (hnot : ¬ Y ≤ L) {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 (2 ^ n)) :
    ∃ y ∈ Y, orderOf y = 3 ∧ LinearDiagonalOnTwoQuotient L y (2 ^ n) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  obtain ⟨y, hy, hyMI, hy3, hyL⟩ := exists_order_three_outside_of_local h.theta_eq hnot
  exact ⟨y, hy, hy3, linear_diagonal_of_action_range h.component_le h.component
    h.odd_core h.rank_component h.rank_overgroup hyMI.2 hy3 hyL
    (h.normalizes (mem_sup_left hy)) hF e (h.linear_action_range hn hF e hy)⟩

private theorem Setup.unitary_diagonal
    (hnot : ¬ Y ≤ L) {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSU L 3 (2 ^ n)) [IsSimpleGroup L] :
    ∃ y ∈ Y, orderOf y = 3 ∧ UnitaryDiagonalOnTwoQuotient L y (2 ^ n) := by
  let := h.component.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe h.component_le)
  obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := hm
  have hfixed : Nat.card {x : F // J.conj x = x} = 2 ^ n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hF hconj
  obtain ⟨eJ⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J (2 ^ n) hF hfixed
  let J' := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  let e' := e.trans eJ
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J') := e'.symm.isSimpleGroup
  let eq : (L ⧸ pCore 2 L) ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq twoCore_eq_bot_of_simple).trans QuotientGroup.quotientBot
  obtain ⟨y, hy, hyMI, hy3, hyL⟩ := exists_order_three_outside_of_local h.theta_eq hnot
  exact ⟨y, hy, hy3, unitary_diagonal_of_action_range h.component_le h.component
    h.odd_core h.rank_component h.rank_overgroup hyMI.2 hy3 hyL
    (h.normalizes (mem_sup_left hy)) J' hF hconj (eq.trans e')
    (h.unitary_action_range J' rfl (by omega) hF hconj (eq.trans e') hy)⟩

/-- The actual marked model and rank-two shadow give the signed alternative
whenever Y₊ is not contained in the singleton component. -/
theorem Setup.diagonal_of_modelAction115 (hnot : ¬ Y ≤ L)
    {α : MulAut L} (hm : ModelAction115 L α) :
    DiagonalAlternative15343 Y L (localSpan L S) := by
  let := h.component.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe h.component_le)
  have hz := local_center_eq_twoCore h.component_le h.component h.odd_core
  have ho : pPrimeCore 2 L = ⊥ := by
    have hh := h.component.1.pPrimeCore_eq_bot h.odd_core
    have he := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe h.component_le)
    simpa only [hh, Subgroup.map_bot] using he.symm
  rcases abelian_or_two_or_degreeThree_of_modelAction115 hz ho hm with
      hcomm | htwo | ⟨hs, n, hn, hlin⟩ | ⟨hs, n, hn, hunit⟩ | hcover
  · exact (hnot (h.le_of_abelian_outer hcomm)).elim
  · exact (hnot (h.le_of_outer_two htwo)).elim
  · let := hs
    by_cases he : Even n
    · let eq : (L ⧸ pCore 2 L) ≃* L :=
        (QuotientGroup.quotientMulEquivOfEq twoCore_eq_bot_of_simple).trans QuotientGroup.quotientBot
      obtain ⟨y, hy, hy3, hyact⟩ := h.linear_diagonal hnot (by omega) (hlin.of_mulEquiv eq)
      exact ⟨h.orbit_eq, y, hy, hy3, Or.inl ⟨n, by omega,
        by simpa [Nat.even_iff.mp he] using Nat.BinaryTorusParity.two_pow_mod_three n,
        hlin, hyact⟩⟩
    · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hlin
      let := Matrix.PSL3.OuterSolvable.outer_isMulCommutative_of_two_power_card_mod_three
        F (by omega : 0 < n) hF (by
          have hh : n % 2 ≠ 0 := by simpa only [Nat.even_iff] using he
          simpa only [if_neg hh] using Nat.BinaryTorusParity.two_pow_mod_three n)
      exact (hnot (h.le_of_abelian_outer (commutative_of_equiv (MulAut.outerCongr e)))).elim
  · let := hs
    by_cases he : Even n
    · obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := hunit
      let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := e.symm.isSimpleGroup
      let := HermitianForm.EvenSemilinear.outer_isCyclic_of_even J (by omega) he hF hconj
      exact (hnot (h.le_of_abelian_outer (commutative_of_equiv (MulAut.outerCongr e)))).elim
    · obtain ⟨y, hy, hy3, hyact⟩ := h.unitary_diagonal hnot hn hunit
      have hmod : 2 ^ n % 3 = 2 := by
        have hh : n % 2 ≠ 0 := by simpa only [Nat.even_iff] using he
        simpa only [if_neg hh] using Nat.BinaryTorusParity.two_pow_mod_three n
      exact ⟨h.orbit_eq, y, hy, hy3, Or.inr (Or.inl ⟨n, by omega, hmod, hunit, hyact⟩)⟩
  · obtain ⟨y, hy, hy3, hyact⟩ := h.linear_diagonal hnot (n := 2) (by decide) hcover
    exact ⟨h.orbit_eq, y, hy, hy3, Or.inr (Or.inr hyact)⟩

omit h

open DiagonalOuter.CoverReduction
open ChapterA.Section05To06

/-- The original marked ordinary component supplies the complete diagonal
product when its rank is two and its Sylow orbit is a singleton. The earlier
record contains precisely the independent source11,13,25,36 conclusions. -/
theorem rankTwoDiagonal_from_selection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I L : Subgroup G} (hI : I ∈ d.Hplus)
    (hLI : L ≤ I) (hL : IsComponent I (L.subgroupOf I))
    (hLrank : primeRank 3 L = 2) (hYrank : primeRank 3 d.Yplus = 2)
    (horbit : L = localSpan L d.S) (hnot : ¬ d.Yplus ≤ L)
    (earlier : LocalCover.SourceBorel.Earlier d)
    (hchoice : Chapter4.UniqueMaximalOvergroup (d.Y ⊔ d.S) d.M →
      d.Yplus = Stellmacher.twoResidualAmbient (d.Y ⊓ centralizer (d.V₁ : Set G)) →
      normalizer (d.V₁ : Set G) ≤ d.M ∧ normalizer (d.V₂ : Set G) ≤ d.M)
    (h7 : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V ∨
      ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action)
    (himage7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hΩ : centralOmegaIn d.S ≤ d.V)
    (hVY : d.V ⊓ centralizer (d.Y : Set G) = ⊥) :
    RankTwoDiagonal d.Yplus L (localSpan L d.S) := by
  obtain ⟨z, _, _, _, h33⟩ := ordinary_component_structure_from_selection
    hG d hempty hM hu hmany hI hL
  obtain ⟨α, _, hm⟩ := h33.model_action
  have hnormal := LocalCover.rank_two_component_normal_in hLI hL
    (earlier.odd I hI) (earlier.rank I hI) hLrank
  have hn : I ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hLI).mp hnormal
  have hs : Setup d.Yplus d.S d.M I L := {
    component_le := hLI
    component := hL
    odd_core := earlier.odd I hI
    theta_eq := earlier.theta_eq I hI
    rank_component := hLrank.ge
    rank_overgroup := earlier.rank I hI
    orbit_eq := horbit
    orbit_bound := by rw [relIndex_eq_one.mpr hn]; decide
    shadow := earlier.shadow }
  exact rankTwoDiagonal_of_signed_of_source hI hLI hL hLrank hYrank earlier
    (hs.diagonal_of_modelAction115 hnot (hm.of_mulEquiv (subgroupOfEquivOfLe hLI).symm))
    hchoice h7 himage7 hΩ hVY

/-- The original marked source produces every clause of the corrected
rank-one branch, including both three-parts and the actual E₉ quotient. -/
theorem rankOneSplit_from_selection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I L : Subgroup G} (hI : I ∈ d.Hplus)
    (hLI : L ≤ I) (hL : IsComponent I (L.subgroupOf I))
    (hLrank : primeRank 3 L = 1) (hYrank : primeRank 3 d.Yplus = 2)
    (horbit : L = localSpan L d.S)
    (hindex : (normalizer (L : Set G)).relIndex I ≤ 2)
    (earlier : LocalCover.SourceBorel.Earlier d) :
    RankOneThreePartSplit d.Yplus L (localSpan L d.S) := by
  obtain ⟨z, _, _, _, h33⟩ := ordinary_component_structure_from_selection
    hG d hempty hM hu hmany hI hL
  let := hL.2
  let e := subgroupOfEquivOfLe hLI
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv e
  have hoK := hL.1.pPrimeCore_eq_bot (earlier.odd I hI)
  have ho : pPrimeCore 2 L = ⊥ := by
    rw [← pPrimeCore_map_iso 2 e, hoK, Subgroup.map_bot]
  obtain ⟨α, _, hm⟩ := h33.model_action
  obtain ⟨hmodel,hcore⟩ := SignedReduction.RankOneModels.rankOneInitialModel_and_core
    _ (hm.of_mulEquiv e.symm) ho hLrank
  have hrne := (ComponentIntersection.source_lemma_15_3_12_1_from_selection
    hG d hempty hM hu hmany hI hLI hL.isCComponent hYrank (by omega)).1
  have hs : RankOneAction.Setup d.Yplus d.S d.M I L := {
    outside := hI
    sylow := earlier.sylow I hI
    sylow_le := inf_le_left.trans d.sylow_le
    component_le := hLI
    component := hL
    component_outside := by simpa only [map_subgroupOf_eq_of_le hLI] using h33.outside
    orbit_eq := horbit
    orbit_bound := hindex
    theta_eq := earlier.theta_eq I hI
    normalizer_eq := earlier.normalizer_eq I hI
    quotient_three := IsPGroup.of_exponent_dvd_pow (n := 1)
      (by simpa only [pow_one] using earlier.quotient_exponent)
    rank_component := hLrank
    rank_yplus := hYrank
    residual_ne := hrne
    characteristic_two_containment := by
      let := earlier.solvable
      intro D hD hDN hDF
      exact lemma_15_3_33_1 hI earlier.sylow earlier.exclusion earlier.odd
        (hD.trans (conjugateSpanBy_le hLI (le_sup_right.trans hI.1.2 |>.trans I.le_normalizer))) hDN hDF }
  obtain ⟨hm,hi⟩ := hs.rankOneModel_and_inner (earlier.odd I hI) hcore hmodel
  obtain ⟨hp, _, _, _, hq, hpart, hcent⟩ :=
    ComponentIntersection.source_lemma_15_3_12_2_three_parts_from_selection
      hG d hempty hM hu hmany hI hLI hL.isCComponent hYrank hLrank hi
  have hcentral : ComponentIntersection.centralizerResidual d.Yplus L =
      centralizingPart d.Yplus L := sectionCentralizingPart_eq_centralizingPart
        (local_center_eq_twoCore hLI hL (earlier.odd I hI)).ge
  refine ⟨horbit, hm, ?_, hpart, ?_, hq⟩
  · simpa only [hcentral, ComponentIntersection.intersectionResidual] using hp
  · simpa only [hcentral] using hcent

/-- The corrected source37 alternatives for an original ordinary component.
The uniform earlier-source record is built independently of this classification. -/
theorem alternatives_from_selection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I L : Subgroup G} (hI : I ∈ d.Hplus)
    (hLI : L ≤ I) (hL : IsComponent I (L.subgroupOf I))
    (hYrank : primeRank 3 d.Yplus = 2)
    (earlier : LocalCover.SourceBorel.Earlier d)
    (hchoice : Chapter4.UniqueMaximalOvergroup (d.Y ⊔ d.S) d.M →
      d.Yplus = Stellmacher.twoResidualAmbient (d.Y ⊓ centralizer (d.V₁ : Set G)) →
      normalizer (d.V₁ : Set G) ≤ d.M ∧ normalizer (d.V₂ : Set G) ≤ d.M)
    (h7 : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V ∨
      ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action)
    (himage7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hΩ : centralOmegaIn d.S ≤ d.V)
    (hVY : d.V ⊓ centralizer (d.Y : Set G) = ⊥) :
    Alternatives15337ThreePart d.Yplus L (componentOrbit L d.S) := by
  rw [componentOrbit_eq_localSpan L d.S]
  by_cases hy : d.Yplus ≤ localSpan L d.S
  · exact Or.inl hy
  have hQ := OutsideStructure.outside_twoCoreQuotient_sqtk hG d hI
  have hindex : (normalizer (L : Set G)).relIndex I ≤ 2 := by
    change ((normalizer (L : Set G)).subgroupOf I).index ≤ 2
    rw [subgroupOf_normalizer_eq hLI]
    rcases Chapter1.Section02.proposition_1_2_1_three_index_knownSimple hQ hL.isCComponent with
      hn | ⟨hi,_⟩
    · let := hn
      rw [Subgroup.normalizer_eq_top, Subgroup.index_top]
      decide
    · exact hi.le
  obtain ⟨z, _, _, _, h33⟩ := ordinary_component_structure_from_selection
    hG d hempty hM hu hmany hI hL
  have hYthree : IsPGroup 3 (d.Yplus ⧸ pCore 2 d.Yplus) :=
    IsPGroup.of_exponent_dvd_pow (n := 1)
      (by simpa only [pow_one] using earlier.quotient_exponent)
  have hrpos := (SuzukiExclusion.lemma_15_3_34 hI earlier.sylow earlier.exclusion
    earlier.odd (inf_le_left.trans d.sylow_le) (earlier.normalizer_eq I hI)
    hYthree (earlier.theta_eq I hI).symm hLI hL h33 hindex).2
  have horbit : L = localSpan L d.S := by
    by_contra hne
    let := hL.2
    have hz := component_center_eq_twoCore hL (earlier.odd I hI)
    let : IsSimpleGroup ((L.subgroupOf I) ⧸ pCore 2 (L.subgroupOf I)) :=
      ((QuotientGroup.quotientMulEquivOfEq hz).isSimpleGroup_congr).mp IsQuasisimple.simple
    let : IsQuasisimple ((L.subgroupOf I) ⧸ pCore 2 (L.subgroupOf I)) :=
      IsQuasisimple.of_surjective _ (QuotientGroup.mk'_surjective (pCore 2 (L.subgroupOf I)))
    have hrq : 1 ≤ primeRank 3 ((L.subgroupOf I) ⧸ pCore 2 (L.subgroupOf I)) := by
      rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup,
        primeRank_equiv 3 (subgroupOfEquivOfLe hLI)]
      exact hrpos
    have hd : 3 ∣ Nat.card ((L.subgroupOf I) ⧸ pCore 2 (L.subgroupOf I)) := by
      by_contra hn
      have hh := PrimeRank.eq_zero_iff_not_dvd_card.mpr hn
      omega
    have hres := source_threeResidual_eq_nonnormal_orbit hG d hI hLI hL.isCComponent
      hd (lt_of_le_of_ne (le_conjugateSpanBy L d.S) hne)
    exact hy ((yplus_le_theta_of_local (earlier.theta_eq I hI)).trans
      ((theta_le_threeResidual I).trans hres.le))
  have hrbound : primeRank 3 L ≤ 2 :=
    (primeRank_mono 3 hLI).trans (earlier.rank I hI)
  by_cases hrone : primeRank 3 L = 1
  · exact Or.inr (Or.inl (rankOneSplit_from_selection hG d hempty hM hu hmany hI
      hLI hL hrone hYrank horbit hindex earlier))
  · have hrtwo : primeRank 3 L = 2 := by omega
    have hnot : ¬ d.Yplus ≤ L := fun hh => hy (hh.trans (le_conjugateSpanBy L d.S))
    exact Or.inr (Or.inr (rankTwoDiagonal_from_selection hG d hempty hM hu hmany hI
      hLI hL hrtwo hYrank horbit hnot earlier hchoice h7 himage7 hΩ hVY))

/-- Original source37 with the rank-two case of source11 and the independently
proved characteristic-two exclusion13. All marked model, action, orbit,
Sylow, plane and residual premises are discharged on the actual local data. -/
theorem source_lemma_15_3_37_from_selection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (h13 : ∀ J ∈ d.Hplus, generalizedFitting J ≠ pCore 2 J)
    {I₀ I L : Subgroup G} (hI₀ : I₀ ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I₀)
    (hI : I ∈ d.Hplus) (hLI : L ≤ I) (hL : IsComponent I (L.subgroupOf I)) :
    Alternatives15337ThreePart d.Yplus L (componentOrbit L d.S) := by
  have earlier := LocalCover.source_borel_earlier_from_selection hG d hempty hM hu hmany h13 htwo
  have hYrank := LocalCover.rank_two_yplus_of_rank_two_case hG d hI₀ htwo
  obtain ⟨hne,_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  obtain ⟨himage,_,_,_,_,_,h7⟩ :=
    source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action hM hu hmany hne
  apply alternatives_from_selection hG d hempty hM hu hmany hI hLI hL hYrank earlier
  · intro hchoice hY
    have hs := (OutsideStructure.source_lemma_15_3_11_from_selection
      hG d hempty hM hu hmany I₀ hI₀).second_choice ⟨hchoice, hY⟩
    exact ⟨hs.2.1, hs.2.2.1⟩
  · exact h7
  · exact himage
  · rw [← (source_lemma_15_3_8 d.T d.action d.sylow_le 1).1]
    exact inf_le_left
  · exact d.action.fixedPlane_eq_bot_of_residual_image
      (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) himage

end Ambient
end CFSG.Quasithin.Chapter15.Section03.Candidates.RankTwoSource
