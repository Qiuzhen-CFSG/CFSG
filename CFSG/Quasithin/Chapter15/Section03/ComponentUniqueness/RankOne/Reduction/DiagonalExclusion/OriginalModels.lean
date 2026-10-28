module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.DiagonalExclusion
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.ExtensionModels.LinearPlacement
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.ModelIntersection.Basic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.RankOneAction.ActionKernel
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.Catalogue
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
public import Theory.SpecificGroups.PSL3Three.OuterTwo

/-!
# Inner action for the original marked component catalogue

In the S₃-shadow branch, an abelian outer automorphism group forces Y₊
to act innerly, and a two-group outer quotient is killed by theta generation.
The complete 1.1.5 catalogue satisfies one of these conditions except for the
signed degree-three matrix families. Existing invariant-plane arguments
exclude even-degree PSL₃ quotients, including central two-covers, and force
any PSU₃ component to have fixed-field degree two, whose outer group is cyclic.
The proof retains the actual component and its two-core throughout.

This supplies the inner-action input of the original 15.3.43 reduction directly.
No A.3.18 extension classification or diagonal actor is needed in this branch.
The local and plane records contain the earlier source hypotheses; their
construction and the moving-component case belong to the source assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 1.1.5(3),
printed pp.501–503, and the inner-action step of 15.3.43, printed p.1139,
using 15.3.11 and 15.3.33(1).
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.DiagonalExclusion.OriginalModels
open Candidates ComponentStructure SignedReduction ModelIntersection
open ClassificationModels Chapter1.Section02.LocalModels Chapter1.XiEmbedding.OuterModels

variable {G : Type*} [Group G] [Finite G]
variable {Y S M I L : Subgroup G}

private theorem commutative_of_equiv {A B : Type*} [Group A] [Group B]
    [IsMulCommutative B] (e : A ≃* B) : IsMulCommutative A := by
  apply IsMulCommutative.of_comm
  intro a b
  apply e.injective
  simp only [map_mul, mul_comm]

private theorem inner_of_outer_two (h : LocalSetup Y S M I L)
    (ho : IsPGroup 2 (MulAut.Outer L)) : Y ≤ L ⊔ centralizer (L : Set G) := by
  let := h.component.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe h.component_le)
  exact le_inner_of_section_inner
    (local_center_eq_twoCore h.component_le h.component h.odd_core).ge
    (RankOneAction.inner_of_twoPerfect_of_outer_twoGroup h.yplus_normalizes
      (h.theta_eq ▸ ComponentIntersection.theta_isPPerfect (M ⊓ I)) ho)

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

private theorem inner_of_linear (d : CharacteristicTwo.LocalData G)
    {I L : Subgroup G} (h : LocalSetup d.Yplus d.S d.M I L)
    (v : PlaneData d.Yplus d.S d.M I d.V₁ d.V₂)
    (horbit : L = localSpan L d.S) {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 (2 ^ n)) :
    d.Yplus ≤ L ⊔ centralizer (L : Set G) := by
  by_cases he : Even n
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
    exact (ExtensionModels.LinearPlacement.false_of_linear_quotient h horbit
      v.first_le v.first_centralizes v.first_normalizer hn he hF e).elim
  · have hmod : 2 ^ n % 3 = 2 := by
      have hnodd : n % 2 ≠ 0 := by simpa only [Nat.even_iff] using he
      simpa only [if_neg hnodd] using Nat.BinaryTorusParity.two_pow_mod_three n
    exact h.inner_of_abelian_outer horbit
      (h.outer_isMulCommutative_of_rankOneQuotientModel
        (Or.inr (Or.inl ⟨n, hn, hmod, hm⟩)))

private theorem inner_of_unitary (d : CharacteristicTwo.LocalData G)
    {I L : Subgroup G} (h : LocalSetup d.Yplus d.S d.M I L)
    (v : PlaneData d.Yplus d.S d.M I d.V₁ d.V₂)
    (horbit : L = localSpan L d.S) {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSU L 3 (2 ^ n)) [IsSimpleGroup L] [IsQuasisimple L] :
    d.Yplus ≤ L ⊔ centralizer (L : Set G) := by
  have hn2 := h.unitary_degree_eq_two horbit v.second_le v.second_elementary
    v.second_card v.second_normalizer v.second_normalized hn hm
  have hmod : 2 ^ n % 3 = 1 := by norm_num [hn2]
  let e : (L ⧸ pCore 2 L) ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq twoCore_eq_bot_of_simple).trans QuotientGroup.quotientBot
  exact h.inner_of_abelian_outer horbit
    (h.outer_isMulCommutative_of_rankOneQuotientModel
      (Or.inr (Or.inr (Or.inl ⟨n, hn, hmod, hm.of_mulEquiv e⟩))))

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

/-- Every original marked model acts innerly in the singleton component orbit
under the genuine S₃-shadow and invariant-plane hypotheses. -/
theorem inner_of_modelAction115 (d : CharacteristicTwo.LocalData G)
    {I L : Subgroup G} (h : LocalSetup d.Yplus d.S d.M I L)
    (v : PlaneData d.Yplus d.S d.M I d.V₁ d.V₂)
    (horbit : L = localSpan L d.S) {α : MulAut L} (hm : ModelAction115 L α) :
    d.Yplus ≤ L ⊔ centralizer (L : Set G) := by
  let := h.component.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe h.component_le)
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  have hz := local_center_eq_twoCore h.component_le h.component h.odd_core
  let eqc : (L ⧸ center L) ≃* (L ⧸ pCore 2 L) :=
    QuotientGroup.quotientMulEquivOfEq hz
  have ho : pPrimeCore 2 L = ⊥ := by
    have hh := h.component.1.pPrimeCore_eq_bot h.odd_core
    have he := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe h.component_le)
    simpa only [hh, Subgroup.map_bot] using he.symm
  cases hm with
  | lie hs hm _ =>
    let := hs
    let e : (L ⧸ pCore 2 L) ≃* L :=
      (QuotientGroup.quotientMulEquivOfEq twoCore_eq_bot_of_simple).trans QuotientGroup.quotientBot
    rcases hm with hb | ht | ⟨n, hn, he⟩
    · cases hb with
      | linear n hn he =>
        let := psl2_binary_model_outer_isMulCommutative n hn he
        exact h.inner_of_abelian_outer horbit inferInstance
      | unitary n hn he => exact inner_of_unitary d h v horbit (by omega) he
      | suzuki m hm he =>
        let := suzuki_outer_isCyclic m hm
        exact h.inner_of_abelian_outer horbit
          (commutative_of_equiv (MulAut.outerCongr he.some))
    · cases ht with
      | linear n hn he => exact inner_of_linear d h v horbit (by omega) (he.of_mulEquiv e)
      | symplectic n hn he =>
        obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := he
        let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
        let := Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.outer_isCyclic_of_card
          hF (by omega : 1 < n)
          Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram
        exact h.inner_of_abelian_outer horbit (commutative_of_equiv
          (MulAut.outerCongr (eF.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)))
      | g2 n hn he => exact h.inner_of_abelian_outer horbit (g2_outer hn he)
      | triality n hn he =>
        obtain ⟨P, hq, ⟨eP⟩⟩ := he
        let : IsSimpleGroup (Triality.Standard.Carrier P) := eP.symm.isSimpleGroup
        let : Group.IsPerfect (Triality.Standard.Carrier P) :=
          Group.IsPerfect.ofSurjective (f := eP.toMonoidHom) eP.surjective
        let := Triality.Standard.OuterOdd.outer_isCyclic P n hn hq
        exact h.inner_of_abelian_outer horbit
          (commutative_of_equiv (MulAut.outerCongr eP))
      | ree m hm he =>
        obtain ⟨b, ⟨eb⟩⟩ := he
        let : IsSimpleGroup b.fixedGroup := eb.symm.isSimpleGroup
        let : Group.IsPerfect b.fixedGroup :=
          Group.IsPerfect.ofSurjective (f := eb.toMonoidHom) eb.surjective
        let := ReeF4.LocalBlockInput.outer_isCyclic hm b
        exact h.inner_of_abelian_outer horbit
          (commutative_of_equiv (MulAut.outerCongr eb))
      | symplectic_derived he =>
        let := AlternatingSix.ShadowLocal.outer_isMulCommutative
        exact h.inner_of_abelian_outer horbit (commutative_of_equiv
          (MulAut.outerCongr (he.some.trans
            Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)))
      | g2_derived he =>
        let := g2_derived_outer_isCyclic_of_coverage
          Atlas.G2.LieAutomorphismExtensions.binaryConjugation_surjective
        exact h.inner_of_abelian_outer horbit
          (commutative_of_equiv (MulAut.outerCongr he.some))
      | tits he =>
        exact inner_of_outer_two h
          (Tits.OuterOddSubgroups.parrott_outer_isPGroup.of_equiv (MulAut.outerCongr he.some).symm)
    · obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := he
      let : Fintype F := Fintype.ofFinite F
      let e₂ : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
        simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
      let := BinaryLinear.OuterCyclic.psl_outer_isCyclic hn
      exact h.inner_of_abelian_outer horbit
        (commutative_of_equiv (MulAut.outerCongr (eF.trans (Atlas.fieldEquivPSL n e₂))))
  | two_cover _ _ hm _ =>
    rcases hm with hm | hm
    · exact inner_of_linear d h v horbit (n := 2) (by decide) hm
    · let := g2_outer (n := 2) (by decide) hm
      exact h.inner_of_abelian_outer horbit (MulAut.outer_isMulCommutative_of_centralQuotient eqc)
  | six σ _ ha =>
    obtain ⟨e⟩ := alternating_model_of_action ho ha
    exact inner_of_outer_two h ((alternating_outer_two 6 (by decide)).of_equiv (MulAut.outerCongr e).symm)
  | seven σ _ ha =>
    obtain ⟨e⟩ := alternating_model_of_action ho ha
    exact inner_of_outer_two h ((alternating_outer_two 7 (by decide)).of_equiv (MulAut.outerCongr e).symm)
  | odd hm _ =>
    rcases hm with hm | ⟨p, hp, hm⟩
    · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
      let : Fintype F := Fintype.ofFinite F
      let e₃ : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq (by
        simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
      exact inner_of_outer_two h (Matrix.PSL3Three.outer_isTwoGroup.of_equiv
        (MulAut.outerCongr (e.trans (Atlas.fieldEquivPSL 3 e₃))).symm)
    · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
      let := Theory.PSL2.OuterSolvable.prime_outer_isCyclic hp.1 hF
      exact h.inner_of_abelian_outer horbit
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
    exact houter.elim (h.inner_of_abelian_outer horbit) (inner_of_outer_two h)

end CFSG.Quasithin.Chapter15.Section03.RankOne.DiagonalExclusion.OriginalModels
