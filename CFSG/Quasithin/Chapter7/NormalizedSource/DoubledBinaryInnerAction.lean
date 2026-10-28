module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.Catalogue
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.SourceInputs
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs
public import Theory.GroupTheory.InnerImageGeometry
public import Theory.ElementaryAbelian.PrimeRankCard
public import Theory.GroupTheory.CyclicTwoAut
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryIntersection
/-!
# Inner component action on the binary doubled orbit

Every group on the full Theorem C list has a cyclic derived outer group or
an outer group of two-power order. The diagonal outer groups in the linear
and unitary degree-three rows are kept explicitly; abelianness of the full
outer group is not assumed. Perfect central covers embed in these outer
groups.

A two-perfect group acting fully on a two-subgroup has trivial image in
either kind of outer group: in the cyclic-derived case the moving image is
cyclic, whose automorphism group is a two-group. Component orbit bounds
and coprime commutator idempotence apply this to the original subgroup
[W,L₀]. Faithfulness then embeds that subgroup in the actual K/Z(K), with
the original conjugation action retained, and gives two-rank at least four.

NonFFSourceDoubledBinaryInnerAction applies the result to the original
chosen module and paired plane. The component exclusion continues with
the Sylow-center and root-group argument.
Source: Aschbacher–Smith, proof of 7.7.6, printed pp.705–706,
refs/quasithin.pdf; full Theorem C list, A.2.3–4, printed pp.33–34.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryInnerAction

private theorem cyclic_derived_of_cyclic_normal {X : Type*} [Group X]
    (N : Subgroup X) [N.Normal] [IsCyclic N] [IsMulCommutative (X ⧸ N)] :
    IsCyclic (commutator X) := by
  have hle : commutator X ≤ N :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  exact isCyclic_of_injective (inclusion hle) (inclusion_injective hle)

private theorem cyclic_derived_of_injective {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (hf : Function.Injective f) [IsCyclic (commutator Y)] :
    IsCyclic (commutator X) := by
  have hle : (commutator X).map f ≤ commutator Y := by
    change Subgroup.map f (⁅(⊤ : Subgroup X),⊤⁆ : Subgroup X) ≤ ⁅(⊤ : Subgroup Y),⊤⁆
    rw [map_commutator]
    exact commutator_mono le_top le_top
  let g : commutator X →* commutator Y := f.restrict (fun x hx => hle (mem_map_of_mem f hx))
  exact isCyclic_of_injective g (fun x y he => Subtype.ext (hf (congrArg Subtype.val he)))

private theorem commutative_cover {B S : Type*} [Group B] [Group S]
    [Group.IsPerfect B] (e : B ⧸ center B ≃* S) [IsMulCommutative (MulAut.Outer S)] :
    IsCyclic (commutator (MulAut.Outer B)) ∨ IsPGroup 2 (MulAut.Outer B) := by
  let := MulAut.outer_isMulCommutative_of_centralQuotient e
  left
  rw [(commutator_eq_bot_iff _).mpr inferInstance]
  infer_instance

private theorem cyclic_derived_cover {B S : Type*} [Group B] [Group S]
    [Group.IsPerfect B] (e : B ⧸ center B ≃* S)
    [IsCyclic (commutator (MulAut.Outer S))] :
    IsCyclic (commutator (MulAut.Outer B)) ∨ IsPGroup 2 (MulAut.Outer B) :=
  Or.inl (cyclic_derived_of_injective (MulAut.centralQuotientOuter e)
    (MulAut.centralQuotientOuter_injective e))

private theorem two_cover {B S : Type*} [Group B] [Group S]
    [Group.IsPerfect B] (e : B ⧸ center B ≃* S) (h : IsPGroup 2 (MulAut.Outer S)) :
    IsCyclic (commutator (MulAut.Outer B)) ∨ IsPGroup 2 (MulAut.Outer B) :=
  Or.inr (h.of_injective (MulAut.centralQuotientOuter e)
    (MulAut.centralQuotientOuter_injective e))

private theorem outer_linear_derived {S : Type*} [Group S]
    {F : Type*} [Field F] [Finite F] (e : S ≃* PSL(3,F))
    (hc : Matrix.PSL3.OuterSolvable.standard F = ⊤) :
    IsCyclic (commutator (MulAut.Outer S)) := by
  let := Matrix.PSL3.OuterSolvable.innerDiagonalOuter_normal_of_coverage F hc
  let := Matrix.PSL3.OuterSolvable.outerDiagonalQuotient_isMulCommutative_of_coverage F hc
  let := Matrix.PSL3.OuterSolvable.innerDiagonalOuter_isCyclic F
  let := cyclic_derived_of_cyclic_normal (Matrix.PSL3.OuterSolvable.innerDiagonalOuter F)
  exact cyclic_derived_of_injective (MulAut.outerCongr e).toMonoidHom
    (MulAut.outerCongr e).injective

private theorem outer_unitary_derived {S : Type*} [Group S]
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hc : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      ∃ σ : E ≃+* E, J.HasUnitarySemilinearForm a σ)
    (e : S ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    IsCyclic (commutator (MulAut.Outer S)) := by
  let := J.unitaryOuterHom_range_normal_of_semilinear_coverage hJ hc
  let := J.outer_mod_unitary_isCyclic_of_semilinear_coverage hJ hc
  let := J.unitaryOuterHom_range_isCyclic
  let := cyclic_derived_of_cyclic_normal J.unitaryOuterHom.range
  exact cyclic_derived_of_injective (MulAut.outerCongr e).toMonoidHom
    (MulAut.outerCongr e).injective
private theorem alternating_two (n : ℕ) (hn : 5 ≤ n) :
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


open Chapter1.Section02 Chapter1.XiEmbedding.OuterModels

/-- The full source catalogue has cyclic derived outer group or a two-group outer group. -/
theorem quasisimple_outer_structure {B : Type*} [Group B] [Finite B] [IsQuasisimple B]
    (hmodel : LocalModels.TheoremCModel (B ⧸ center B)) :
    IsCyclic (commutator (MulAut.Outer B)) ∨ IsPGroup 2 (MulAut.Outer B) := by
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  let : IsQuasisimple (B ⧸ center B) :=
    IsQuasisimple.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  cases hmodel with
  | alternating n hn he => exact two_cover he.some (alternating_two n hn.1)
  | linear_odd p n hp ho hn _ he =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := he
    exact two_cover e (Theory.PSL2.OuterSolvable.SmallDegreeSquares.outer_isPGroup_two
      hp ho (by rcases hn with rfl | rfl <;> omega) hF)
  | three_odd p hp ho unitary he =>
    cases unitary with
    | false =>
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := he
      let : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
      let : Group.IsPerfect PSL(3,F) := Group.IsPerfect.ofSurjective
        (f := e.toMonoidHom) e.surjective
      let := outer_linear_derived e (Matrix.PSL3.OuterSolvable.standard_eq_top_of_odd_prime_card
        F (Group.IsPerfect.not_isSolvable _) hp ho hF)
      exact cyclic_derived_cover (MulEquiv.refl _)
    | true =>
      obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := he
      let : Fact p.Prime := ⟨hp⟩
      have hfixed : Nat.card {x : F // J.conj x = x} = p := by
        simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
          J.conj p 1 (by decide) (by simpa only [pow_one] using hF)
          (by simpa only [pow_one] using hconj)
      obtain ⟨eJ⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
        J p hF hfixed
      let I := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
      let eS := e.trans eJ
      let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup I) := eS.symm.isSimpleGroup
      let := outer_unitary_derived I rfl
        (HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage.semilinear_coverage_odd
          I rfl hp ho hF hfixed) eS
      exact cyclic_derived_cover (MulEquiv.refl _)
  | rank_one he =>
    cases he with
    | linear n hn he =>
      let := psl2_binary_model_outer_isMulCommutative n hn he
      exact commutative_cover (MulEquiv.refl _)
    | unitary n hn he =>
      obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := he
      have hfixed : Nat.card {x : F // J.conj x = x} = 2 ^ n :=
        FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hF hconj
      obtain ⟨eJ⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
        J (2 ^ n) hF hfixed
      let I := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
      let := outer_unitary_derived I rfl (I.semilinear_coverage n hn rfl hF hfixed) (e.trans eJ)
      exact cyclic_derived_cover (MulEquiv.refl _)
    | suzuki m hm he =>
      let := suzuki_outer_isCyclic m hm
      exact commutative_cover he.some
  | rank_two he =>
    cases he with
    | linear n hn he =>
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := he
      let := outer_linear_derived e
        (Matrix.PSL3.OuterSolvable.standard_eq_top_of_two_power_card F (by omega) hF)
      exact cyclic_derived_cover (MulEquiv.refl _)
    | symplectic n hn he =>
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := he
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      let := Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.outer_isCyclic_of_card
        hF (by omega : 1 < n)
        Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram
      exact commutative_cover (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)
    | g2 n hn he =>
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := he
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
      exact commutative_cover e
    | triality n hn he =>
      obtain ⟨P, hq, ⟨e⟩⟩ := he
      let : IsSimpleGroup (Triality.Standard.Carrier P) := e.symm.isSimpleGroup
      let : Group.IsPerfect (Triality.Standard.Carrier P) :=
        Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
      let := Triality.Standard.OuterOdd.outer_isCyclic P n hn hq
      exact commutative_cover e
    | ree m hm he =>
      obtain ⟨d, ⟨e⟩⟩ := he
      let : IsSimpleGroup d.fixedGroup := e.symm.isSimpleGroup
      let : Group.IsPerfect d.fixedGroup :=
        Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
      let := ReeF4.LocalBlockInput.outer_isCyclic hm d
      exact commutative_cover e
    | symplectic_derived he =>
      let := AlternatingSix.ShadowLocal.outer_isMulCommutative
      exact commutative_cover (he.some.trans
        Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)
    | g2_derived he =>
      let := g2_derived_outer_isCyclic_of_coverage
        Atlas.G2.LieAutomorphismExtensions.binaryConjugation_surjective
      exact commutative_cover he.some
    | tits he => exact two_cover he.some Tits.OuterOddSubgroups.parrott_outer_isPGroup
  | binary_linear n hn he =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := he
    let : Fintype F := Fintype.ofFinite F
    let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
      simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
    let := BinaryLinear.OuterCyclic.psl_outer_isCyclic hn
    exact commutative_cover (e.trans (Atlas.fieldEquivPSL n eF))
  | sporadic name hne he =>
    cases name with
    | m11 => exact two_cover he.some Sporadic.Mathieu.m11_outer_isPGroup_two
    | m12 => exact two_cover he.some (m12_outer_isPGroup_two_of_sylow_aut
        Sporadic.Mathieu.M12SmallPair.SylowAutomorphismGroup.isPGroup_two)
    | m22 => exact two_cover he.some (m22_outer_isPGroup_two_of_coverage
        Sporadic.Mathieu.m22DesignAutToAut_surjective)
    | m23 => exact two_cover he.some Sporadic.Mathieu.m23_outer_isTwoGroup
    | m24 => exact two_cover he.some Sporadic.Mathieu.M24OuterRestriction.outer_isPGroup_two
    | j2 => exact two_cover he.some JankoTwo.outer_isPGroup_two
    | hs => exact two_cover he.some (Sporadic.LeechRelated.HS.outer_isPGroup_two_of_pointStabilizer_map
        Sporadic.LeechRelated.HS.pointStabilizer_map Sporadic.LeechRelated.HS.normalizer_relIndex_dvd_two_pow)
    | ru =>
      let : IsSimpleGroup Rudvalis.Model := he.some.symm.isSimpleGroup
      let := rudvalis_outer_subsingleton
      let : IsMulCommutative (MulAut.Outer Rudvalis.Model) :=
        ⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩
      exact commutative_cover (show _ ≃* Rudvalis.Model from he.some)
    | j3 => exact (hne rfl).elim
    | he => exact two_cover he.some (Subgroup.isPGroup_outer_of_normalizer
        Held.permutationGroup 2 Held.Realization.normalizer_surjective Held.isPGroup_permutationNormalizerQuotient)
    | j4 => exact two_cover he.some Janko4.AdequateLocal.outer_isPGroup_two
  | janko_one he =>
    let := janko_one_outer_isMulCommutative he.some
    exact commutative_cover (MulEquiv.refl _)

/-- Two-perfect action on a fully moved two-subgroup is trivial in these outer groups. -/
theorem moved_twoSubgroup_eq_bot {X : Type*} [Group X] [Finite X]
    (hs : IsCyclic (commutator X) ∨ IsPGroup 2 X)
    (A B : Subgroup X) (hA : IsPGroup 2 A) (hB : IsPPerfect 2 B)
    (hmove : ⁅A,B⁆ = A) : A = ⊥ := by
  rcases hs with hc | hp
  · let := hc
    have hAC : A ≤ commutator X := by
      rw [← hmove]
      exact commutator_mono le_top le_top
    let : IsCyclic A := isCyclic_of_injective (inclusion hAC) (inclusion_injective hAC)
    have hBN : B ≤ normalizer (A : Set X) :=
      le_normalizer_iff_commutator_le_left.mpr hmove.le
    let r : B →* MulAut A := A.normalizerMonoidHom.comp (inclusion hBN)
    have hr := hB.hom_eq_one_of_isPGroup hA.mulAut_of_isCyclic_two r
    have hcent : B ≤ centralizer (A : Set X) := by
      intro b hb a ha
      have hh := congrArg (fun f : B →* MulAut A => (f ⟨b,hb⟩ ⟨a,ha⟩ : X)) hr
      change b*a*b⁻¹ = a at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    rw [← hmove,commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hcent
  · have hB0 : B = ⊥ := by
      have hh := hB.hom_eq_one_of_isPGroup hp B.subtype
      apply le_bot_iff.mp
      intro b hb
      have he := DFunLike.congr_fun hh (⟨b,hb⟩ : B)
      exact mem_bot.mpr he
    rw [← hmove,hB0,commutator_bot_right]

/-- The two-residual normalizes each ordinary component in the actual overgroup. -/
theorem residual_normalizes_component
    {G : Type*} [Group G] [Finite G] (H R K : Subgroup G)
    (hQ : IsStronglyQuasithin H) (hK : IsComponentIn K H)
    (hRH : R ≤ H) (hR : IsPPerfect 2 R) : R ≤ normalizer (K : Set G) := by
  let N := normalizer (K.subgroupOf H : Set H)
  have hRN : R.subgroupOf H ≤ N := by
    rcases hK.2.normal_or_index_two_of_odd_rank_le_two hQ with hn | hi
    · let := hn
      rw [show N = normalizer (K.subgroupOf H : Set H) from rfl,normalizer_eq_top]
      exact le_top
    · let : N.Normal := N.normal_of_index_eq_two hi
      have hp : IsPGroup 2 (H ⧸ N) := IsPGroup.of_card (n := 1) (by
        change N.index = 2 ^ 1
        simpa only [pow_one] using hi)
      exact (le_pResidual_of_isPPerfect _ (hR.of_surjective
        (subgroupOfEquivOfLe hRH).symm.toMonoidHom
        (subgroupOfEquivOfLe hRH).symm.surjective)).trans (sInf_le ⟨inferInstance,hp⟩)
  have hh := map_mono (f := H.subtype) hRN
  rw [map_subgroupOf_eq_of_le hRH] at hh
  have he : N = (normalizer (K : Set G)).subgroupOf H := (subgroupOf_normalizer_eq hK.1).symm
  exact hh.trans (by
    rw [he]
    rintro x ⟨y,hy,rfl⟩
    exact hy)

/-- The moving two-subgroup acts inner through the literal normalizer homomorphism. -/
theorem residual_movement_inner
    {G : Type*} [Group G] [Finite G] (K A R : Subgroup G)
    (hs : IsCyclic (commutator (MulAut.Outer K)) ∨ IsPGroup 2 (MulAut.Outer K))
    (hA : IsPGroup 2 A) (hR : IsPPerfect 2 R)
    (hAN : A ≤ normalizer (K : Set G)) (hRN : R ≤ normalizer (K : Set G))
    (hmove : ⁅A,R⁆ = A) :
    ∀ a : A, K.normalizerMonoidHom (inclusion hAN a) ∈ MulAut.innerSubgroup K := by
  let N := normalizer (K : Set G)
  let q : N →* MulAut.Outer K :=
    (QuotientGroup.mk' (MulAut.innerSubgroup K)).comp K.normalizerMonoidHom
  let E := (A.subgroupOf N).map q
  let B := (R.subgroupOf N).map q
  have hAR : ⁅A.subgroupOf N,R.subgroupOf N⁆ = A.subgroupOf N := by
    apply map_injective N.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hAN,map_subgroupOf_eq_of_le hRN,hmove]
  have hB : IsPPerfect 2 B :=
    (hR.of_surjective (subgroupOfEquivOfLe hRN).symm.toMonoidHom
      (subgroupOfEquivOfLe hRN).symm.surjective).of_surjective _ (q.subgroupMap_surjective _)
  have hE : E = ⊥ := moved_twoSubgroup_eq_bot hs E B
    (hA.comap_subtype.map q) hB (by rw [← map_commutator,hAR])
  intro a
  have ha : q (inclusion hAN a) ∈ E := mem_map_of_mem q a.property
  rw [hE] at ha
  exact (QuotientGroup.eq_one_iff _).mp (mem_bot.mp ha)


/-- Original SQTK hypotheses supply the complete outer-group inspection for
an actual ordinary component; no model or automorphism premise is added. -/
theorem component_outer_structure
    {G : Type*} [Group G] [Finite G] (H K : Subgroup G)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hK : IsComponentIn K H) :
    IsCyclic (commutator (MulAut.Outer K)) ∨ IsPGroup 2 (MulAut.Outer K) := by
  let := hK.quasisimple
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hs : IsSQTK KnownSimple.IsKnownSimple K :=
    ⟨hH.stronglyQuasithin.of_injective (inclusion hK.1) (inclusion_injective hK.1),
      hH.isKGroup.of_injective (inclusion hK.1) (inclusion_injective hK.1)⟩
  have hm := Chapter1.QuasisimpleInvolutions.quotient_model hs
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremC_knownSimple
  exact quasisimple_outer_structure
    (ChapterA.Section03.SourceComponents.sourceTheoremC_to_local
      (Group.IsPerfect.not_isMulCommutative _) hm)

/-- The full residual moving subgroup acts inner on each ordinary component
of the original strongly quasithin K-group. -/
theorem component_movement_inner
    {G : Type*} [Group G] [Finite G] (H W R K : Subgroup G)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hK : IsComponentIn K H)
    (hWH : W ≤ H) (hRH : R ≤ H) (hW : IsPGroup 2 W)
    (hR : IsPPerfect 2 R) (hRW : R ≤ normalizer (W : Set G)) :
    ∃ hAN : ⁅W,R⁆ ≤ normalizer (K : Set G),
      ∀ a : (⁅W,R⁆ : Subgroup G), K.normalizerMonoidHom (inclusion hAN a) ∈ MulAut.innerSubgroup K := by
  have hAN := DoubledBinaryIntersection.residual_movement_normalizes_component
    H W R K hH.stronglyQuasithin hK hWH hRH hR
  exact ⟨hAN, residual_movement_inner K ⁅W,R⁆ R
    (component_outer_structure H K hH hK)
    (hW.to_le (le_normalizer_iff_commutator_le_left.mp hRW)) hR hAN
    (residual_normalizes_component H R K hH.stronglyQuasithin hK hRH hR)
    (commutator_isPPerfect_idempotent R W hR hW hRW)⟩

/-- A faithful inner action gives an embedding in the literal central quotient.
Its factorization identifies the original conjugation automorphism. -/
theorem faithful_inner_centralQuotient
    {G : Type*} [Group G] (K A : Subgroup G)
    (hAN : A ≤ normalizer (K : Set G))
    (hker : A ⊓ centralizer (K : Set G) = ⊥)
    (hi : ∀ a : A, K.normalizerMonoidHom (inclusion hAN a) ∈ MulAut.innerSubgroup K) :
    ∃ j : A →* K ⧸ center K, Function.Injective j ∧
      ∀ a : A, (innerEquivCentralQuotient.symm (j a) : MulAut K) =
        K.normalizerMonoidHom (inclusion hAN a) := by
  let r : A →* MulAut K := K.normalizerMonoidHom.comp (inclusion hAN)
  have hr : Function.Injective r := by
    apply (MonoidHom.ker_eq_bot_iff r).mp
    apply (eq_bot_iff_forall _).mpr
    intro a ha
    have hc : (a : G) ∈ centralizer (K : Set G) := by
      have hh : inclusion hAN a ∈ K.normalizerMonoidHom.ker := ha
      rw [normalizerMonoidHom_ker] at hh
      exact hh
    apply Subtype.ext
    exact mem_bot.mp (hker ▸ (show (a : G) ∈ A ⊓ centralizer (K : Set G) from ⟨a.property,hc⟩))
  let i : A →* MulAut.innerSubgroup K := r.codRestrict _ hi
  let j : A →* K ⧸ center K := innerEquivCentralQuotient.toMonoidHom.comp i
  refine ⟨j,innerEquivCentralQuotient.injective.comp
    (fun a b he => hr (congrArg Subtype.val he)),?_⟩
  intro a
  exact congrArg Subtype.val (innerEquivCentralQuotient.symm_apply_apply (i a))

/-- An elementary actor of order sixteen with faithful inner action forces
rank at least four in the actual component central quotient. -/
theorem four_le_rank_centralQuotient
    {G : Type*} [Group G] [Finite G] (K A : Subgroup G)
    [IsElementaryAbelian 2 A] (hcard : Nat.card A = 16)
    (j : A →* K ⧸ center K) (hj : Function.Injective j) :
    4 ≤ primeRank 2 (K ⧸ center K) := by
  have hr := _root_.primeRank_le_of_injective 2 j hj
  have hc := IsElementaryAbelian.log_card_eq_primeRank (p := 2) A
  rw [hcard] at hc
  norm_num at hc
  omega

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryInnerAction
