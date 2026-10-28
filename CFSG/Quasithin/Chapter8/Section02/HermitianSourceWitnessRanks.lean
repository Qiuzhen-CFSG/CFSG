module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceWitnessGeometry
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceLinearRanks

/-!
# A geometric bound for the actual witness degree

The native actor has rank strictly greater than the quotient field degree:
in the small-rank linear case its core would be elementary and give an FF
actor on the original V. The natural-sum theorem makes the linear actor rank
divisible by that degree. The Suzuki and dihedral calculations give the same
lower bound of twice the degree. The Hermitian automizer has two-rank at most
4n, so the actual witness degree is at most 2n.

These are the actor arguments already used for `Selected`, applied to the
proved `GeometricSelected` clauses. They use neither ambient E-generation nor
its relation to quotient fields. Together with the actual weak-closure lower
bound they provide precisely n ≤ k ≤ 2n for the original chosen-module
consumer, including the endpoint needed by the subsequent torus argument.

Source: Aschbacher--Smith E.2.13(4), E.2.14(2,5,7), and 8.2.3,
printed pp.224--228,715--716, refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource.GeometricSelected
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
open BenderSuzuki.PFAppendixIII BenderSuzuki.Converse BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G]
  {H T M V I : Subgroup G} [IsElementaryAbelian 2 V]
  {k : ℕ} {i : I} {S : Sylow 2 I}

omit [Finite G] in
private theorem generator_proper (s : GeometricSelected H T M V I k i S) : V.subgroupOf I ≠ ⊤ := by
  intro he
  have hS : (S : Subgroup I) = ⊤ := top_unique (he ▸ s.twoConjugate.le_sylow)
  have hp : IsPGroup 2 (⊤ : Subgroup I) := hS ▸ S.isPGroup'
  have hc : pCore 2 I = ⊤ := top_unique (le_sSup ⟨inferInstance,hp⟩)
  have hq : coreImage I V = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [QuotientGroup.ker_mk',hc]
    exact le_top
  have hr := s.rank_eq
  rw [hq,Representation.BinaryOffender.rank_bot] at hr
  have hk := s.positive
  omega

private theorem actor_normalizes (s : GeometricSelected H T M V I k i S) :
    V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype ≤
      normalizer (V : Set G) := by
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  rw [← selected_actor_image I M V hVI S i s.twoConjugate]
  rintro _ ⟨a,ha,rfl⟩
  have hn := s.twoConjugate.sylow_le_normalizer (DihedralCubic.A_le_sylow s.twoConjugate ha)
  rw [←subgroupOf_normalizer_eq hVI] at hn
  exact hn

/-- The original automizer rank is the rank of the literal native actor
quotient by the two-conjugate intersection. -/
theorem actor_rank_eq_native (s : GeometricSelected H T M V I k i S) :
    rank (inducedAutomizer V
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype)) =
      Nat.log 2 ((TwoConjugate.Z (V.subgroupOf I) i⁻¹).relIndex
        (TwoConjugate.A (V.subgroupOf I) (M.subgroupOf I) i⁻¹)) := by
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  rw [rank_inducedAutomizer V _ (actor_normalizes s),
    selected_actor_kernel I M V hVI S i s.twoConjugate]
  unfold subgroupCorank
  rw [←selected_intersection_image I V hVI i,
    ←selected_actor_image I M V hVI S i s.twoConjugate,
    relIndex_map_map_of_injective _ _ I.subtype_injective]

omit [Finite G] in
private theorem core_card_eq_star (s : GeometricSelected H T M V I k i S) :
    Nat.card (coreImage I V) = Nat.card (starImage M I V) := by
  rw [←starImage_map_coreQuotientEquiv M I V s.core_eq,
    card_map_of_injective (coreQuotientEquiv M I s.core_eq).injective]

private theorem not_elementary_pair_core (s : GeometricSelected H T M V I k i S)
    (d : ℕ) (hstar : Nat.card (coreImage I V) ≤ 2^d)
    (hd : d ≤ Nat.log 2 ((TwoConjugate.Z (V.subgroupOf I) i⁻¹).relIndex
      (TwoConjugate.A (V.subgroupOf I) (M.subgroupOf I) i⁻¹))) :
    ¬ IsElementaryAbelian 2 (TwoConjugate.P (V.subgroupOf I) (M.subgroupOf I) i⁻¹) := by
  intro hP
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hSN : (S : Subgroup I).map I.subtype ≤ normalizer (V : Set G) := by
    rintro _ ⟨a,ha,rfl⟩
    have hn := s.twoConjugate.sylow_le_normalizer ha
    rw [←subgroupOf_normalizer_eq hVI] at hn
    exact hn
  let a := DihedralCubic.actorIn s.twoConjugate hSN
  let ψ : TwoConjugate.A (V.subgroupOf I) (M.subgroupOf I) i⁻¹ →*
      inducedAutomizer V I :=
    (V.normalizerMonoidHom.rangeRestrict.comp a).codRestrict (inducedAutomizer V I)
      (fun x => mem_map_of_mem _ x.val.property)
  let ρ := (automizerRepresentation V).comp (inducedAutomizer V I).subtype
  let e := subgroupOfEquivOfLe hVI
  have hρ : Function.Injective ρ := (automizerRepresentation_injective V).comp
    (inducedAutomizer V I).subtype_injective
  have ha : ∀ (x : TwoConjugate.A (V.subgroupOf I) (M.subgroupOf I) i⁻¹)
      (v : V.subgroupOf I),
      (e.symm (ρ (ψ x) (Additive.ofMul (e v))).toMul : I) =
        (x : I) * v * (x : I)⁻¹ := by
    intro x v
    apply Subtype.ext
    rfl
  have hstar' : Nat.card ((V.subgroupOf I).map
      (QuotientGroup.mk' (TwoConjugate.J (M.subgroupOf I)))) ≤ 2^d := by
    change Nat.card ((V.subgroupOf I).map (QuotientGroup.mk' (localCore M I))) ≤ _
    rw [core_card_eq_star s] at hstar
    exact hstar
  exact (not_le_of_gt s.quadraticRatio_gt_one)
    (s.twoConjugate.offender_of_P_elementary_and_star_dimension
      (generator_proper s) s.characteristic_two hP e ρ hρ ψ ha d hstar' hd).2

private theorem rank_gt_one (s : GeometricSelected H T M V I k i S) (hk : k = 1) :
    1 < Nat.log 2 ((TwoConjugate.Z (V.subgroupOf I) i⁻¹).relIndex
      (TwoConjugate.A (V.subgroupOf I) (M.subgroupOf I) i⁻¹)) := by
  have hp := s.twoConjugate.actor_rank_pos (generator_proper s) s.characteristic_two
  by_contra! hh
  have hr : Nat.log 2 ((TwoConjugate.Z (V.subgroupOf I) i⁻¹).relIndex
      (TwoConjugate.A (V.subgroupOf I) (M.subgroupOf I) i⁻¹)) = 1 := by omega
  have hidx : (TwoConjugate.Z (V.subgroupOf I) i⁻¹).relIndex
      (TwoConjugate.A (V.subgroupOf I) (M.subgroupOf I) i⁻¹) = 2 := by
    let := s.twoConjugate.A_elementary
    rw [log_relIndex_eq_quotient_finrank] at hr
    rw [relIndex_eq_two_pow_quotient_finrank,hr]
    rfl
  have hc : Nat.card (coreImage I V) ≤ 2^1 := by
    let := s.twoConjugate.elementary
    let : IsElementaryAbelian 2 (coreImage I V) :=
      IsElementaryAbelian.map (p := 2) (A := V.subgroupOf I) (QuotientGroup.mk' (pCore 2 I))
    rw [IsElementaryTwo.card_eq_two_pow_rank ⟨?_,inferInstance⟩,s.rank_eq,hk]
    · intro he
      have h := s.rank_eq
      rw [he,Representation.BinaryOffender.rank_bot,hk] at h
      omega
  exact not_elementary_pair_core s 1 hc (by omega)
    (s.twoConjugate.P_elementary_of_actor_index_two hidx)

private theorem linear_rank_gt_parameter
    (s : GeometricSelected H T M V I k i S) (hk : 1 < k)
    (ξ : (I ⧸ pCore 2 I) ≃* PSL2 (BinaryGaloisField k)) :
    k < Nat.log 2 ((TwoConjugate.Z (V.subgroupOf I) i⁻¹).relIndex
      (TwoConjugate.A (V.subgroupOf I) (M.subgroupOf I) i⁻¹)) := by
  by_contra! hr
  let e0 := (QuotientGroup.quotientMulEquivOfEq s.core_eq).trans ξ
  let e := e0.trans (Theory.PSL2.sl2QuotientEquiv (BinaryGaloisField k)).symm
  have hcard := GaloisField.card 2 k (by omega)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (localCore M I))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let R := S.mapSurjective (f := q) hq
  have hR : (R : Subgroup SL(2,BinaryGaloisField k)) =
      (coreImage I T).map (ξ.trans (Theory.PSL2.sl2QuotientEquiv (BinaryGaloisField k)).symm).toMonoidHom := by
    change (S : Subgroup I).map q = _
    rw [s.sylow_eq]
    simp only [coreImage,map_map]
    rfl
  have hcR : embeddedCenter (R : Subgroup SL(2,BinaryGaloisField k)) = R := by
    let er := Matrix.SpecialLinearGroup.sylowEquivAdditive (BinaryGaloisField k) 2 R
    let : IsMulCommutative R := ⟨⟨fun a b => er.symm.injective (by
      simp only [map_mul]; exact mul_comm _ _)⟩⟩
    rw [embeddedCenter,center_eq_top,←MonoidHom.range_eq_map,range_subtype]
  have hVS : (V.subgroupOf I).map q = R := by
    have he := congrArg
      (Subgroup.map (ξ.trans (Theory.PSL2.sl2QuotientEquiv (BinaryGaloisField k)).symm).toMonoidHom)
      s.center_eq
    unfold embeddedCenter at he
    rw [map_embeddedCenter _ _ (ξ.trans
      (Theory.PSL2.sl2QuotientEquiv (BinaryGaloisField k)).symm).injective,←hR] at he
    change _ = embeddedCenter (R : Subgroup SL(2,BinaryGaloisField k)) at he
    rw [hcR] at he
    have hqeq : q = (ξ.trans
        (Theory.PSL2.sl2QuotientEquiv (BinaryGaloisField k)).symm).toMonoidHom.comp
        (QuotientGroup.mk' (pCore 2 I)) := by
      ext x
      simp [q,e,e0]
    rw [hqeq]
    simpa only [coreImage,map_map] using he
  let := s.twoConjugate.Z_normal
  let := s.twoConjugate.core_geometry.1
  let := s.twoConjugate.quotient_direct_sum.1
  let := ZMod.algebra (BinaryGaloisField k) 2
  obtain ⟨eP,heP⟩ := s.twoConjugate.linear_two_core_natural_of_rank_le_and_sylow
    (generator_proper s) s.characteristic_two k (by omega) hcard e hr R hVS
  have hP := s.twoConjugate.P_elementary_of_linear_two_natural
    (generator_proper s) s.characteristic_two e eP heP
  apply not_elementary_pair_core s k ?_ ?_ hP
  · have hh := s.twoConjugate.star_card_le_linear_two k hcard e
    change Nat.card ((V.subgroupOf I).map (QuotientGroup.mk' (localCore M I))) ≤ _ at hh
    rw [core_card_eq_star s]
    exact hh
  · exact s.twoConjugate.actor_rank_ge_linear_two_star (generator_proper s)
      s.characteristic_two k (by omega) hcard e

/-- In every selected nonsymplectic family the actual actor rank is
strictly larger than the selected parameter. The small linear case would
make P/Z natural and P elementary, contradicting the original non-FF action.
No E.2.14 rank clause is assumed. -/
theorem actor_rank_gt_parameter (s : GeometricSelected H T M V I k i S) :
    k < rank (inducedAutomizer V
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype)) := by
  rw [actor_rank_eq_native s]
  rcases s.models with ⟨hk,e,_⟩ | ⟨m,hm,hk,e,_⟩ | ⟨hk,_⟩
  · exact linear_rank_gt_parameter s hk e
  · let e' := (QuotientGroup.quotientMulEquivOfEq s.core_eq).trans e
    have hd := s.twoConjugate.actor_rank_ge_suzuki s.characteristic_two m (by omega) e'
    omega
  · rw [hk]
    exact rank_gt_one s hk



private theorem linear_markings
    (s : GeometricSelected H T M V I k i S)
    (ξ : (I ⧸ pCore 2 I) ≃* PSL2 (BinaryGaloisField k)) :
    let e := ((QuotientGroup.quotientMulEquivOfEq s.core_eq).trans ξ).trans
      (Theory.PSL2.sl2QuotientEquiv (BinaryGaloisField k)).symm
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (localCore M I))
    let R := S.mapSurjective (f := q)
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
    M.subgroupOf I ≤ normalizer (V.subgroupOf I : Set I) ∧
      (V.subgroupOf I).map q = R ∧
      (M.subgroupOf I).map q = normalizer (R : Set SL(2,BinaryGaloisField k)) := by
  let e0 := (QuotientGroup.quotientMulEquivOfEq s.core_eq).trans ξ
  let e := e0.trans (Theory.PSL2.sl2QuotientEquiv (BinaryGaloisField k)).symm
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (localCore M I))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let R := S.mapSurjective (f := q) hq
  let f := ξ.trans (Theory.PSL2.sl2QuotientEquiv (BinaryGaloisField k)).symm
  have hR : (R : Subgroup SL(2,BinaryGaloisField k)) = (coreImage I T).map f.toMonoidHom := by
    change (S : Subgroup I).map q = _
    rw [s.sylow_eq]
    simp only [coreImage,map_map]
    rfl
  have hcR : embeddedCenter (R : Subgroup SL(2,BinaryGaloisField k)) = R := by
    let er := Matrix.SpecialLinearGroup.sylowEquivAdditive (BinaryGaloisField k) 2 R
    let : IsMulCommutative R := ⟨⟨fun a b => er.symm.injective (by
      simp only [map_mul]; exact mul_comm _ _)⟩⟩
    rw [embeddedCenter,center_eq_top,←MonoidHom.range_eq_map,range_subtype]
  have hqeq : q = f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I)) := by
    ext x
    simp [q,e,e0,f]
  refine ⟨?_,?_,?_⟩
  · have hVI : V ≤ I := s.generate ▸ le_sup_left
    rw [←subgroupOf_normalizer_eq hVI]
    intro x hx
    exact (s.normalizer_eq.le ⟨hx,x.property⟩).2
  · have he := congrArg (Subgroup.map f.toMonoidHom) s.center_eq
    unfold embeddedCenter at he
    rw [map_embeddedCenter _ _ f.injective,←hR] at he
    change _ = embeddedCenter (R : Subgroup SL(2,BinaryGaloisField k)) at he
    rw [hcR] at he
    change (V.subgroupOf I).map q = R
    rw [hqeq]
    simpa only [coreImage,map_map] using he
  · have he := congrArg (Subgroup.map f.toMonoidHom) s.borel_eq
    rw [map_equiv_normalizer_eq,←hR] at he
    change (M.subgroupOf I).map q = _
    have hmap : (M.subgroupOf I).map q = (coreImage I M).map f.toMonoidHom := by
      simp only [coreImage,map_map]
      rw [hqeq]
    exact hmap.trans he

/-- The defining field degree divides the actual selected actor rank in
the PSL₂ row. This uses the full natural sum, including the field-four row. -/
theorem linear_actor_rank_dvd
    (s : GeometricSelected H T M V I k i S) (hk : 1 < k)
    (ξ : (I ⧸ pCore 2 I) ≃* PSL2 (BinaryGaloisField k)) :
    k ∣ rank (inducedAutomizer V
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype)) := by
  rw [actor_rank_eq_native s]
  obtain ⟨hMN,hVS,hMS⟩ := linear_markings s ξ
  exact s.twoConjugate.linear_pair_actor_rank_dvd hMN k (by omega)
    (GaloisField.card 2 k (by omega)) _ _ hVS hMS

/-- The E.2.14 rank bound needed by the original Hermitian source is now
unconditional on every selected nonsymplectic family. -/
theorem actor_rank_ge_twice_parameter (s : GeometricSelected H T M V I k i S) :
    2*k ≤ rank (inducedAutomizer V
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype)) := by
  have hgt := actor_rank_gt_parameter s
  rcases s.models with ⟨hk,e,_⟩ | ⟨m,hm,hk,e,_⟩ | ⟨hk,_⟩
  · obtain ⟨d,hd⟩ := linear_actor_rank_dvd s hk e
    have hd2 : 2 ≤ d := by nlinarith
    nlinarith
  · rw [actor_rank_eq_native s]
    let e' := (QuotientGroup.quotientMulEquivOfEq s.core_eq).trans e
    have hd := s.twoConjugate.actor_rank_ge_suzuki s.characteristic_two m (by omega) e'
    omega
  · omega


open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter

/-- The literal Hermitian automizer bounds the selected parameter by 2n,
using the proved rank bound instead of an E.2.14 callback. -/
theorem parameter_le_twice_half_degree
    (s : GeometricSelected H T M V I k i S) (n : ℕ) [NeZero n]
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j) : k ≤ 2*n := by
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let A := W ⊓ (pCore 2 I).map I.subtype
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 (inducedAutomizer V A) :=
    inducedAutomizer_elementary V A (actor_normalizes s)
  have hu : rank (inducedAutomizer V A) ≤ 4*n :=
    (offender_rank_le_primeRank _).trans ((_root_.primeRank_le_of_injective 2 j hj).trans
      (OuterRank.normalizer_twoRank_le n (normalizerCoverage n) ⟨FieldSections.centralizerEquiv n⟩))
  have hl := actor_rank_ge_twice_parameter s
  change 2*k ≤ rank (inducedAutomizer V A) at hl
  omega


end CFSG.Quasithin.Chapter8.Section02.HermitianSource.GeometricSelected
