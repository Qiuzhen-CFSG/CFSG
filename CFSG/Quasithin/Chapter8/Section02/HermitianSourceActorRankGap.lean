module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectionCenter
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.LinearEquality.NaturalLift
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.RankOne
public import Theory.SpecificGroups.SL2.SylowConsequences

/-!
# The strict rank gap for the original selected actor

The literal actor embeds in the induced automizer with kernel equal to the
original conjugate intersection. If its rank is at most k in the PSL₂
family, the actual central core quotient is natural; transitivity makes
the core elementary and hence supplies an offender, contrary to the
selected non-FF action. At k = 1 the rank-one core calculation gives the
same contradiction. The Suzuki minimum degree supplies its strict gap.

Thus the actor rank is greater than k for every selected pair. This is a
proved part of the E.2.14(7) argument, not its full twice-k conclusion.
HermitianSourceEndpointRanks applies the gap to the original torus endpoint.
The original selection, torus clause and field-four endgame remain open.

Source: Aschbacher–Smith E.2.13(4), E.2.14(2,5,7), printed pp.224–228,
and 8.2.2(7), printed p.715 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
open BenderSuzuki.PFAppendixIII BenderSuzuki.Converse BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G]
  {H T M V I : Subgroup G} [IsElementaryAbelian 2 V]
  {k : ℕ} {i : I} {S : Sylow 2 I}

private theorem generator_proper (s : Selected H T M V I k i S) : V.subgroupOf I ≠ ⊤ := by
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

private theorem actor_normalizes (s : Selected H T M V I k i S) :
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
theorem selected_actor_rank_eq_native (s : Selected H T M V I k i S) :
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

private theorem core_card_eq_star (s : Selected H T M V I k i S) :
    Nat.card (coreImage I V) = Nat.card (starImage M I V) := by
  rw [←starImage_map_coreQuotientEquiv M I V s.core_eq,
    card_map_of_injective (coreQuotientEquiv M I s.core_eq).injective]

private theorem selected_not_elementary_pair_core (s : Selected H T M V I k i S)
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

private theorem selected_rank_gt_one (s : Selected H T M V I k i S) (hk : k = 1) :
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
  exact selected_not_elementary_pair_core s 1 hc (by omega)
    (s.twoConjugate.P_elementary_of_actor_index_two hidx)

private theorem selected_linear_rank_gt_parameter
    (s : Selected H T M V I k i S) (hk : 1 < k)
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
  apply selected_not_elementary_pair_core s k ?_ ?_ hP
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
theorem selected_actor_rank_gt_parameter (s : Selected H T M V I k i S) :
    k < rank (inducedAutomizer V
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype)) := by
  rw [selected_actor_rank_eq_native s]
  rcases s.models with ⟨hk,e,_⟩ | ⟨m,hm,hk,e,_⟩ | ⟨hk,_⟩
  · exact selected_linear_rank_gt_parameter s hk e
  · let e' := (QuotientGroup.quotientMulEquivOfEq s.core_eq).trans e
    have hd := s.twoConjugate.actor_rank_ge_suzuki s.characteristic_two m (by omega) e'
    omega
  · rw [hk]
    exact selected_rank_gt_one s hk


end CFSG.Quasithin.Chapter8.Section02.HermitianSource
