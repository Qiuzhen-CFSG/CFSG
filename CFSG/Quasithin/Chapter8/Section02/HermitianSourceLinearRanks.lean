module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.LinearNaturalSum
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceEndpointRanks
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceActorRankGap

/-!
# The selected Hermitian actor has rank at least twice its parameter

The natural-sum theorem for the original linear-two core makes its actor
rank divisible by the defining field degree. The checked strict rank gap
then gives the twice-parameter bound. The actual Suzuki degree bound and
the parameter-one calculation give the same bound in the other rows.

The Hermitian automizer bounds the selected parameter by 2n. At equality,
the previous torus endpoint calculation gives actor rank 3n, contradicting
the new lower bound 4n. This removes the E.2.14 rank premise, including n = 1.
Selection, the torus fixed-space clause and the final field-four argument
remain with the source assembly.
Source: Aschbacher–Smith E.2.14(3,7), pp.226–228, and 8.2.3,
pp.715–716 (refs/quasithin.pdf).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE

open Offenders.Parabolic Offenders.Parabolic.Construction
open BenderSuzuki.PFAppendixIII BenderSuzuki.Converse BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G]
  {H T M V I : Subgroup G} [IsElementaryAbelian 2 V]
  {k : ℕ} {i : I} {S : Sylow 2 I}

private theorem selected_linear_markings
    (s : Selected H T M V I k i S)
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
theorem selected_linear_actor_rank_dvd
    (s : Selected H T M V I k i S) (hk : 1 < k)
    (ξ : (I ⧸ pCore 2 I) ≃* PSL2 (BinaryGaloisField k)) :
    k ∣ rank (inducedAutomizer V
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype)) := by
  rw [selected_actor_rank_eq_native s]
  obtain ⟨hMN,hVS,hMS⟩ := selected_linear_markings s ξ
  exact s.twoConjugate.linear_pair_actor_rank_dvd hMN k (by omega)
    (GaloisField.card 2 k (by omega)) _ _ hVS hMS

/-- The E.2.14 rank bound needed by the original Hermitian source is now
unconditional on every selected nonsymplectic family. -/
theorem selected_actor_rank_ge_twice_parameter (s : Selected H T M V I k i S) :
    2*k ≤ rank (inducedAutomizer V
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype)) := by
  have hgt := selected_actor_rank_gt_parameter s
  rcases s.models with ⟨hk,e,_⟩ | ⟨m,hm,hk,e,_⟩ | ⟨hk,_⟩
  · obtain ⟨d,hd⟩ := selected_linear_actor_rank_dvd s hk e
    have hd2 : 2 ≤ d := by nlinarith
    nlinarith
  · rw [selected_actor_rank_eq_native s]
    let e' := (QuotientGroup.quotientMulEquivOfEq s.core_eq).trans e
    have hd := s.twoConjugate.actor_rank_ge_suzuki s.characteristic_two m (by omega) e'
    omega
  · omega


open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter

/-- The literal Hermitian automizer bounds the selected parameter by 2n,
using the proved rank bound instead of an E.2.14 callback. -/
theorem selected_parameter_le_twice_half_degree
    (s : Selected H T M V I k i S) (n : ℕ) [NeZero n]
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j) : k ≤ 2*n := by
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let A := W ⊓ (pCore 2 I).map I.subtype
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 (inducedAutomizer V A) :=
    inducedAutomizer_elementary V A (actor_normalizes s)
  have hu : rank (inducedAutomizer V A) ≤ 4*n :=
    (offender_rank_le_primeRank _).trans ((primeRank_le_of_injective 2 j hj).trans
      (OuterRank.normalizer_twoRank_le n (normalizerCoverage n) ⟨FieldSections.centralizerEquiv n⟩))
  have hl := selected_actor_rank_ge_twice_parameter s
  change 2*k ≤ rank (inducedAutomizer V A) at hl
  omega

/-- The selected endpoint is impossible on the actual Hermitian action,
including half-degree one, with no E.2.14 rank hypothesis. -/
theorem selected_not_endpoint_of_natural_sum
    (s : Selected H T M V I k i S) (n : ℕ) [NeZero n] (hkn : k = 2*n)
    (e : Additive V ≃ₗ[ZMod 2] Space n)
    (j : Automizer V →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction n (binaryNormalizer n) (j a) (e v))
    (x : Automizer V) (ho : orderOf x = 2^k-1)
    (hx : x ∈ inducedAutomizer V (M ⊓ I))
    (hfixed : automizerFixedGroup V (zpowers x) =
      V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom) : False := by
  have ha := (selected_endpoint_actor_rank_three_mul s n hkn e j hj he x ho hx hfixed).1
  have hl := selected_actor_rank_ge_twice_parameter s
  rw [ha,hkn] at hl
  have hn := NeZero.pos n
  omega

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
