module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.PointParabolic.MathieuOverlap.Placement
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.PointParabolic
public import Theory.GroupTheory.SylowConjugateOvergroup
public import Theory.SpecificGroups.Janko4.Model.SylowNormalizer

/-!
# The reverse native Mathieu–max4 incidence

A Sylow two-subgroup in a conjugate max4 fixes a point in its five-letter
quotient action. The corresponding full point parabolic has Sylow index 63
and lies in a conjugate max1 by the certified elementary subgroup. A common
full Sylow aligns that max1 with the given Mathieu local.

The point parabolic's Mathieu image has nontrivial two-core: otherwise its
order would divide the max4 core quotient order 20160, incompatible with the
full Mathieu Sylow. Native trio recognition identifies it as a full trio
preimage. The literal projection lifts the two trio conjugators, and the
self-normalizing ambient Sylow forces equality with the given trio preimage.
Thus that whole original parabolic lies in the specified conjugate max4.

The exterior consumer `Normalizers/JankoReverseLocal` applies this incidence
to the original component map and actor. No native cover is assumed here.
Source: Aschbacher–Smith 12.5.3–4, printed pp.818–819/PDF pp.835–836.
-/

public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.SymmetricLinear
attribute [local irreducible] modelGroup matrixA matrixB max4Subgroup
local notation "M" => Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four

private lemma pointParabolic_le (j : Fin 5) : pointParabolic j ≤ max4Subgroup := map_subtype_le _

private lemma sylow_le_pointParabolic (S : Sylow 2 Model) (hS : (S : Subgroup Model) ≤ max4Subgroup) :
    ∃ j : Fin 5, (S : Subgroup Model) ≤ pointParabolic j := by
  let f : S →* Equiv.Perm (Fin 5) := ((MonoidHom.fst _ _).comp max4Projection).comp
    (inclusion hS)
  let : MulAction S (Fin 5) := MulAction.compHom (Fin 5) f
  obtain ⟨j, hj⟩ := S.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card (Fin 5)
    (by simp)
  refine ⟨j, ?_⟩
  intro x hx
  apply mem_map_of_mem max4Subgroup.subtype (x := ⟨x, hS hx⟩)
  exact ⟨hj ⟨x, hx⟩, mem_top _⟩

private lemma pointParabolic_card (j : Fin 5) : Nat.card (pointParabolic j) = 2 ^ 21 * 63 := by
  let J := ((MulAction.stabilizer (Equiv.Perm (Fin 5)) j).prod
    (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))).comap max4Projection
  have hi : J.index = 5 := by
    rw [index_comap_of_surjective _ max4Projection_surjective, index_prod, index_top, mul_one]
    rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ]
    simp
  have hc := J.card_mul_index
  rw [hi, max4_card] at hc
  change Nat.card (J.map max4Subgroup.subtype) = _
  rw [card_map_of_injective max4Subgroup.subtype_injective]
  omega

private lemma pointParabolic_sylow_index (j : Fin 5) (S : Sylow 2 Model)
    (hS : (S : Subgroup Model) ≤ pointParabolic j) :
    (S : Subgroup Model).relIndex (pointParabolic j) = 63 := by
  let R := S.subtype hS
  have hc : Nat.card R = 2 ^ 21 := by
    rw [R.card_eq_multiplicity, pointParabolic_card]
    decide +kernel
  have he := (R : Subgroup (pointParabolic j)).card_mul_index
  rw [hc, pointParabolic_card] at he
  change 2 ^ 21 * (S : Subgroup Model).relIndex (pointParabolic j) = _ at he
  omega

open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open MathieuHallActors

private lemma trio_of_max4_embedding (S : Sylow 2 Model) (P : Subgroup Model)
    (hSP : (S : Subgroup Model) ≤ P) (hPM : P ≤ M)
    (hi : (S : Subgroup Model).relIndex P = 63)
    (f0 : P →* max4Subgroup) (hf0 : Function.Injective f0) :
    ∃ g : Sporadic.Mathieu.M24,
      P.subgroupOf M = (trioStabilizer standardTrio).comap
        ((MulAut.conj g).toMonoidHom.comp projection) := by
  let R := S.subtype (hSP.trans hPM)
  let J := P.subgroupOf M
  have hRJ : (R : Subgroup M) ≤ J := comap_mono hSP
  have hkernel : IsPGroup 2 projection.ker := by
    rw [projection_ker, localKernel_eq_twoCore]
    exact pCore_isPGroup
  have hkR : projection.ker ≤ (R : Subgroup M) := hkernel.le_sylow_of_normal R
  let Q := R.mapSurjective projection_surjective
  let X := J.map projection
  have hQX : (Q : Subgroup Sporadic.Mathieu.M24) ≤ X := map_mono hRJ
  have hrel : (Q : Subgroup Sporadic.Mathieu.M24).relIndex X = 63 := by
    change ((R : Subgroup M).map projection).relIndex (J.map projection) = 63
    rw [relIndex_map_map, sup_eq_left.mpr hkR, sup_eq_left.mpr (hkR.trans hRJ)]
    change ((S : Subgroup Model).subgroupOf M).relIndex (P.subgroupOf M) = 63
    rw [relIndex_subgroupOf hPM]
    exact hi
  have hcore : pCore 2 X ≠ ⊥ := by
    intro hz
    let f : J →* max4Subgroup := f0.comp
      (subgroupOfEquivOfLe hPM).toMonoidHom
    have hf : Function.Injective f := hf0.comp
      (subgroupOfEquivOfLe hPM).injective
    have hd := MonoidHom.card_corefree_quotient_dvd_of_embedding f hf
      (projection.subgroupMap J) (projection.subgroupMap_surjective J) hz
    rw [Nat.card_congr max4QuotientEquiv.toEquiv, quotientModel_card] at hd
    have h128 : 128 ∣ Nat.card Q := Q.pow_dvd_card_of_pow_dvd_card (n := 7)
      (by rw [Sporadic.Mathieu.m24_order]; decide)
    have bad := (h128.trans (card_dvd_of_le hQX)).trans hd
    norm_num at bad
  obtain ⟨g, hg⟩ := Sporadic.Mathieu.M24LocalGeometry.TrioRecognition.exists_conjugate_trio
    Q X hQX hcore hrel
  refine ⟨g, ?_⟩
  rw [← hg, ← comap_comap, comap_map_eq_self_of_injective (MulAut.conj g).injective]
  exact (comap_map_eq_self (hkR.trans hRJ)).symm

private lemma trio_preimages_eq (S : Sylow 2 Model) (H J : Subgroup M)
    (hSH : (S : Subgroup Model) ≤ H.map (M).subtype)
    (hSJ : (S : Subgroup Model) ≤ J.map (M).subtype)
    (g h : Sporadic.Mathieu.M24)
    (hH : H = (trioStabilizer standardTrio).comap
      ((MulAut.conj g).toMonoidHom.comp projection))
    (hJ : J = (trioStabilizer standardTrio).comap
      ((MulAut.conj h).toMonoidHom.comp projection)) : H = J := by
  obtain ⟨a, ha⟩ := projection_surjective (h⁻¹ * g)
  have he : H.map (MulAut.conj a).toMonoidHom = J := by
    apply (comap_injective (f := (MulAut.conj a).toMonoidHom) (MulAut.conj a).surjective)
    rw [comap_map_eq_self_of_injective (MulAut.conj a).injective, hH, hJ]
    ext x
    simp only [mem_comap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, map_mul, map_inv, ha, mul_inv_rev, inv_inv,
      mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left]
  have hmap : (H.map (M).subtype).map (MulAut.conj (a : Model)).toMonoidHom = J.map (M).subtype := by
    have hf : (MulAut.conj (a : Model)).toMonoidHom.comp (M).subtype =
        (M).subtype.comp (MulAut.conj a).toMonoidHom := by ext x; rfl
    rw [map_map, hf, ← map_map, he]
  have heq := S.conjugate_overgroup_eq (H.map (M).subtype) hSH
    (by rw [Janko4.sylow_normalizer_eq]; exact hSH) (a : Model) (hmap.symm ▸ hSJ)
  exact (map_injective (M).subtype_injective) (hmap.symm.trans heq).symm

private lemma conj_map_map (H : Subgroup Model) (a b : Model) :
    (H.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

/-- A conjugate max4 point parabolic sharing the specified full Sylow with
native max1 lies in that very max1. -/
theorem conjugate_pointParabolic_le_mathieu (j : Fin 5) (a : Model) (S : Sylow 2 Model)
    (hSP : (S : Subgroup Model) ≤ (pointParabolic j).map (MulAut.conj a).toMonoidHom)
    (hSM : (S : Subgroup Model) ≤ M) :
    (pointParabolic j).map (MulAut.conj a).toMonoidHom ≤ M := by
  let c := MulAut.conj a
  have hc : c.symm.toMonoidHom.comp c.toMonoidHom = MonoidHom.id Model := by
    ext x
    exact c.symm_apply_apply x
  let R := S.mapSurjective (f := c.symm.toMonoidHom) c.symm.surjective
  have hRP : (R : Subgroup Model) ≤ pointParabolic j := by
    change (S : Subgroup Model).map c.symm.toMonoidHom ≤ pointParabolic j
    have hh := map_mono (f := c.symm.toMonoidHom) hSP
    change (S : Subgroup Model).map c.symm.toMonoidHom ≤ ((pointParabolic j).map c.toMonoidHom).map c.symm.toMonoidHom at hh
    simpa only [map_map, hc, map_id] using hh
  obtain ⟨b, hb⟩ := pointParabolic_le_conjugate_mathieu j R hRP
  have hh := map_mono (f := c.toMonoidHom) hb
  change (pointParabolic j).map (MulAut.conj a).toMonoidHom ≤ _ at hh
  rw [conj_map_map] at hh
  have he := S.conjugate_overgroup_eq M hSM
    (by rw [Janko4.sylow_normalizer_eq]; exact hSM) (a * b) (hSP.trans hh)
  exact hh.trans_eq he

/-- The original trio preimage lies in any conjugate native max4 containing
its specified full Sylow; the whole parabolic is retained. -/
theorem trio_preimage_le_conjugate_max4 (S : Sylow 2 Model) (H : Subgroup Model)
    (hSH : (S : Subgroup Model) ≤ H) (hHM : H ≤ M) (a : Model)
    (hSM4 : (S : Subgroup Model) ≤ max4Subgroup.map (MulAut.conj a).toMonoidHom)
    (g : Sporadic.Mathieu.M24)
    (hH : H = ((trioStabilizer standardTrio).comap
      ((MulAut.conj g).toMonoidHom.comp projection)).map (M).subtype) :
    H ≤ max4Subgroup.map (MulAut.conj a).toMonoidHom := by
  let c := MulAut.conj a
  have hc : c.symm.toMonoidHom.comp c.toMonoidHom = MonoidHom.id Model := by
    ext x
    exact c.symm_apply_apply x
  let R := S.mapSurjective (f := c.symm.toMonoidHom) c.symm.surjective
  have hRM4 : (R : Subgroup Model) ≤ max4Subgroup := by
    change (S : Subgroup Model).map c.symm.toMonoidHom ≤ max4Subgroup
    have hh := map_mono (f := c.symm.toMonoidHom) hSM4
    change (S : Subgroup Model).map c.symm.toMonoidHom ≤ (max4Subgroup.map c.toMonoidHom).map c.symm.toMonoidHom at hh
    simpa only [map_map, hc, map_id] using hh
  obtain ⟨j, hRP⟩ := sylow_le_pointParabolic R hRM4
  let P := (pointParabolic j).map c.toMonoidHom
  have hc' : c.toMonoidHom.comp c.symm.toMonoidHom = MonoidHom.id Model := by
    ext x
    exact c.apply_symm_apply x
  have hSP : (S : Subgroup Model) ≤ P := by
    have hh := map_mono (f := c.toMonoidHom) hRP
    change ((S : Subgroup Model).map c.symm.toMonoidHom).map c.toMonoidHom ≤ P at hh
    simpa only [map_map, hc', map_id] using hh
  have hPM := conjugate_pointParabolic_le_mathieu j a S hSP (hSH.trans hHM)
  have hidx : (S : Subgroup Model).relIndex P = 63 := by
    have he := relIndex_map_map_of_injective (f := c.symm.toMonoidHom)
      (S : Subgroup Model) P c.symm.injective
    have hP : P.map c.symm.toMonoidHom = pointParabolic j := by
      change ((pointParabolic j).map c.toMonoidHom).map c.symm.toMonoidHom = _
      simp only [map_map, hc, map_id]
    rw [hP] at he
    exact he.symm.trans (pointParabolic_sylow_index j R hRP)
  let f : P →* max4Subgroup := (inclusion (pointParabolic_le j)).comp
    (c.subgroupMap (pointParabolic j)).symm.toMonoidHom
  have hf : Function.Injective f := (inclusion_injective (pointParabolic_le j)).comp
    (c.subgroupMap (pointParabolic j)).symm.injective
  obtain ⟨h, hh⟩ := trio_of_max4_embedding S P hSP hPM hidx f hf
  have hH' : H.subgroupOf M = (trioStabilizer standardTrio).comap
      ((MulAut.conj g).toMonoidHom.comp projection) := by
    rw [hH]
    exact comap_map_eq_self_of_injective (M).subtype_injective _
  have he := trio_preimages_eq S (H.subgroupOf M) (P.subgroupOf M)
    (by rwa [map_subgroupOf_eq_of_le hHM]) (by rwa [map_subgroupOf_eq_of_le hPM]) g h hH' hh
  have he' := congrArg (map (M).subtype) he
  rw [map_subgroupOf_eq_of_le hHM, map_subgroupOf_eq_of_le hPM] at he'
  exact he'.trans_le (map_mono (pointParabolic_le j))

end Janko4.LocalStructure.SymmetricLinear
