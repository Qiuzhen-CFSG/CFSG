module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalBlockModel
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.A6Irreducibility

/-!
# The literal nonsingular A6-block inside the original A8-block

The compatible six-letter and eight-letter maps put O2(L_v) inside Q.
When L is short, [Q,L]=V and two-perfect commutator idempotence identify
U(L_v) with the original V_v=[V,L_v]. The existing augmentation-core
coordinates then identify its actual fixed quotient with the natural
A6 module. Its irreducibility and the already proved characteristic-two
structure give every shortness clause, hence the genuine A6-block type.

ResidualBlock propagates this local block to K_v and constructs the
canonical-module containment. The quotient here is U(L_v)/C_{U(L_v)}(L_v);
V and its original fixed-space projection have not been replaced.
Source: Aschbacher--Smith, 12.6.18, printed p.827, combined manuscript
of 1 March 2004, with C.1.7 and C.1.12, printed pp.123--124.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation BinaryPermutation BinaryPermutation.EightNonsingular
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original quotient kernels place the local two-core inside the original Q. -/
theorem SourceHypothesis.nonsingular_local_core_le_original_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v) :
    (Lv L (v : G)).pCoreIn 2 ≤ Q T L := by
  obtain ⟨i,j,hij,hp⟩ := nonsingular_pair _ hv
  rintro _ ⟨a,ha,rfl⟩
  have ha6 : D.localSixMap v i j hij hp a = 1 := by
    change a ∈ (D.localSixMap v i j hij hp).ker
    rwa [D.localSixMap_ker H.chosen H.source.quasisimple v i j hij hp]
  have haP : D.localPairMap v i j hij hp a = 1 :=
    (pointFixerEquiv i j hij).injective (ha6.trans (pointFixerEquiv i j hij).map_one.symm)
  have ha8 : D.actorMap (inclusion (Lv_le_L L (v : G)) a) = 1 :=
    congrArg Subtype.val haP
  have haL : inclusion (Lv_le_L L (v : G)) a ∈ pCore 2 L := by
    rw [←D.actorMap_ker H.chosen H.source.quasisimple]
    exact ha8
  have hL : L.pCoreIn 2 ≤ Q T L := pCoreAmbient_mono_of_isSubnormalIn L (LT T L) 2
    le_sup_left (normal_subgroupOf_of_le_normalizer
      (sup_le L.le_normalizer H.chosen.sylow_normalizes_component)).isSubnormal
  exact hL (mem_map_of_mem L.subtype haL)

/-- Shortness of L identifies the actual intrinsic local layer with V_v. -/
theorem SourceHypothesis.nonsingular_local_block_layer
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hshort : ChapterC.IsShort L) (v : V) (hv : D.Nonsingular v) :
    (ChapterC.blockU (Lv L (v : G))).map (Lv L (v : G)).subtype = Vv L V (v : G) := by
  let A := Lv L (v : G)
  have hcore : A.pCoreIn 2 ≤ Q T L := H.nonsingular_local_core_le_original_core D v hv
  have hp : IsPPerfect 2 A := isPPerfect_embedded_pResidual 2 (CLv L (v : G))
  have hn : A ≤ normalizer (A.pCoreIn 2 : Set G) :=
    A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  have hid := commutator_isPPerfect_idempotent A (A.pCoreIn 2) hp (isPGroup_pCoreIn 2 A) hn
  have hc : ⁅A.pCoreIn 2,A⁆ ≤ V :=
    (commutator_mono hcore (Lv_le_L L (v : G))).trans_eq (H.original_core_commutator_of_short hshort)
  rw [ChapterC.blockU,map_commutator,←MonoidHom.range_eq_map,range_subtype]
  apply le_antisymm
  · exact hid.symm.le.trans (commutator_mono hc le_rfl)
  · rw [←D.local_moved_generated H.chosen v hv]
    exact commutator_mono (Vv_le_core_Lv H.chosen v) le_rfl

/-- The intrinsic local block module retains the original six-letter action and its fixed kernel. -/
theorem OrthogonalMarking.local_block_model
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes) (hq : IsQuasisimple (Star L))
    (v : V) (hv : D.Nonsingular v)
    (hu : (ChapterC.blockU (Lv L (v : G))).map (Lv L (v : G)).subtype = Vv L V (v : G)) :
    ChapterC.IsLinearBlockModel (Lv L (v : G))
      ((naturalRepresentation (Fin 6)).comp (alternatingGroup (Fin 6)).subtype) := by
  let A := Lv L (v : G)
  let W := Vv L V (v : G)
  let := Vv_elementary chosen.normalizes (v : G)
  obtain ⟨i,j,hij,hp⟩ := nonsingular_pair _ hv
  obtain ⟨E,hE,_⟩ := D.local_core_marking chosen v i j hij hp
  let β := D.localSixMap v i j hij hp
  let eU : ChapterC.blockU A ≃* W :=
    ((ChapterC.blockU A).equivMapOfInjective A.subtype A.subtype_injective).trans
      (MulEquiv.subgroupCongr hu)
  let fW : W →* Multiplicative (natural (Fin 6)) :=
    ((coreToNatural (Fin 6)).comp E.symm.toLinearMap).toAddMonoidHom.toMultiplicativeRight
  let f := fW.comp eU.toMonoidHom
  have hfW : Function.Surjective fW := coreToNatural_surjective.comp E.symm.surjective
  have hf : Function.Surjective f := hfW.comp eU.surjective
  have hz (x : core (Fin 6)) : coreToNatural (Fin 6) x = 0 ↔
      ∀ a : alternatingGroup (Fin 6), alternatingCoreRepresentation (Fin 6) a x = x := by
    change coreToNatural (Fin 6) x = 0 ↔
      ∀ a : alternatingGroup (Fin 6), coreRepresentation (Fin 6) a.val x = x
    rw [core_fixed_iff_constant (by simp : 3 ≤ Nat.card (Fin 6))]
    rw [←Subtype.val_inj]
    exact Submodule.Quotient.mk_eq_zero _
  have hk : f.ker = ChapterC.blockFixed A := by
    ext u
    change coreToNatural (Fin 6) (E.symm (Additive.ofMul (eU u))) = 0 ↔
      (u : A) ∈ center A
    rw [hz]
    constructor
    · intro h
      apply mem_center_iff.mpr
      intro l
      have hh := hE l (E.symm (Additive.ofMul (eU u)))
      rw [h (β l),E.apply_symm_apply] at hh
      have hh' := congrArg (fun z : Additive W => (z.toMul : G)) hh
      change ((u : A) : G) = (l : G) * (u : A) * (l : G)⁻¹ at hh'
      exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp hh'.symm)
    · intro h a
      obtain ⟨l,rfl⟩ := D.localSixMap_surjective v i j hij hp a
      apply E.injective
      rw [hE,E.apply_symm_apply]
      apply Additive.toMul.injective
      apply Subtype.ext
      change (l : G) * (u : A) * (l : G)⁻¹ = (u : A)
      have hh := congrArg A.subtype (mem_center_iff.mp h l)
      simp only [map_mul,subtype_apply] at hh
      rw [hh,mul_inv_cancel_right]
  let em : ChapterC.BlockModule A ≃* Multiplicative (natural (Fin 6)) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  refine ⟨(naturalMulAction (Fin 6)).comp (alternatingGroup (Fin 6)).subtype,
    ⟨{ quotientIso := D.localCoreQuotientEquiv chosen hq v i j hij hp
       moduleIso := em
       intertwining := ?_ }⟩,fun _ _ => rfl⟩
  intro l u
  change f (ChapterC.blockConjugate A l u) = naturalMulAction (Fin 6)
    ((D.localCoreQuotientEquiv chosen hq v i j hij hp (QuotientGroup.mk' (pCore 2 A) l)) :
      Equiv.Perm (Fin 6)) (f u)
  rw [D.localCoreQuotientEquiv_mk chosen hq]
  have he : E.symm (seedRepresentation A W (Lv_normalizes_Vv L V (v : G)) l
      (Additive.ofMul (eU u))) = alternatingCoreRepresentation (Fin 6) (β l)
        (E.symm (Additive.ofMul (eU u))) := by
    apply E.injective
    rw [E.apply_symm_apply,hE,E.apply_symm_apply]
  apply Multiplicative.toAdd.injective
  change coreToNatural (Fin 6) (E.symm (seedRepresentation A W
    (Lv_normalizes_Vv L V (v : G)) l (Additive.ofMul (eU u)))) = _
  rw [he]
  exact coreToNatural_equivariant _ _

/-- Once L is short, its literal nonsingular residual is an A6-block. -/
theorem SourceHypothesis.nonsingular_local_alternating_block
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hshort : ChapterC.IsShort L) (v : V) (hv : D.Nonsingular v) :
    ChapterC.IsAlternatingBlock (Lv L (v : G)) 6 := by
  let A := Lv L (v : G)
  let := Vv_elementary H.chosen.normalizes (v : G)
  have hUeq := H.nonsingular_local_block_layer D hshort v hv
  have hm := D.local_block_model H.chosen H.source.quasisimple v hv hUeq
  have hs := (H.nonsingular_local_faithful_signalizer D v hv).2.1
  let : IsElementaryAbelian 2 (ChapterC.blockU A) :=
    IsElementaryAbelian.of_injective
      (((MulEquiv.subgroupCongr hUeq).toMonoidHom).comp
        ((ChapterC.blockU A).equivMapOfInjective A.subtype A.subtype_injective).toMonoidHom)
      ((MulEquiv.subgroupCongr hUeq).injective.comp
        ((ChapterC.blockU A).equivMapOfInjective A.subtype A.subtype_injective).injective)
  obtain ⟨e⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
  let : Group.IsPerfect A := Lv_isPerfect_of_A6 L (v : G) e
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (A ⧸ pCore 2 A) := e.isSimpleGroup
  have hq : IsQuasisimple (A ⧸ pCore 2 A) := {
    toIsPerfect := inferInstance
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (Lv_coreQuotient_center_eq_bot_of_A6 L (v : G) e)).trans QuotientGroup.quotientBot).isSimpleGroup }
  refine ⟨by decide,{
    finite := inferInstance
    twoPerfect := hs.2.1
    fitting := hs.2.2
    elementary := inferInstance
    central := ?_
    quotient := Or.inl hq
    irreducible := hm.alternating_six_irreducible },hm⟩
  intro u hu r hr
  apply Subtype.ext
  have huW : (u : G) ∈ Vv L V (v : G) := hUeq ▸ mem_map_of_mem A.subtype hu
  have hred := D.local_residual_moved_isReduced H.chosen H.source.quasisimple v hv
  exact congrArg A.subtype (hred.le_centralizer_pCore
    (show u ∈ (Vv L V (v : G)).subgroupOf A from huW) r hr)

end CFSG.Quasithin.Chapter12.Section06
