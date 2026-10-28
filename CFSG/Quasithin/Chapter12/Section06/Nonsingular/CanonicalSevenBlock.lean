module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.CanonicalSevenModule
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport

/-!
# The literal canonical A7 block

Natural coordinates on the full moved space identify the intrinsic block
module. The actor map is the original quotient by the two-core, and the
module map intertwines the original conjugation action. Relative normality
inside K_v S transports this identification to the original K_v.

The preferred-point consumer in PreferredCanonicalModule supplies shortness,
the canonical kernel and the intrinsic moved-layer identity. Its FF witness
remains explicit; this module does not establish source 12.6.2 or 12.6.23.
Source: Aschbacher--Smith, 12.6.18(2), printed p.827, with C.1.12,
combined manuscript of 1 March 2004.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open ChapterB.QuasisimpleSource

/-- Natural coordinates on the whole canonical moved space identify the
intrinsic block module, retaining its literal conjugation and two-core map. -/
theorem canonical_seven_alternating_block {A : Type*} [Group A] [Finite A]
    (E : Subgroup A) [E.Normal] [IsElementaryAbelian 2 E] (K : Subgroup A) [K.Normal]
    (hshort : ChapterC.IsShort K)
    (hker : centralizer (E : Set A) = pCore 2 A)
    (hlayer : (ChapterC.blockU K).map K.subtype = ⁅E,K⁆)
    (hmodel : CanonicalSevenMoved E K) : ChapterC.IsAlternatingBlock K 7 := by
  let := hshort.elementary
  let q := ChapterB.InternalThompsonAction.actionMk E
  let ρ := ChapterB.InternalThompsonAction.action E
  let B := K.map q
  let O := offenderSubgroup ρ
  let C := B.subgroupOf O
  obtain ⟨hBO,s,hs,⟨a⟩⟩ := hmodel
  have hspace : s.space.toSubmodule = subspaceCommutator ρ ⊤ B := by
    rw [s.space_eq]
    change subspaceCommutator (ρ.comp O.subtype) ⊤ C = _
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hBO]
  let W := (⁅E,K⁆ : Subgroup A)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left E K)
  let eU : ChapterC.blockU K ≃* W :=
    ((ChapterC.blockU K).equivMapOfInjective K.subtype K.subtype_injective).trans
      (MulEquiv.subgroupCongr hlayer)
  let u : Additive (ChapterC.blockU K) ≃ₗ[ZMod 2] Additive W :=
    { eU.toAdditive with map_smul' := fun c x => ZMod.map_smul eU.toAdditive c x }
  let m := (NormalElementaryQuotient.movedEquiv E q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) K).trans
      (LinearEquiv.ofEq _ _ hspace.symm)
  let l := (u.trans m).trans a.linearEquiv
  have hzero : ChapterC.blockFixed K = ⊥ := by
    apply bot_unique
    intro x hx
    have hxW : (eU x : A) ∈ W := (eU x).property
    have hxC : (eU x : A) ∈ centralizer (K : Set A) := by
      intro k hk
      exact congrArg K.subtype (mem_center_iff.mp hx ⟨k,hk⟩)
    have hh := (canonical_seven_moved_properties E K ⟨hBO,s,hs,⟨a⟩⟩).2.1.le ⟨hxW,hxC⟩
    exact Subtype.ext (Subtype.ext (show ((x : K) : A) = 1 from hh))
  have hk : (q.subgroupMap K).ker = pCore 2 K := by
    rw [Subgroup.ker_subgroupMap,QuotientGroup.ker_mk',hker]
    exact (pCore_subnormal_eq_comap 2 (inferInstance : K.Normal).isSubnormal).symm
  let f : (K ⧸ pCore 2 K) ≃* B :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (q.subgroupMap_surjective K))
  let eC : B ≃* C := (subgroupOfEquivOfLe hBO).symm
  let em : ChapterC.BlockModule K ≃* Multiplicative (BinaryPermutation.natural (Fin 7)) :=
    ((QuotientGroup.quotientMulEquivOfEq hzero).trans QuotientGroup.quotientBot).trans
      l.toAddEquiv.toMultiplicativeRight
  refine ⟨by decide,hshort,(BinaryPermutation.naturalMulAction (Fin 7)).comp
    (alternatingGroup (Fin 7)).subtype,
    ⟨{ quotientIso := f.trans (eC.trans a.groupEquiv)
       moduleIso := em
       intertwining := ?_ }⟩,fun _ _ => rfl⟩
  intro k x
  apply Multiplicative.toAdd.injective
  change l (Additive.ofMul (ChapterC.blockConjugate K k x)) =
    alternatingNatural 7 (a.groupEquiv (eC (q.subgroupMap K k))) (l (Additive.ofMul x))
  have hact : m (u (Additive.ofMul (ChapterC.blockConjugate K k x))) =
      s.space.toRepresentation (eC (q.subgroupMap K k)).val (m (u (Additive.ofMul x))) := by
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    change (k : A) * ((x : K) : A) * (k : A)⁻¹ =
      ((ChapterB.InternalThompsonAction.action E (q k)
        (Additive.ofMul ⟨(x : K),commutator_le_left E K (eU x).property⟩)).toMul : A)
    rw [ChapterB.InternalThompsonAction.action_apply]
    rfl
  change a.linearEquiv (m (u (Additive.ofMul (ChapterC.blockConjugate K k x)))) = _
  rw [hact]
  exact a.intertwines (eC (q.subgroupMap K k)) (m (u (Additive.ofMul x)))
/-- The A7 block is the original K_v, with relative normality inside K_v S. -/
theorem nonsingular_canonical_seven_block {G : Type*} [Group G] [Finite G]
    (v : G) (S : Subgroup G) (hS : S ≤ Gv v)
    (hshort : ChapterC.IsShort (Kv v))
    (hker : centralizer (reducedTwoSubgroup (Kv v ⊔ S : Subgroup G) :
      Set (Kv v ⊔ S : Subgroup G)) = pCore 2 (Kv v ⊔ S : Subgroup G))
    (hred : U (Kv v) S = (reducedTwoSubgroup (Kv v ⊔ S : Subgroup G)).map
      (Kv v ⊔ S : Subgroup G).subtype)
    (hlayer : ⁅U (Kv v) S,Kv v⁆ = (ChapterC.blockU (Kv v)).map (Kv v).subtype)
    (hmodel : let E := reducedTwoSubgroup (Kv v ⊔ S : Subgroup G)
      letI : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
      CanonicalSevenMoved E ((Kv v).subgroupOf (Kv v ⊔ S))) :
    ChapterC.IsAlternatingBlock (Kv v) 7 := by
  let J := Kv v ⊔ S
  let K := (Kv v).subgroupOf J
  let E := reducedTwoSubgroup J
  let : IsElementaryAbelian 2 E := isPReduced_reducedPSubgroup.elementary
  let e : K ≃* Kv v := subgroupOfEquivOfLe (show Kv v ≤ J from le_sup_left)
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    ((sup_le (Kv_le_Gv v) hS).trans
      ((normal_subgroupOf_iff_le_normalizer (Kv_le_Gv v)).mp (Kv_normalIn_Gv v)))
  have hu : (ChapterC.blockU K).map e.toMonoidHom = ChapterC.blockU (Kv v) := by
    rw [ChapterC.blockU,map_commutator,pCore_map_iso,
      map_top_of_surjective _ e.surjective,ChapterC.blockU]
  have hum : ((ChapterC.blockU K).map K.subtype).map J.subtype =
      (ChapterC.blockU (Kv v)).map (Kv v).subtype := by
    rw [map_map,show J.subtype.comp K.subtype = (Kv v).subtype.comp e.toMonoidHom from rfl,
      ←map_map,hu]
  have hl : (ChapterC.blockU K).map K.subtype = ⁅E,K⁆ := by
    apply map_injective J.subtype_injective
    rw [hum,map_commutator,map_subgroupOf_eq_of_le (show Kv v ≤ J from le_sup_left),←hred]
    exact hlayer.symm
  exact (canonical_seven_alternating_block E K (hshort.of_mulEquiv e.symm) hker hl hmodel).of_mulEquiv e

end CFSG.Quasithin.Chapter12.Section06
