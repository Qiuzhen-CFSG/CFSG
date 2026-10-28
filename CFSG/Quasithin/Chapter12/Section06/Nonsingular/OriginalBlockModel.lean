module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalBlock
public import CFSG.Quasithin.ChapterC.Section01.BlockCoreCentralConjugation

/-!
# The original A8-block and its unchanged module

Short-group irreducibility and the full movement of the chosen V identify
U(L) with that same V. The full core then satisfies [Q,L]=V, the action
identity used in 12.6.16(2). Transport the actual fixed denominator and the
given orthogonal marking to construct an equivariant block model, retaining
the original map L/O2(L) to A8.

The preferred-point application constructs both O^2(X)'s A3-block and L's
A8-block, with relative subnormality inside LT and all original point,
Sylow, core, quotient and generation data. This establishes the block
construction in 12.6.18(1) under the proved normalizer escape. The remaining
12.6.16(2) contradiction, HS/J4 exclusions, canonical-module analysis,
splitting and fixed-space elimination are still required; neither 12.6.2
nor 12.6.23 is asserted. Earlier invariance/TI retain qt-d-1222-source and
final discharge remains with qt-d-12634-source.
Source: Aschbacher--Smith 12.6.16(2) and 12.6.18(1), printed pp.826--827,
combined manuscript of 1 March 2004.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

omit [IsElementaryAbelian 2 V] in
/-- In the short branch the block layer is exactly the original chosen V. -/
theorem SourceHypothesis.original_block_layer
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (hs : ChapterC.IsShort L) :
    (ChapterC.blockU L).map L.subtype = V := by
  let A := V.subgroupOf L
  let : A.Normal := normal_subgroupOf_of_le_normalizer H.chosen.normalizes
  have hVU : V ≤ (ChapterC.blockU L).map L.subtype := by
    rw [ChapterC.blockU,map_commutator,←MonoidHom.range_eq_map,range_subtype,
      H.chosen.eq_commutator]
    exact commutator_mono H.chosen.le_componentCore le_rfl
  have hAU : A ≤ ChapterC.blockU L := by
    rw [←comap_map_eq_self_of_injective L.subtype_injective (ChapterC.blockU L)]
    exact comap_mono hVU
  rcases hs.normal_core_dichotomy A hAU with hz | hu
  · have hcent : V ≤ centralizer (L : Set G) := by
      intro v hv l hl
      exact congrArg L.subtype (mem_center_iff.mp (hz (show (⟨v,H.chosen.le_component hv⟩ : L) ∈ A from hv)) ⟨l,hl⟩)
    exact (H.chosen.ne_bot (H.chosen.eq_commutator.trans
      (commutator_eq_bot_iff_le_centralizer.mpr hcent))).elim
  · apply le_antisymm _ hVU
    have hm := map_mono (f := L.subtype) hu
    rwa [map_subgroupOf_eq_of_le H.chosen.le_component] at hm


omit [IsElementaryAbelian 2 V] in
/-- The full original core has exactly V as its L-commutator layer in the
block branch. This is the action premise used in source12.6.16(2). -/
theorem SourceHypothesis.original_core_commutator_of_short
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (hs : ChapterC.IsShort L) : ⁅Q T L,L⁆ = V := by
  have hJM : LT T L ≤ normalizer (L : Set G) :=
    sup_le L.le_normalizer H.chosen.sylow_normalizes_component
  have hQL : Q T L ≤ normalizer (L : Set G) := (pCoreIn_le 2 _).trans hJM
  have hLQ : L ≤ normalizer (Q T L : Set G) :=
    (show L ≤ LT T L from le_sup_left).trans ((LT T L).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (LT T L) (pCore 2 (LT T L))))
  have hcomm : ⁅Q T L,L⁆ ≤ L.pCoreIn 2 :=
    le_pCoreIn_of_normalizes
      ((isPGroup_pCoreIn 2 _).to_le (le_normalizer_iff_commutator_le_left.mp hLQ))
      (le_normalizer_iff_commutator_le_right.mp hQL)
      (normalizer_commutator_ge_right (Q T L) L)
  have hid := commutator_isPPerfect_idempotent L (Q T L) hs.twoPerfect
    (isPGroup_pCoreIn 2 _) hLQ
  have hV : ⁅L.pCoreIn 2,L⁆ = V := by
    simpa only [ChapterC.blockU,pCoreIn,map_commutator,←MonoidHom.range_eq_map,range_subtype]
      using H.original_block_layer hs
  apply le_antisymm ((hid.symm.le.trans (commutator_mono hcomm le_rfl)).trans_eq hV)
  rw [H.chosen.eq_commutator]
  exact commutator_mono H.chosen.le_core le_rfl

/-- The original orthogonal marking identifies the intrinsic block module,
including its fixed denominator, with the natural A8 module. -/
def OrthogonalMarking.originalBlockModel
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (hq : IsQuasisimple (Star L))
    (hu : (ChapterC.blockU L).map L.subtype = V) :
    ChapterC.BlockModuleModel L
      ((BinaryPermutation.naturalMulAction (Fin 8)).comp (alternatingGroup (Fin 8)).subtype) := by
  let eU : ChapterC.blockU L ≃* V :=
    ((ChapterC.blockU L).equivMapOfInjective L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr hu)
  let fV : V →* Multiplicative (BinaryPermutation.natural (Fin 8)) := {
    toFun := fun v => Multiplicative.ofAdd (D.coordinates
      (Submodule.Quotient.mk (Additive.ofMul v)))
    map_one' := by change D.coordinates 0 = 0; exact map_zero _
    map_mul' := by
      intro v w
      change D.coordinates (Submodule.Quotient.mk (Additive.ofMul v + Additive.ofMul w)) = _
      rw [Submodule.Quotient.mk_add,map_add]
      rfl }
  let f := fV.comp eU.toMonoidHom
  have hfV : Function.Surjective fV := by
    intro w
    obtain ⟨q,hq⟩ := D.coordinates.surjective w.toAdd
    obtain ⟨v,hv⟩ := (fixedSeed L V chosen.normalizes).toSubmodule.mkQ_surjective q
    exact ⟨v.toMul,congrArg Multiplicative.ofAdd ((congrArg D.coordinates hv).trans hq)⟩
  have hf : Function.Surjective f := hfV.comp eU.surjective
  have hk : f.ker = ChapterC.blockFixed L := by
    ext u
    change D.coordinates (Submodule.Quotient.mk (Additive.ofMul (eU u))) = 0 ↔
      (u : L) ∈ center L
    rw [D.coordinates.map_eq_zero_iff,Submodule.Quotient.mk_eq_zero,
      mem_fixedSeed_iff L V chosen.normalizes]
    constructor
    · intro h
      apply mem_center_iff.mpr
      intro l
      exact Subtype.ext (h.2 l l.property)
    · intro h
      exact ⟨(eU u).property,fun l hl => congrArg L.subtype (mem_center_iff.mp h ⟨l,hl⟩)⟩
  let em : ChapterC.BlockModule L ≃* Multiplicative (BinaryPermutation.natural (Fin 8)) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  exact {
    quotientIso := D.coreQuotientEquiv chosen hq
    moduleIso := em
    intertwining := by
      intro l u
      change f (ChapterC.blockConjugate L l u) =
        BinaryPermutation.naturalMulAction (Fin 8)
          ((D.coreQuotientEquiv chosen hq (QuotientGroup.mk' (pCore 2 L) l)) :
            Equiv.Perm (Fin 8)) (f u)
      rw [D.coreQuotientEquiv_mk chosen hq]
      apply Multiplicative.toAdd.injective
      change D.coordinates (Submodule.Quotient.mk
        (Additive.ofMul (eU (ChapterC.blockConjugate L l u)))) = _
      have he : eU (ChapterC.blockConjugate L l u) = conjugation L V chosen.normalizes l (eU u) :=
        Subtype.ext rfl
      rw [he]
      exact D.equivariant l (Submodule.Quotient.mk (Additive.ofMul (eU u))) }

/-- The short structure and actual marking give the full A8-block type. -/
theorem SourceHypothesis.original_alternating_block_of_short
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hs : ChapterC.IsShort L) : ChapterC.IsAlternatingBlock L 8 := by
  refine ⟨by decide,hs,((BinaryPermutation.naturalMulAction (Fin 8)).comp
    (alternatingGroup (Fin 8)).subtype),⟨D.originalBlockModel H.chosen H.source.quasisimple
      (H.original_block_layer hs)⟩,?_⟩
  intro g v
  rfl

/-- Source12.6.18(1) under the original proved normalizer escape, with the
same original V and fixed-space quotient. -/
theorem SourceHypothesis.nonsingular_original_alternating_block
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (v : V) (hv : D.Nonsingular v)
    (hn : ¬ normalizer (Rv T L (v : G) : Set G) ≤ M L) :
    ChapterC.IsAlternatingBlock L 8 ∧ (ChapterC.blockU L).map L.subtype = V := by
  have hs := H.nonsingular_original_short D hTV v hv hn
  exact ⟨H.original_alternating_block_of_short D hs,H.original_block_layer hs⟩


/-- The preferred point constructs both the literal cubic block and the
original A8-block, including relative subnormality in LT and its exact V. -/
theorem SourceHypothesis.exists_preferred_nonsingular_original_blocks_of_fixed
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hz : ZV L V ≠ ⊥)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ChapterC.IsBlock (L.subgroupOf (LT T L)) ∧
      ChapterC.IsAlternatingBlock L 8 ∧ (ChapterC.blockU L).map L.subtype = V ∧
      ⁅Q T L,L⁆ = V ∧
      ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
        Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
        (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
        Lv L (w : G) < Kv (w : G) ∧ ¬ Kv (w : G) ≤ M L ∧
        V ⊓ centralizer (Kv (w : G) : Set G) = zpowers (w : G) ∧
        ¬ IsQuasisimple (Kv (w : G)) ∧
        ¬ normalizer (Rv T L (w : G) : Set G) ≤ M L ∧
        Q T L < Rv T L (w : G) ∧
        (Q T L).relIndex (Rv T L (w : G)) = 2 ∧
        L ⊔ Rv T L (w : G) = LT T L ∧
        ∃ X : Subgroup G, X ≤ LT T L ∧ Rv T L (w : G) ≤ X ∧
          X.pCoreIn 2 = Q T L ∧ Nonempty (Star X ≃* Equiv.Perm (Fin 3)) ∧
          Chapter1.IsSylowIn 2 (Rv T L (w : G)) X ∧
          X ⊔ (LT T L ⊓ Gv (w : G)) = LT T L ∧
          IsElementaryAbelian 2 (pCore 2 (pResidual 2 X)) ∧
          Nat.card (pCore 2 (pResidual 2 X)) = 4 ∧
          Nat.card (pResidual 2 X ⧸ pCore 2 (pResidual 2 X)) = 3 ∧
          ChapterC.IsBlock (pResidual 2 X) ∧
          ChapterC.IsAlternatingBlock (pResidual 2 X) 3 := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,hline,hnq,hn,hr,hidx,hjoin,X,hX,hRX,hcore,hq,hSyl,hgen,_⟩ :=
    H.exists_preferred_nonsingular_three_overgroup_of_fixed D hTV hTI hz v hv he
  have hb := H.nonsingular_three_residual_block w hn X hX hRX hq hSyl hgen
  have hshort := H.nonsingular_short_of_three_block D X hX (hr.le.trans hRX) hb.2.2.2.1.short hb.2.2.1
  let C := L.subgroupOf (LT T L)
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer H.chosen.sylow_normalizes_component)
  have hc : ChapterC.IsBlock C := ⟨inferInstance,hshort.of_mulEquiv
    (subgroupOfEquivOfLe (show L ≤ LT T L from le_sup_left)).symm,
    (inferInstance : C.Normal).isSubnormal⟩
  exact ⟨hc,H.original_alternating_block_of_short D hshort,H.original_block_layer hshort,
    H.original_core_commutator_of_short hshort,w,hw,he,hs,hi,hlt,hnot,hline,hnq,hn,hr,hidx,hjoin,X,hX,hRX,hcore,hq,hSyl,hgen,hb⟩

end CFSG.Quasithin.Chapter12.Section06
