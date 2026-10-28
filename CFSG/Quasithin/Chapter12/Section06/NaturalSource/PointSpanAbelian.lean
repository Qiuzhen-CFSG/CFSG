module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentElevenSaturation
public import Theory.SpecificGroups.AlternatingEight.CentralKernelBound
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Quotient

/-!
# Abelianness of the original point span

In the contrary branch, the proved [O₂(L),L]=V makes L/V a perfect
central cover of the marked A₈. Its central attachment has order at most
two. The original L₁ action has image A₄×A₄ and kernel L₁∩O₂(L).
That kernel meets V in a subgroup of V₅, so has order at most64.
The literal L₁/O₂(L₁) has order nine, giving |O₂(L₁)|≤2¹⁰.

This contradicts the proved lower bound2¹¹ on the same intrinsic core
and establishes V_H abelian. F.9 then gives U_H abelian, V≤O₂(H), and
V≤C_G(U_H). The original geometry assumptions remain explicit; the
later12.6.27--34 alternatives and universal natural reduction are separate.
The bound permits a central double attachment and suffices for the source
contradiction. Source: Aschbacher--Smith12.6.25--26, printed pp.831--833.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
  (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
include hz hTV hTz hbound hH hn in
/-- The actual central attachment above V has order at most two. -/
theorem SourceHypothesis.original_nonabelian_point_span_core_index
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    V.relIndex (L.pCoreIn 2) ≤ 2 := by
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect S.source.maximal_faithful.1.1
  let e := D.coreQuotientEquiv S.chosen S.source.quasisimple
  let f : PerfectCentralCovering.Cover (L ⧸ ChapterC.blockU L) (alternatingGroup (Fin 8)) := {
    toMonoidHom := e.toMonoidHom.comp ChapterC.blockCoreProjection
    surjective := e.surjective.comp ChapterC.blockCoreProjection_surjective
    isPerfect := inferInstance
    ker_le_center := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective,ChapterC.blockCoreProjection_ker]
      exact ChapterC.blockU_core_image_le_center }
  have hb := AlternatingEight.central_cover_kernel_card_le_two f
  change Nat.card ((e.toMonoidHom.comp ChapterC.blockCoreProjection).ker) ≤ 2 at hb
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective,ChapterC.blockCoreProjection_ker,
    ←relIndex_ker,QuotientGroup.ker_mk'] at hb
  have hu : (ChapterC.blockU L).map L.subtype = V := by
    simpa only [ChapterC.blockU,pCoreIn,map_commutator,←MonoidHom.range_eq_map,range_subtype]
      using S.original_nonabelian_point_span_original_core_commutator
        D hZ z hz hTV hTz hbound hH hn hTI hns
  have he := relIndex_map_map_of_injective (ChapterC.blockU L) (pCore 2 L) L.subtype_injective
  rw [hu] at he
  exact he ▸ hb

include hz hTV hTz hbound hH hn in
/-- Bound the literal kernel of the original L₁ action on the two four-block factors. -/
theorem SourceHypothesis.original_nonabelian_point_span_residual_kernel_card
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    Nat.card ((D.fullSetup hZ T z).L₁ ⊓ L.pCoreIn 2 : Subgroup G) ≤ 64 := by
  let E := D.fullSetup hZ T z
  let J := E.L₁ ⊓ L.pCoreIn 2
  have hL₁L : E.L₁ ≤ L := (map_subtype_le _).trans inf_le_left
  have hLQ : L ≤ normalizer (L.pCoreIn 2 : Set G) := L.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hJR : J ≤ E.L₁.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 L).to_le inf_le_right)
      inf_le_left ((le_inf E.L₁.le_normalizer (hL₁L.trans hLQ)).trans inf_normalizer_le_normalizer_inf)
  have hRH := (S.original_nonabelian_point_span_core_bounds
    D hZ z hz hTV hTz hbound hH hn hTI hns).2.1
  have hgeom := (S.original_nonabelian_geometry D hZ z hz hTV hTz hbound hH hn).2.2.1
  have hJV : V ⊓ J ≤ E.V₅ := (inf_le_inf_left V (hJR.trans hRH)).trans_eq hgeom
  let f : V.subgroupOf J → E.V₅ := fun x => ⟨x.val.val,hJV ⟨x.property,x.val.property⟩⟩
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun y : E.V₅ => (y : G)) he))
  have hc : Nat.card (V.subgroupOf J) ≤ 32 :=
    (Nat.card_le_card_of_injective f hf).trans_eq (E.perpendicular_card hz)
  have hi : V.relIndex J ≤ 2 :=
    (relIndex_le_of_le_right (H := V) (show J ≤ L.pCoreIn 2 from inf_le_right) index_ne_zero_of_finite).trans
      (S.original_nonabelian_point_span_core_index D hZ z hz hTV hTz hbound hH hn hTI hns)
  have hcount := (V.subgroupOf J).card_mul_index
  change Nat.card (V.subgroupOf J) * V.relIndex J = Nat.card J at hcount
  change Nat.card J ≤ 64
  rw [←hcount]
  exact (Nat.mul_le_mul hc hi).trans (by norm_num)

include hz hTV hTz hbound hH hn in
/-- The same intrinsic O₂(L₁) has order at most 2¹⁰. The possible central
attachment is retained, and the original four-block action supplies its index. -/
theorem SourceHypothesis.original_nonabelian_point_span_residual_core_card_le
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    Nat.card ((D.fullSetup hZ T z).L₁.pCoreIn 2) ≤ 2^10 := by
  let E := D.fullSetup hZ T z
  obtain ⟨_,f,hf,_,hk,_⟩ := S.original_point_residual_map D hZ z hz hTz
  have hker : Nat.card f.ker ≤ 64 := by
    rw [hk,←inf_subgroupOf_left (L.pCoreIn 2) E.L₁,
      Nat.card_congr (subgroupOfEquivOfLe (show E.L₁ ⊓ L.pCoreIn 2 ≤ E.L₁ from inf_le_left)).toEquiv]
    exact S.original_nonabelian_point_span_residual_kernel_card
      D hZ z hz hTV hTz hbound hH hn hTI hns
  have hindex : f.ker.index = 144 := by
    rw [index_eq_card,Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
    exact BinaryPermutation.TerminalOrthogonal.FourBlockResidual.R_card
  have htotal := f.ker.card_mul_index
  rw [hindex] at htotal
  have hLcard : Nat.card E.L₁ ≤ 64*144 := by nlinarith
  obtain ⟨_,_,_,e,_,_⟩ := S.original_point_residual_quotient D hZ z hz hTz
  have hqcard : Nat.card (E.L₁ ⧸ pCore 2 E.L₁) = 9 :=
    (Nat.card_congr e.toEquiv).trans BinaryPermutation.TerminalOrthogonal.FourBlockResidual.E9_card
  have hcount := card_eq_card_quotient_mul_card_subgroup (pCore 2 E.L₁)
  rw [hqcard] at hcount
  have he : Nat.card (E.L₁.pCoreIn 2) = Nat.card (pCore 2 E.L₁) :=
    (Nat.card_congr (equivMapOfInjective (pCore 2 E.L₁) E.L₁.subtype E.L₁.subtype_injective).toEquiv).symm
  change Nat.card (E.L₁.pCoreIn 2) ≤ 2^10
  rw [he]
  nlinarith

include hz hTV hTz hbound hH in
/-- The original point span is abelian: the PSL₂(11) branch forces incompatible
bounds on the same intrinsic residual core. Earlier geometry remains explicit. -/
theorem SourceHypothesis.original_point_span_abelian
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    IsMulCommutative ((D.fullSetup hZ T z).VH H) := by
  by_contra hn
  have hl := (S.original_nonabelian_point_span_core_bounds
    D hZ z hz hTV hTz hbound hH hn hTI hns).2.2
  have hu := S.original_nonabelian_point_span_residual_core_card_le
    D hZ z hz hTV hTz hbound hH hn hTI hns
  norm_num at hl hu
  omega

include hz hTV hTz hbound hH in
/-- The abelian branch of F.9 now applies to the unchanged original point setup. -/
theorem SourceHypothesis.original_abelian_point_geometry
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    IsMulCommutative ((D.fullSetup hZ T z).VH H) ∧
      IsMulCommutative ((D.fullSetup hZ T z).UH H) ∧
      V ≤ H.pCoreIn 2 ∧ V ≤ centralizer ((D.fullSetup hZ T z).UH H : Set G) := by
  have hv := S.original_point_span_abelian D hZ z hz hTV hTz hbound hH hTI hns
  have he := S.original_abelian_criteria D hZ z hz hTV hTz hbound hH
  have hu := he.2.2.mpr hv
  have hq := he.1.mp hu
  exact ⟨hv,hu,hq,he.2.1.mp hq⟩

end CFSG.Quasithin.Chapter12.Section06
