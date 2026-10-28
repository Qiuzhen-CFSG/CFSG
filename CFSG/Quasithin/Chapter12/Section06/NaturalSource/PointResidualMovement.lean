module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.PointResidual
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.FourBlockSylowMovement
public import Theory.GroupTheory.PResidual.CoreCentralizer
public import Theory.GroupTheory.PCoreRestriction
/-!
# Nontriviality of the original residual-nine action

The original T ∩ L acts nontrivially on L₁/O₂(L₁). Otherwise the Sylow
intersection in C_L(z) would centralize its two-residual modulo the
point-centralizer two-core, and the residual centralizer criterion would
place that Sylow in O₂(C_L(z)). Its image under the actual marked point
stabilizer surjection contradicts the explicit even four-block model.

Intersecting any overgroup's two-core with L₁ transfers the obstruction
to that overgroup. The exchanged Borel application in AbelianExchangedFour
uses this with the same B = K₀ ∩ M and the original T ∩ L. The kernels
L₁ ∩ O₂(L) and O₂(L₁) are never identified.

Source: Aschbacher--Smith 12.6.31, printed pp.836--837, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis K T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The original Sylow intersection moves the intrinsic residual-nine quotient. -/
theorem SourceHypothesis.original_point_residual_not_centralized
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G)) :
    ¬ ⁅(T : Subgroup G) ⊓ L,(D.fullSetup hZ T z).L₁⁆ ≤
      (D.fullSetup hZ T z).L₁.pCoreIn 2 := by
  intro hc
  let E := D.fullSetup hZ T z
  let C := L ⊓ E.Gz
  have hTC : (T : Subgroup G) ≤ E.Gz := hTz.trans
    (normalizer_le_centralizer_of_card_two E.V₁ (E.point_card hz))
  have hnC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf S.chosen.sylow_normalizes_component (hTC.trans E.Gz.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  let J := C ⊔ (T : Subgroup G)
  have hCJ : C ≤ J := le_sup_left
  let : (C.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le C.le_normalizer hnC)
  obtain ⟨P₀,hP₀⟩ := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).exists_subgroupOf_eq_of_normal
    (C.subgroupOf J)
  let e := subgroupOfEquivOfLe hCJ
  let P := P₀.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP : (P : Subgroup C) = (T : Subgroup G).subgroupOf C := by
    change (P₀ : Subgroup (C.subgroupOf J)).map e.toMonoidHom = _
    rw [hP₀]
    ext c
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ha
    · intro ht
      exact ⟨⟨⟨c,hCJ c.property⟩,c.property⟩,ht,rfl⟩
  have hcore : E.L₁.pCoreIn 2 ≤ C.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes (map_subtype_le _)
      (C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pResidual 2 C)))
  have hp : (P : Subgroup C) ≤ pCore 2 C := by
    apply pSubgroup_le_pCore_of_commutator_pResidual_le _ P.isPGroup'
    apply (map_le_map_iff_of_injective C.subtype_injective).mp
    rw [map_commutator,hP,subgroupOf_map_subtype]
    exact ((commutator_mono (inf_le_inf_left _ inf_le_left) le_rfl).trans hc).trans hcore
  obtain ⟨_,f,hf,_,_⟩ := S.original_point_stabilizer_map D hZ z hz hTz
  have hm : (pCore 2 C).map f ≤ pCore 2 BinaryPermutation.TerminalOrthogonal.FourBlockResidual.P :=
    le_sSup ⟨(inferInstance : (pCore 2 C).Normal).map f hf,pCore_isPGroup.map f⟩
  exact BinaryPermutation.TerminalOrthogonal.FourBlockResidual.sylow_not_le_core
    (P.mapSurjective (f := f) hf) ((map_mono hp).trans hm)
/-- The same original actor cannot fix an overgroup of L₁ modulo its two-core. -/
theorem SourceHypothesis.original_point_residual_not_centralized_in_overgroup
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (B : Subgroup G) (hLB : (D.fullSetup hZ T z).L₁ ≤ B) :
    ¬ ⁅(T : Subgroup G) ⊓ L,B⁆ ≤ B.pCoreIn 2 := by
  intro hc
  let E := D.fullSetup hZ T z
  let C := L ⊓ E.Gz
  have hTC : (T : Subgroup G) ≤ E.Gz := hTz.trans
    (normalizer_le_centralizer_of_card_two E.V₁ (E.point_card hz))
  have hTL : (T : Subgroup G) ⊓ L ≤ C := le_inf inf_le_right (inf_le_left.trans hTC)
  have hn : (T : Subgroup G) ⊓ L ≤ normalizer (E.L₁ : Set G) := hTL.trans
    (C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pResidual 2 C)))
  exact S.original_point_residual_not_centralized D hZ z hz hTz
    ((le_inf (le_normalizer_iff_commutator_le_right.mp hn)
      ((commutator_mono le_rfl hLB).trans hc)).trans (inf_pCoreIn_le_of_le 2 hLB))
end CFSG.Quasithin.Chapter12.Section06
