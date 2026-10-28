module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.G2Selection.Action
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.G2Selection
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.MinimalReplacement
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.MovedSectionModel
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.G2Irreducibility
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.G2Source
public import Theory.ElementaryAbelian.Injective

/-!
# The binary G₂ terminal after whole-core reconstruction

Identify the intrinsic commutator core with the full original U_K. The
marked B.5 moving quotient then constructs the literal natural block model.
The original kernel makes this core elementary and central in O₂(K), so
all short-group clauses follow. The remaining source input is precisely
the whole-core equality supplied by the G₂ branch of C.1.32.

Source: Aschbacher--Smith C.1.32 and 13.6.22, printed pp.135--136 and 932.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.G2Selection
open ChapterC ChapterB.QuasisimpleSource ComponentSelection
open SourceContainment.LinearThree.CentralAction.ModuleAlternatives
open SourceTransferFields.RankOneBorel
variable {G : Type*} [Group G]
variable (K L T : Subgroup G) (z v : G)
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
variable (hz : Tv T v ≤ centralizer ({z} : Set G))
variable [IsElementaryAbelian 2 (WK K L T z v)]
  [(plusImage K L T z v hL hz K).Normal]

private def quotientMarking
    (hk : (centralizer (WK K L T z v : Set G)).subgroupOf K = pCore 2 K) :
    (K ⧸ pCore 2 K) ≃* plusImage K L T z v hL hz K :=
  (QuotientGroup.quotientMulEquivOfEq
    ((Replacement.MinimalGeometry.componentMap_ker K L T z v hL hz).trans hk).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (componentMap_surjective K L T z v hL hz))

private theorem quotientMarking_mk
    (hk : (centralizer (WK K L T z v : Set G)).subgroupOf K = pCore 2 K) (k : K) :
    quotientMarking K L T z v hL hz hk (QuotientGroup.mk' _ k) =
      componentMap K L T z v hL hz k := by
  unfold quotientMarking
  rfl

private def naturalSection
    (hK : K ≤ Gv v)
    (hk : (centralizer (WK K L T z v : Set G)).subgroupOf K = pCore 2 K)
    (he : (blockU K).map K.subtype = UK K L T z v)
    (m : Action.Data (wkRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz K)) :
    BinaryConjugationSection K (UK K L T z v)
      (UK K L T z v ⊓ centralizer (K : Set G))
      ((g2DerivedNatural (ZMod 2)).comp
        (((quotientMarking K L T z v hL hz hk).trans m.natural.groupEquiv).toMonoidHom.comp
          (QuotientGroup.mk' (pCore 2 K)))) := by
  let s := m.sectionData
  let E := movedEquivUK K L T z v hL hz s
  let f := m.natural.linearEquiv.toAddEquiv.toMultiplicative.toMonoidHom.comp
    (s.central.toSubmodule.mkQ.toAddMonoidHom.toMultiplicative.comp E.symm.toMonoidHom)
  refine {
    section_le := he ▸ map_subtype_le (blockU K)
    kernel_le := inf_le_left
    normalized := normalizer_commutator_ge_right _ _
    coordinates := f
    onto := m.natural.linearEquiv.surjective.comp
      (s.central.toSubmodule.mkQ_surjective.comp E.symm.surjective)
    kernel_eq := ?_
    equivariant := ?_ }
  · ext u
    change m.natural.linearEquiv (s.central.toSubmodule.mkQ (E.symm u).toAdd) = 0 ↔ _
    rw [m.natural.linearEquiv.map_eq_zero_iff]
    change (Submodule.Quotient.mk (E.symm u).toAdd = 0) ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    exact (mem_sectionCentral_iff K L T z v hL hz hK s (E.symm u).toAdd).trans
      (show (u : G) ∈ centralizer (K : Set G) ↔
        u ∈ (UK K L T z v ⊓ centralizer (K : Set G)).subgroupOf (UK K L T z v)
        from ⟨fun h => ⟨u.property,h⟩, fun h => h.2⟩)
  · intro k u
    change m.natural.linearEquiv (s.central.toSubmodule.mkQ (E.symm _).toAdd) =
      g2DerivedNatural (ZMod 2)
        (m.natural.groupEquiv (quotientMarking K L T z v hL hz hk (QuotientGroup.mk' _ k)))
        (m.natural.linearEquiv (s.central.toSubmodule.mkQ (E.symm u).toAdd))
    rw [quotientMarking_mk, ← m.natural.intertwines]
    apply congrArg m.natural.linearEquiv
    change s.central.toSubmodule.mkQ (E.symm _).toAdd =
      s.central.toSubmodule.mkQ
        (s.space.toRepresentation (componentMap K L T z v hL hz k) (E.symm u).toAdd)
    congr 1
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    change (k : G) * (u : G) * (k : G)⁻¹ =
      ((wkRepresentation K L T z v hL hz
        (plusMk K L T z v hL hz (inclusion (K_le_plusActor K L T v) k))
        (E.symm u).toAdd.val).toMul : G)
    rw [wkRepresentation_apply]
    rfl

/-- Whole-core reconstruction transports the actual natural quotient to the
intrinsic block module, retaining its original conjugation action. -/
theorem natural_block_model_of_core_identity
    (hK : K ≤ Gv v)
    (hk : (centralizer (WK K L T z v : Set G)).subgroupOf K = pCore 2 K)
    (he : (blockU K).map K.subtype = UK K L T z v)
    (m : Action.Data (wkRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz K)) :
    Nonempty (BlockModuleModel K g2TwoNaturalAction) := by
  exact ⟨blockModelOfIdentifiedMovedSection K (WK K L T z v) he
    ((quotientMarking K L T z v hL hz hk).trans m.natural.groupEquiv)
    (g2DerivedNatural (ZMod 2)) g2TwoNaturalAction (fun _ _ => rfl)
    (naturalSection K L T z v hL hz hK hk he m)⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.G2Selection
