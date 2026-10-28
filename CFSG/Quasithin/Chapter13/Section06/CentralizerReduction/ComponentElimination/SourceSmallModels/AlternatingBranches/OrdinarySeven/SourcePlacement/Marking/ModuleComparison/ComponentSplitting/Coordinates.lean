module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.ComponentSplitting.Cohomology
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.Construction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.BlockQuotient
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices.Covers.BlockCover

/-!
# The chosen ordinary A₇ block coordinates on U(K)

The source uses U = [Z(O₂(K)),K], while the Chapter C definition uses
[O₂(K),K]. The short-group commutator theorem identifies these subgroups.
The existing intrinsic central cover, built from the prescribed
`ordinaryModuleModel`, has kernel C_U(K). The dual natural A₇ module has
zero first cohomology, so this cover is injective. Its quotient coordinates
therefore give actual linear coordinates on U, with the original
conjugation formula preserved. No natural model of W_K is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7,
B.3.3(1), and the ordinary A₇ paragraph of 13.6.22, printed p.932/PDF949.
-/

@[expose] public section

open scoped IsMulCommutative
open Subgroup Representation Representation.OneCohomology BinaryPermutation
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.ComponentSplitting
variable {G : Type*} [Group G] [Finite G] (K : Subgroup G)

omit [Finite G] in
/-- C.1 two-perfection identifies the source central-core commutator with U(K). -/
theorem central_commutator (h : IsShort K) :
    ⁅((center (pCore 2 K)).map (pCore 2 K).subtype).map K.subtype, K⁆ =
      (blockU K).map K.subtype := by
  have hi := short_centerPreimage_commutator h (MonoidHom.id K)
    Function.surjective_id (by simp only [MonoidHom.ker_id]; exact IsPGroup.of_bot)
  have he : ⁅(center (pCore 2 K)).map (pCore 2 K).subtype, (⊤ : Subgroup K)⁆ = blockU K := by
    simpa using hi
  have hm := congrArg (Subgroup.map K.subtype) he
  simpa only [map_commutator, ← MonoidHom.range_eq_map, range_subtype] using hm

/-- Remove the fixed kernel of the SAME chosen ordinary block-module model. -/
noncomputable def coordinates (h : IsAlternatingBlock K 7) :
    letI := h.2.1.elementary
    Additive (blockU K) ≃ₗ[ZMod 2] natural (Fin 7) := by
  let := h.2.1.elementary
  let m := ordinaryModuleModel K h
  let p := IntrinsicCover.projection h.2.1 m (alternatingNaturalRepresentation (Fin 7)) h.2.2.choose_spec.2
  have hp := IntrinsicCover.projection_isCover h.2.1 m
    (alternatingNaturalRepresentation (Fin 7)) h.2.2.choose_spec.2
  have hinj : Function.Injective p :=
    CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.ComponentSplitting.cover_injective
      (MulEquiv.refl (alternatingGroup (Fin 7))) (IntrinsicCover.action h.2.1 m) p hp
  exact LinearEquiv.ofBijective p.toLinearMap ⟨hinj, hp.1⟩

/-- These coordinates are the original quotient map followed by the chosen model. -/
theorem coordinates_apply (h : IsAlternatingBlock K 7) (w : blockU K) :
    letI := h.2.1.elementary
    coordinates K h (Additive.ofMul w) = Multiplicative.toAdd
      ((ordinaryModuleModel K h).moduleIso (QuotientGroup.mk' (blockFixed K) w)) := rfl

/-- The coordinates retain conjugation by every original element of K. -/
theorem coordinates_conjugate (h : IsAlternatingBlock K 7) (k : K) (w : blockU K) :
    letI := h.2.1.elementary
    coordinates K h (Additive.ofMul (blockConjugate K k w)) =
      naturalRepresentation (Fin 7) (blockProjection K (ordinaryQuotientEquiv K h) k).val
        (coordinates K h (Additive.ofMul w)) := by
  let := h.2.1.elementary
  rw [coordinates_apply, (ordinaryModuleModel K h).intertwining]
  exact h.2.2.choose_spec.2 _ _

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison.ComponentSplitting
end
