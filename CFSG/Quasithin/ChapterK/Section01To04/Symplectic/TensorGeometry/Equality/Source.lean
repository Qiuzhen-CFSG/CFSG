module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Equality
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Involutions
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Outer

/-!
# Source assembly for tensor equality actors

The genuine Chapter K hypotheses and the displayed tensor identification
supply every premise of the equality argument. Native involution dimensions
force diagram preservation and the outer-actor exclusion. The actual Sylow
pointwise-fixer calculation then supplies the strict rank argument.

Consequently the only small-ratio actor in a marked Sylow is the literal
transported plane radical, and the cubic ratio is at least two. The parent
combines this with the independently proved attained ratio and quadratic
obstruction to finish K.3.4.2.

Source: Aschbacher–Smith, K.3.4.2, printed p.457 (PDF p.468).
-/

public section
open Representation Representation.BinaryOffender Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour SymplecticConjugatePair
open Theory.SpecificGroups.SymplecticFour.InvolutionTypes
namespace CFSG.Quasithin.ChapterK.Symplectic
variable {G V F : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
  [IsIrreducible (ρ.comp L.subtype)] [Field F]
  [Algebra (SchurField (ρ.comp L.subtype)) F]
  {K : GroupClass} (hS : SourceHypothesis K ρ L)
  {s : ℕ} (hs : 0 < s) (h : TensorIdentification (ρ.comp L.subtype) F s)

include hS hs h

private theorem tensor_equality_earlier_premises :
    (∀ A, IsElementaryTwo A → fixedCodim ρ A ≤ 2 * rank A → A ≤ L) ∧
    (∀ (T : Sylow 2 G) (j : G) (hjL : j ∈ L), j ∈ T → orderOf j = 2 →
      ¬ IsB1 (h.groupEquiv ⟨j, hjL⟩) →
      rank (subspaceKernel ρ (fixedSpace ρ (Subgroup.zpowers j)) T) ≤ s) := by
  have hb (j : L) (hj : IsB1 (h.groupEquiv j)) :=
    h.component_isB1_fixed_finrank ρ L j.val j.property hj
  have ha (j : L) (hj : IsA2 (h.groupEquiv j)) :=
    h.component_isA2_fixed_finrank ρ L j.val j.property hj
  refine ⟨h.elementary_le_component hS hs hb ha, ?_⟩
  let : L.Normal := by rw [← hS.fitting]; infer_instance
  have hdiagram := h.preservesDiagram_of_native_fixed_dimensions hs hb ha
  intro T j hjL _ hj hB
  exact h.sylow_nonB1_fixedKernel_rank_le hS hdiagram T j hjL hj hB

/-- The source hypotheses discharge the placement and pointwise-fixer inputs
in the strict rank argument. -/
theorem tensor_source_actor_rank_gt_four_mul {A : Subgroup G}
    (hA : IsElementaryTwo A) (hsmall : fixedCodim ρ A ≤ 2 * rank A) :
    4 * s < rank A := by
  obtain ⟨hp, hf⟩ := tensor_equality_earlier_premises hS hs h
  exact tensor_actor_rank_gt_four_mul ρ L hs h hf hA (hp A hA hsmall) hsmall

/-- K.3.4.2's equality actor with the exact Sylow marking and literal
component/model maps. No earlier-source premise remains undischarged. -/
theorem tensor_source_marked_actor_eq (T : Sylow 2 G)
    (hT : ((T : Subgroup G).subgroupOf L).map h.groupEquiv.toMonoidHom = unipotent)
    {A : Subgroup G} (hA : IsElementaryTwo A) (hAT : A ≤ T)
    (hsmall : actionRatio ρ A ≤ 2) :
    A = planeRadical.map (L.subtype.comp h.groupEquiv.symm.toMonoidHom) := by
  obtain ⟨hp, hf⟩ := tensor_equality_earlier_premises hS hs h
  exact tensor_marked_actor_eq_of_ratio_le_two ρ L hs h hp hf T hT hA hAT hsmall

/-- The lower cubic bound from the source hypotheses and actual tensor
identification, with every local geometric premise discharged. -/
theorem tensor_source_cubicRatio_ge_two : 2 ≤ cubicRatio ρ := by
  obtain ⟨hp, hf⟩ := tensor_equality_earlier_premises hS hs h
  exact tensor_cubicRatio_ge_two ρ L hs h hp hf

end CFSG.Quasithin.ChapterK.Symplectic
