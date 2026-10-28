module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCoreRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairReduced
public import CFSG.Quasithin.ChapterF.Section01.SourceLocalResidual
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.Overlap

/-!
# Original A5 factors from reduced core and residual markings

The DGS reduction preserves the embedded core and solvable residual of each
full parabolic. Transporting these subgroups through one reduced endpoint
isomorphism therefore gives the corresponding original core containment.
An original A5 core quotient then identifies the original factor with that
residual. The same reduced map consequently marks the actual factor; neither
perfectness of the original factor nor an original model marking is assumed.

This compares full parabolic cores. Control of the original join with S is
a further model calculation, supplied by the row modules in this family.

Source: DGS, Groups and Graphs, (6.1), pp.118–119, and (15.2), pp.226–228;
Aschbacher–Smith F.1.12, printed p.264.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.A5PairCatalogue
open SuzukiContainment
variable {G : Type*} [Group G] [Finite G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Transport the intrinsic core and residual through the same reduced endpoint map. -/
theorem original_core_le_residual_of_reduced_equiv
    (h : HypothesisF11 L S) (i : Fin 2) {X : Type*} [Group X] [Finite X]
    (e : parabolic L (reducedSylow L S) i ≃* X)
    (hc : pCore 2 X ≤ solvableResidual X) :
    pCore 2 (parabolic L S i) ≤ solvableResidual (parabolic L S i) := by
  have hr : pCore 2 (parabolic L (reducedSylow L S) i) ≤
      solvableResidual (parabolic L (reducedSylow L S) i) := by
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [pCore_map_iso, map_solvableResidual_eq _ e.surjective]
    exact hc
  apply (map_le_map_iff_of_injective (parabolic L S i).subtype_injective).mp
  change twoCore (parabolic L S i) ≤ _
  rw [← reduced_parabolic_core h i, ← reduced_parabolic_residual h i]
  exact map_mono hr

/-- The original factor is identified with the full parabolic residual;
perfectness of the original factor is a conclusion, not an input. -/
theorem local_eq_residual_of_reduced_equiv
    (h : HypothesisF11 L S) (i : Fin 2)
    (a : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5))
    {X : Type*} [Group X] [Finite X]
    (e : parabolic L (reducedSylow L S) i ≃* X)
    (hc : pCore 2 X ≤ solvableResidual X) :
    L i = (solvableResidual (parabolic L S i)).map (parabolic L S i).subtype :=
  h.a5_local_eq_parabolic_residual_of_core_le i a
    (original_core_le_residual_of_reduced_equiv h i e hc)

/-- The same map marks the original factor by the actual model residual. -/
theorem local_marking_of_reduced_equiv
    (h : HypothesisF11 L S) (i : Fin 2)
    (a : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5))
    {X : Type*} [Group X] [Finite X]
    (e : parabolic L (reducedSylow L S) i ≃* X)
    (hc : pCore 2 X ≤ solvableResidual X) :
    ((L i).subgroupOf (parabolic L (reducedSylow L S) i)).map e.toMonoidHom =
      solvableResidual X := by
  have he : (L i).subgroupOf (parabolic L (reducedSylow L S) i) =
      solvableResidual (parabolic L (reducedSylow L S) i) := by
    apply map_injective (parabolic L (reducedSylow L S) i).subtype_injective
    rw [map_subgroupOf_eq_of_le (show L i ≤ parabolic L (reducedSylow L S) i from
      le_sup_left.trans le_sup_left), reduced_parabolic_residual h i]
    exact local_eq_residual_of_reduced_equiv h i a e hc
  rw [he, map_solvableResidual_eq _ e.surjective]

theorem parabolic_core_eq_of_reduced_equiv
    (h : HypothesisF11 L S) (i : Fin 2) {X : Type*} [Group X] [Finite X]
    (e : parabolic L (reducedSylow L S) i ≃* X)
    (hc : pCore 2 X ≤ solvableResidual X) :
    twoCore (parabolic L S i) = twoCore (L i) := by
  have hle : twoCore (parabolic L S i) ≤ L i :=
    (map_mono (original_core_le_residual_of_reduced_equiv h i e hc)).trans
      (h.parabolic_residual_le_local i)
  rw [← h.local_inf_parabolic_core i, inf_eq_right.mpr hle]

end CFSG.Quasithin.ChapterF.Source.A5PairCatalogue
