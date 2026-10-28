module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Flags
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.Residuals.FlagTypes

/-!
# The degree-five minimal parabolic with its prescribed marking

The proved binary Bruhat exhaustion supplies actual basis flag coordinates.
The complete flag in that basis is Sylow by conjugating the standard Sylow.
Equality of Sylow orders transfers the given index three to this complete
flag; the deleted-cut argument then constructs the precise chapter flag.

Source: Aschbacher–Smith, 15.3.49(l), combined manuscript (1 March 2004),
printed pp.1143–1145. No component or offender assertion is needed here.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
open Chapter2.ComponentRefinement.LieType.Binary
open Chapter1
namespace Five
open BinaryLinear.FiveFlagGeometry BinaryLinear.FiveFlagGeometry.SylowOvergroups

private instance : Finite (BinaryLinear.GL (Vector 5)) :=
  Finite.of_injective (fun g : BinaryLinear.GL (Vector 5) => (g : Vector 5 → Vector 5))
    DFunLike.coe_injective

private theorem full_flag_sylow (b : FiveBasis) :
    ∃ R : Sylow 2 (BinaryLinear.GL (Vector 5)),
      (R : Subgroup (BinaryLinear.GL (Vector 5))) = cutStabilizer b Set.univ := by
  let g := standardBasis.equiv b (Equiv.refl (Fin 5))
  have hb : standardBasis.map g = b := by simp [g, Module.Basis.map_equiv]
  refine ⟨standardSylow.mapSurjective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).surjective, ?_⟩
  change standardBorel.map (MulAut.conj g).toMonoidHom = _
  rw [standardBorel, flagStabilizer_map_conj, hb]
  rfl

/-- Index-three Sylow overgroups in degree five give actual deleted-node flags,
with exactly the supplied projective model. -/
theorem exists_position {K : Type*} [Group K] [Finite K]
    (L S P : Subgroup K) (e : L ≃* PSL 5) (hs : IsSylowIn 2 S L)
    (hSP : S ≤ P) (hPL : P ≤ L) (hi : S.relIndex P = 3) :
    ∃ pos : ModelExclusions.BinaryGeometry.Position L P 5, pos.model = e := by
  obtain ⟨Q, _, hQP, hindex⟩ := model_inputs L S P (linearModel e) hs hSP hPL hi
  obtain ⟨b, cuts, hP⟩ := isFlagParabolic_of_sylow_le Q _ hQP
  change (P.subgroupOf L).map (linearModel e).toMonoidHom = cutStabilizer b cuts at hP
  obtain ⟨R, hR⟩ := full_flag_sylow b
  apply position_of_coordinates (m := 4) (by decide) e hPL b cuts hP
  have hRP : (R : Subgroup (BinaryLinear.GL (Vector 5))) ≤
      (P.subgroupOf L).map (linearModel e).toMonoidHom := by
    rw [hR, hP]
    exact (cutStabilizer_le_iff _ _ _).mpr (Set.subset_univ _)
  have heq := sylow_relIndex_eq Q R _ hQP hRP
  simpa only [hR, hP] using heq.symm.trans hindex

end Five
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
