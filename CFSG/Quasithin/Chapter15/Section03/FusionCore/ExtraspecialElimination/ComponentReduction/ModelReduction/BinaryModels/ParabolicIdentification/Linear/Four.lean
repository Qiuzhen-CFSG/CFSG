module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Flags
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.Sylow
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.Bruhat
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.StandardOvergroups

/-!
# The degree-four minimal parabolic with its prescribed marking

The concrete upper triangular subgroup has order 64 and odd index 315.
Conjugating it to the supplied Sylow subgroup and applying the four-dimensional
Bruhat exhaustion produces actual flag coordinates. Prime index then deletes
exactly one cut. All transports retain the original PSL model.

Source: Aschbacher–Smith, 15.3.49(l), combined manuscript (1 March 2004),
printed pp.1143–1145.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four
open Chapter2.ComponentRefinement.LieType.Binary
open Chapter1

private instance : Finite (BinaryLinear.GL (Vector 4)) :=
  Finite.of_injective (fun g : BinaryLinear.GL (Vector 4) => (g : Vector 4 → Vector 4))
    DFunLike.coe_injective

private theorem coordinates (S : Sylow 2 (BinaryLinear.GL (Vector 4)))
    (P : Subgroup (BinaryLinear.GL (Vector 4))) (hSP : (S : Subgroup (BinaryLinear.GL (Vector 4))) ≤ P) :
    ∃ (b : Basis 3) (cuts : Set (Fin 3)), P = cutStabilizer b cuts ∧
      (S : Subgroup (BinaryLinear.GL (Vector 4))) = cutStabilizer b Set.univ := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (BinaryLinear.GL (Vector 4)) standardSylow S
  have hmap : standardBorel.map (MulAut.conj g).toMonoidHom = (S : Subgroup (BinaryLinear.GL (Vector 4))) := by
    change ((g • standardSylow : Sylow 2 (BinaryLinear.GL (Vector 4))) : Subgroup (BinaryLinear.GL (Vector 4))) = _
    rw [hg]
  let Q := P.map (MulAut.conj g).symm.toMonoidHom
  have hBQ : standardBorel ≤ Q := by
    intro u hu
    apply Subgroup.mem_map_equiv.mpr
    apply hSP
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
  obtain ⟨cuts, hQ⟩ := standard_overgroups_of_bruhat hasBruhatDecomposition Q hBQ
  have hQP : Q.map (MulAut.conj g).toMonoidHom = P :=
    (Subgroup.map_symm_eq_iff_map_eq Q (e := MulAut.conj g) (H := P)).mp rfl
  refine ⟨standardBasis.map g, cuts, ?_, ?_⟩
  · rw [← hQP, hQ, cutStabilizer_map_conj]
  · rw [← hmap, standardBorel, cutStabilizer_map_conj]

/-- Construct the actual flag with one deleted dimension in degree four. -/
theorem exists_position {K : Type*} [Group K] [Finite K]
    (L S P : Subgroup K) (e : L ≃* PSL 4) (hs : IsSylowIn 2 S L)
    (hSP : S ≤ P) (hPL : P ≤ L) (hi : S.relIndex P = 3) :
    ∃ pos : ModelExclusions.BinaryGeometry.Position L P 4, pos.model = e := by
  obtain ⟨Q, _, hQP, hindex⟩ := model_inputs L S P (linearModel e) hs hSP hPL hi
  obtain ⟨b, cuts, hP, hQ⟩ := coordinates Q _ hQP
  apply position_of_coordinates (m := 3) (by decide) e hPL b cuts hP
  simpa only [hQ, hP] using hindex

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four
