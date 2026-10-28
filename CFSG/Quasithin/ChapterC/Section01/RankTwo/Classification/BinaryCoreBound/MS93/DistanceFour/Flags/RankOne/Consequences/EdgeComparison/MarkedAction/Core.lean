module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.Residual
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedProduct

/-!
# The marked core modulo the vertex kernel

The literal point-parabolic core is its translation four-group, contained in
its two-residual. The same diagram automorphism transports this containment
to the line parabolic, and conjugation transports both to the source flag.
Mapping the intrinsic core through the supplied quotient and pulling back
shows that the embedded edge core lies in the source-ordered residual times
the vertex kernel. All normality and residuals remain relative to the actual
parabolic; the free amalgam is not assumed finite.

Source: Meierfrankenfeld--Stellmacher (1993), the rank-one action used in
(4.6.9), printed p.908, with flag notation on pp.905--907.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne

private theorem model_core_le_residual (g : SL) (i : Bool) :
    (modelParabolic g i).pCoreIn 2 ≤
      (pResidual 2 (modelParabolic g i)).map (modelParabolic g i).subtype := by
  have hp : Matrix.PSL3Two.pointParabolicSL.pCoreIn 2 ≤
      (pResidual 2 Matrix.PSL3Two.pointParabolicSL).map
        Matrix.PSL3Two.pointParabolicSL.subtype := by
    rw [Matrix.PSL3Two.MarkedProduct.pointParabolic_core]
    change Matrix.PSL3Two.MarkedAutomorphisms.pointV ≤
      Matrix.PSL3Two.MarkedAutomorphisms.residual _
    rw [Matrix.PSL3Two.MarkedAutomorphisms.point_residual]
    exact Matrix.PSL3Two.MarkedAutomorphisms.pointV_le
  have hl : Matrix.PSL3Two.lineParabolicSL.pCoreIn 2 ≤
      (pResidual 2 Matrix.PSL3Two.lineParabolicSL).map
        Matrix.PSL3Two.lineParabolicSL.subtype := by
    rw [← Matrix.PSL3Two.MarkedAutomorphisms.pointParabolic_map_diagram,
      ← map_pCoreIn_of_injective 2 _ _
        Matrix.PSL3Two.MarkedAutomorphisms.diagram.injective,
      ← map_embedded_pResidual]
    exact map_mono hp
  cases i
  · have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hp
    rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,
      map_embedded_pResidual] at hh
    exact hh
  · have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hl
    rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,
      map_embedded_pResidual] at hh
    exact hh

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The core acts on the natural layer through the marked residual. -/
theorem flagKernel_le_residual_sup_vertexKernel (source : LocalSource L R) (i : Bool) :
    flagKernel source i ≤ flagResidual source i ⊔ Q R (alpha R) := by
  let P := parabolic source.projection source.flag i
  have hP : P.map source.projection = modelParabolic source.flag i := by
    exact map_comap_eq_self_of_surjective source.projection_surjective _
  have hk : IsPGroup 2 source.projection.ker := by
    rw [source.projection_kernel]
    exact pCore_isPGroup
  have hm : (P.pCoreIn 2).map source.projection ≤
      ((pResidual 2 P).map P.subtype).map source.projection := by
    rw [map_pCoreIn_of_ker_isPGroup source.projection hk P,
      map_embedded_pResidual, hP]
    exact model_core_le_residual source.flag i
  have hle : P.pCoreIn 2 ≤ (pResidual 2 P).map P.subtype ⊔ pCore 2 M := by
    rw [← source.projection_kernel, ← comap_map_eq]
    exact map_le_iff_le_comap.mp hm
  have he := map_mono (f := embedM R) hle
  rw [Subgroup.map_sup, ← Q_alpha R source.two_group source.core_le] at he
  change flagKernel source i ≤ _ at he
  simpa only [flagResidual,
    rankOne_parabolic_eq source.projection source.projection_surjective hk,
    P] using he

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
