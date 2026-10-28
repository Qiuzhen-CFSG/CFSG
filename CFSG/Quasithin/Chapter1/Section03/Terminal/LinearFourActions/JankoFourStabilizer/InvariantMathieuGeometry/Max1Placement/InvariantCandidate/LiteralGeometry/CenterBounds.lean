module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.LiteralGeometry.Bounds
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.LiteralGeometry.CenterBounds.Seed
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.LiteralGeometry.FixedSpaces.Conjugacy
import all CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.AmbientGeometry.LiteralCentralizer.SeedWitness

/-!
# Centers of the literal octad residuals

There are 148 distinct duad vectors supported within the two parts of the
native octad partition. Commutators put them in the residual's two-core.
The individual fixed-space bound therefore forces its center into the
E₂¹¹ kernel. The 28 octad duads are central, and fixing all of them forces
pointwise fixation of the octad, exactly its two-core in the M₂₄ quotient.
Native octad conjugacy transports both containments from the seed octad.

The individual fixed-space bound is the sole extra premise. The residual
remains the embedded solvable residual of the octad preimage; no splitting
of max1 or ambient J₄ centralizer assertion is used.

The internal import of `SeedWitness` reuses its residual conjugacy proof
without changing the shared module's public boundary.
Source: Aschbacher–Smith A.3.12(17), pp.47–48, and the local configuration
in 1.3.9, p.514; GLS3 Tables 5.3e and 5.3i.
-/

public section
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
attribute [local irreducible] Janko4.modelGroup certifiedMathieuSubgroup

/-- The center of the residual two-core lies in the literal kernel, and its
centralizer in max1 lies above the pointwise octad kernel. -/
theorem literalOctad_centerBounds (hfixed : LiteralOctadElementFixedBound) :
    LiteralOctadCenterBounds := by
  intro O
  obtain ⟨q, hq⟩ := exists_smul_octad_eq LinearFourCore.seedOctad O
  obtain ⟨g, rfl⟩ := literalMathieuMap_surjective q
  let e := MulAut.conj g
  have hR : (literalOctadResidual LinearFourCore.seedOctad).map e.toMonoidHom =
      literalOctadResidual O := AmbientGeometry.residual_conjugate _ _ g hq
  have hZ : (coreCenter (literalOctadResidual LinearFourCore.seedOctad)).map e.toMonoidHom =
      coreCenter (literalOctadResidual O) := by
    rw [map_coreCenter, hR]
  have hQ : (literalOctadTwoPreimage LinearFourCore.seedOctad).map e.toMonoidHom =
      literalOctadTwoPreimage O := literalOctadTwoPreimage_map_conj g _ _ hq
  constructor
  · intro x hx
    have hs : e.symm x ∈ coreCenter (literalOctadResidual LinearFourCore.seedOctad) :=
      mem_map_equiv.mp (hZ.symm ▸ hx)
    have hv := OctadCenter.seed_center_le_core hfixed hs
    rw [← pCore_map_iso 2 e]
    exact ⟨e.symm x, hv, e.apply_symm_apply x⟩
  · intro x hx
    have hs : e.symm x ∈ centralizer
        (coreCenter (literalOctadResidual LinearFourCore.seedOctad) :
          Set certifiedMathieuSubgroup) := by
      intro z hz
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using
        hx (e z) (hZ ▸ mem_map_of_mem e.toMonoidHom hz)
    rw [← hQ]
    exact ⟨e.symm x, OctadCenter.seed_centralizer_le_preimage hs, e.apply_symm_apply x⟩

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
