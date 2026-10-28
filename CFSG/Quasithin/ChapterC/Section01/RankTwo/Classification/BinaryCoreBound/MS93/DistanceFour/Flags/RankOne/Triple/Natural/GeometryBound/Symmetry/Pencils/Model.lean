module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Symmetry.Algebra
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.Model

/-!
# Literal matrix pencils for the p.905 flag selection

The objects below are actual parabolic cosets, intrinsic two-cores, and fixed
subgroups in the natural binary three-space. A selection generating the matrix
group lifts to centrality in the full vertex stabilizer. The fixed spaces retain
an arbitrary automorphism marking, including the graph automorphism.

`MatrixSeparation` is an intermediate matrix obligation, not a source theorem.
Its constructor is needed before the source pencil facts can be assembled.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.905.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Pencils
open RankOnePairing.Incidence.FixedGeometry.ValueConstruction

/-- Left-coset incidence in the literal quotient group. -/
def matrixIncident (t : SL) (i : Bool) (g d : SL) : Prop :=
  ∃ a : SL, g⁻¹ * a ∈ modelParabolic t i ∧ d⁻¹ * a ∈ modelParabolic t (!i)

/-- The intrinsic core at the left parabolic coset represented by g. -/
def matrixCore (t : SL) (i : Bool) (g : SL) : Subgroup SL :=
  ((modelParabolic t i).pCoreIn 2).map (MulAut.conj g).toMonoidHom

/-- Fixed vectors of that core in the supplied marking of the natural module. -/
def matrixFixed (σ : MulAut SL) (t : SL) (i : Bool) (g : SL) :
    Subgroup VectorGroup := fixedSpace ((matrixCore t i g).map σ.toMonoidHom)

@[simp] theorem matrixCore_one (t : SL) (i : Bool) :
    matrixCore t i 1 = (modelParabolic t i).pCoreIn 2 := by
  unfold matrixCore
  rw [map_one]
  exact map_id _

/-- A sufficient finite matrix selection: the three cores generate the full
matrix group, and both selected fixed spaces differ from the base fixed space. -/
structure MatrixSeparation (σ : MulAut SL) (t : SL) (i : Bool) : Prop where
  separate : ∀ d d' : SL, matrixIncident t i 1 d → matrixIncident t i 1 d' →
    matrixCore t i 1 ⊓ matrixCore t (!i) d ≠
      matrixCore t i 1 ⊓ matrixCore t (!i) d' →
    ∃ g g' : SL, matrixIncident t i g d ∧ matrixIncident t i g' d' ∧
      matrixFixed σ t i g ≠ matrixFixed σ t i 1 ∧
      matrixFixed σ t i g' ≠ matrixFixed σ t i 1 ∧
      (matrixCore t i 1 ⊔ matrixCore t i g) ⊔ matrixCore t i g' = ⊤

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Pencils
