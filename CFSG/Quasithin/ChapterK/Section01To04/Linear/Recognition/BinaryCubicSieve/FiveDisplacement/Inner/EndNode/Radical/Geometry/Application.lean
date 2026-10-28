module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Geometry
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical

/-!
# Discharging the geometric premise of the end-radical estimate

The geometry theorem supplies the actual relative two-core, its rank, minimal
normality, and the literal root-group inclusion to the existing maximizer
argument. Only the independent root fixed-space codimension estimate remains.

Source: Guralnick–Malle, *Classification of 2F-modules, II*, Proposition 4.7,
step 1, manuscript p.25.
-/

public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode
open Representation Representation.BinaryOffender

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) SL5TenDimensional.Group V)

/-- The literal root subgroup has the same common-fixed-space codimension
as the intrinsic radical acting through the parabolic inclusion. -/
theorem radical_fixedCodim_eq_marked_roots (e : Fin 2) :
    fixedCodim (σ.comp (parabolic e).subtype) (radical e) =
      fixedCodim σ (radicalRootGroup e) :=
  radical_fixedCodim_eq_rootGroup σ radical_geometry e

/-- The geometric premise is discharged; the separate representation-theoretic
root codimension estimate is retained explicitly. -/
theorem radical_estimate_of_root_codimension [FiniteDimensional (ZMod 2) V]
    (hroot : RootCodimensionEstimate σ) : RadicalEstimate σ :=
  radical_estimate_of_geometry_of_root_codimension σ radical_geometry hroot

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode
