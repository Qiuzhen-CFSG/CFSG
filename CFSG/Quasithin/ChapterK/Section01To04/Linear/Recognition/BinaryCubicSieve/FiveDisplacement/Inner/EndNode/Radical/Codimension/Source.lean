module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Codimension
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical

/-!
# Applying the proved codimension bound to radical maximization

The geometric identification of the relative two-core remains with the
independent geometry producer. The representation-theoretic codimension
premise is now discharged for the literal root group used by the relative
maximizer. The parent end-radical task retains the unconditional assembly.

Source: Guralnick–Malle, Classification of 2F-modules II, Proposition 4.7
step 1, pp.25–26; Aschbacher–Smith K.3.2, printed pp.454–455.
-/

public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Codimension
open Representation
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) SL5TenDimensional.Group V)

/-- Discharge the root-codimension premise in the actual relative radical argument. -/
theorem radical_estimate_of_geometry [FiniteDimensional (ZMod 2) V]
    (hgeometry : RadicalGeometry) : RadicalEstimate σ :=
  radical_estimate_of_geometry_of_root_codimension σ hgeometry
    (root_codimension_estimate_of_local_highest σ)

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Codimension
