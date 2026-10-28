module

public import Theory.Representation.Mathieu.SmallModules.M11DegreeTwelve.InducedHeads
public import Theory.Mathieu.M11.Properties.IndexTwelve

/-!
# Completeness of the binary M11 modules through degree twelve

The concrete index-twelve overgroup of the marked eleven-normalizer supplies
both twelve-coset actions and normal generation by the eleven-subgroup. The
resulting induced-module degree gap excludes dimensions eleven and twelve.
The prime-eleven lower bound then forces degree ten, where the existing
classification gives an actual equivalence to the M12 point restriction.

This discharges the low-degree recognition input in Aschbacher--Smith K.4,
printed p.457/PDF p.468, using the Mathieu module calculation of James,
J. Algebra 27 (1973), 57--111. The native M11 marking is retained throughout;
no cubic-ratio, covering-group, or additional classification premise is used.
-/

public section
namespace Representation.MathieuSmall.M11DegreeTwelve
open Sporadic.Mathieu

/-- The literal normalizer induction has no simple quotient of dimension
eleven or twelve, with all subgroup premises discharged. -/
theorem smallInducedHeads : SmallInducedHeads := by
  obtain ⟨H, hNH, hH, hN, hgen⟩ := exists_m11Sylow11Normalizer_indexTwelve_overgroup
  exact smallInducedHeads_of_index_twelve H hNH hH hN hgen

/-- Every faithful irreducible binary M11 module through degree twelve is
equivalent to the actual point restriction of the M12 heart. -/
theorem equiv_point_of_faithful_degree_le_twelve
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) M11 V) (hf : Function.Injective σ) [σ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V ≤ 12) :
    Nonempty (σ.Equiv M12Recognition.pointRepresentation) :=
  equiv_point_of_smallInducedHeads σ smallInducedHeads hf hd

end Representation.MathieuSmall.M11DegreeTwelve
