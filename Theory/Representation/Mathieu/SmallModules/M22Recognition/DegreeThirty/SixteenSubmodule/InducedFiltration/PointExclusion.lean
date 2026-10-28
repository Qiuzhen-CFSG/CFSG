module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.Induction

/-!
# Excluding an identified adjoint point submodule

An actual binary adjoint point submodule supplies a nonzero map from the
native induced adjoint onto an irreducible M22 module. The checked filtration
of that induction forces the target degree to be at most ten or greater than
thirty. The sixteen-dimensional point submodule rules out the first case.

This discharges the filtration assumption of `impossible_of_equiv_of_filtration`.
The binary identification of the point submodule remains an explicit input
for the separate sixteen-dimensional branch assembly.

Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16;
Aschbacher--Smith, Chapter K, printed pp.451--452 and 457.
-/

public section
open Representation Sporadic.Mathieu
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule

/-- No irreducible binary M22 module of degree at most thirty contains an
identified sixteen-dimensional adjoint point submodule. -/
theorem impossible_of_equiv {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) M22 V) [σ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V ≤ 30)
    (S : Subrepresentation (pointRestriction σ))
    (hS : Module.finrank (ZMod 2) S.toSubmodule = 16)
    (e : Representation.Equiv (S.toRepresentation.comp pointSL) adjointBinary) :
    False :=
  impossible_of_equiv_of_filtration σ hd S hS e induced_factorDegreeFiltration

end Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule
