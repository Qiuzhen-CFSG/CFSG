module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.Restriction
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.BinaryIdentification
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.Induction
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration

/-!
# The sixteen-dimensional point-submodule branch for M22

An irreducible sixteen-dimensional binary point submodule is equivalent to
the restriction of the adjoint action of SL₃(4). Its actual inclusion induces
a nonzero map from the native induced adjoint to the original M22 module.
The checked filtration of that induction has simple-factor degrees
140, 1, 34, 1, 34, 1, 1, 140. Thus an irreducible target of degree at most
thirty has degree at most ten, contradicting its sixteen-dimensional subspace.

Both the binary identification and the native filtration are discharged here.
The point restriction is along the literal zero-stabilizer inclusion, and no
semisimplicity of that restriction is used. This excludes the sixteen-dimensional
branch in `DegreeThirty.finrank_eq_ten_of_point_submodule_cases`.

Source context: Guralnick–Malle I, Proposition 5.1, pp.15–16, and
Aschbacher–Smith, Chapter K, printed pp.451–452 and 457.
-/

public section
open Representation Sporadic.Mathieu
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule

/-- A faithful irreducible binary M22 module of degree at most thirty has no
sixteen-dimensional irreducible submodule on its native point stabilizer. -/
theorem impossible
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) M22 V) (_hf : Function.Injective σ)
    [σ.IsIrreducible] (hd : Module.finrank (ZMod 2) V ≤ 30)
    (S : Subrepresentation (pointRestriction σ))
    (hS : S.toRepresentation.IsIrreducible)
    (hdS : Module.finrank (ZMod 2) S.toSubmodule = 16) : False := by
  let := hS
  obtain ⟨e⟩ := point_submodule_equiv_adjointBinary σ S hdS
  exact impossible_of_equiv_of_filtration σ hd S hdS e induced_factorDegreeFiltration

end Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule
