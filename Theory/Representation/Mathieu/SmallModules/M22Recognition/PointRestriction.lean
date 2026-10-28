module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.PointRestriction.Extensions
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.PointRestriction.SimpleDegrees
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.OrbitStabilizers.Models

/-!
# Fixed vectors for small M22 point-stabilizer modules

The actual native point stabilizer is identified with PSL(3,4) by
`MathieuCode.m22PointStabilizerEquiv 0`. Inflation along the inverse
isomorphism transports the proved binary simple degrees one and nine.
The maximal-submodule argument then gives a fixed vector or a fixed
covector in every module of dimension ten through twelve, including
nonsplit extensions and arbitrary carrier universes.

This is precisely the local premise consumed by
`M22Recognition.of_small_degree_of_local_fixed_vectors`. It uses no
faithfulness or irreducibility assumption on the original module.

Source: Aschbacher--Smith G.7.3(2), printed p.348 (PDF p.359), whose
M22 clause cites James, J. Algebra 27 (1973), 57–111. The sufficient local
classification here instead uses the actual SL₃ tensor-word theorem,
GLS III §§2.8.6, 2.8.8 and 2.8.10(c).
-/

public section

namespace Representation.MathieuSmall.M22Recognition.PointRestriction

/-- Every binary module of dimension ten through twelve for the native M22
point stabilizer has a fixed vector in itself or its contragredient. -/
theorem fixed_or_dual
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (τ : Representation (ZMod 2)
      (MulAction.stabilizer Sporadic.Mathieu.M22 (0 : Fin 22)) V)
    (hlo : 10 ≤ Module.finrank (ZMod 2) V)
    (hhi : Module.finrank (ZMod 2) V ≤ 12) :
    τ.invariants ≠ ⊥ ∨ τ.dual.invariants ≠ ⊥ := by
  apply fixed_or_dual_of_simple_degrees ?_ τ hlo hhi
  intro W _ _ _ σ hσ hd
  let e := MathieuCode.m22PointStabilizerEquiv 0
  let σ' : Representation (ZMod 2) Matrix.PSL3Four.PSL W := σ.comp e.symm.toMonoidHom
  let : σ'.IsIrreducible :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective σ).mpr hσ
  exact SimpleDegrees.simple_degree σ' hd

end Representation.MathieuSmall.M22Recognition.PointRestriction
