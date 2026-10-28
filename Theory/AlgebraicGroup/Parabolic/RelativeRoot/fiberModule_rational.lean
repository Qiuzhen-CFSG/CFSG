module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.sourceRelativeRootLayer_root_mem
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.source_fiber_regular_morphism
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.fiber_module_source_action_bridge

/-!
# Regularity of relative-root fiber conjugation

This module isolates the geometric input needed to recognize a relative-root
fiber action as a rational representation. Regular conjugation means that,
after transporting the concrete Levi action through the fiber's point-group
equivalence, its matrices are the rational points of an algebraic-group
morphism to `GL(M.V)`.

The transported source-coordinate morphism supplies this regular action for
every fiber module. The bridge below then identifies its matrices with
`M.representation` using the defining agreement between that representation
and quotient conjugation.

This proves the rationality clause of GLS3, Chapter 1, Theorem 1.14.7, at the
lower representation layer where the fiber action and its regular coordinate
model are available; it does not depend on the numbered theorem.
-/

universe u v

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The concrete Levi conjugation action on a relative-root fiber is regular
after transport through its chosen point equivalence. -/
@[expose]
public def RelativeRootFiberModule.HasRegularConjugation
    {K : Variety k} [AlgebraicGroup K]
    {S : RelativeRootRepresentationSource K}
    (M : RelativeRootFiberModule S) : Prop :=
  ∃ e : Module.Basis (Fin (Module.finrank k M.V)) k M.V,
    ∃ f : AlgebraicGroup.Morphism S.L.carrierVariety (glVarietyOf k M.V),
      ∀ l q,
        Multiplicative.ofAdd
            ((glPointEquivOf k M.V e (f.onPoints l)).1
              (Multiplicative.toAdd (M.pointEquiv q))) =
          M.pointEquiv (M.conjugationAction l q)

public theorem RelativeRootFiberModule.hasRegularConjugation
    {K : Variety k} [AlgebraicGroup K]
    {S : RelativeRootRepresentationSource K}
    (M : RelativeRootFiberModule S) : M.HasRegularConjugation := by
  let e := M.coordinateLinearEquiv
  let b := S.sourceFiberCoordinateTransportBasis e
  let f := S.sourceFiberCoordinateTransportMorphism e
  refine ⟨b, f, ?_⟩
  intro l q
  dsimp [b, f, e]
  rw [M.pointEquiv_coordinate, M.pointEquiv_coordinate]
  rw [M.conjugationAction_eq_sourceFiberConjugationHom]
  simpa using S.sourceFiberCoordinateTransportMorphism_point_action e l q

/-- A regular realization of the transported concrete conjugation action makes
the fiber representation rational. -/
public theorem
    RelativeRootFiberModule.isRationalRepresentation_of_hasRegularConjugation
    {K : Variety k} [AlgebraicGroup K]
    {S : RelativeRootRepresentationSource K}
    (M : RelativeRootFiberModule S) (hM : M.HasRegularConjugation) :
    IsRationalRepresentation M.representation := by
  rcases hM with ⟨e, f, hf⟩
  refine ⟨e, f, fun l ↦ ?_⟩
  ext v
  let q : relativeRootFiberQuotientSubgroup S :=
    M.pointEquiv.symm (Multiplicative.ofAdd v)
  have hq := (hf l q).trans (M.representation_agrees_with_conjugation l q)
  simpa [q] using congrArg Multiplicative.toAdd hq

/-- Every relative-root fiber representation is rational. The representing
morphism is concrete Levi conjugation in the fiber module's linear
coordinates. -/
public theorem RelativeRootFiberModule.isRationalRepresentation
    {K : Variety k} [AlgebraicGroup K]
    {S : RelativeRootRepresentationSource K}
    (M : RelativeRootFiberModule S) :
    IsRationalRepresentation M.representation :=
  M.isRationalRepresentation_of_hasRegularConjugation
    M.hasRegularConjugation

end Theory.AlgebraicGroup
