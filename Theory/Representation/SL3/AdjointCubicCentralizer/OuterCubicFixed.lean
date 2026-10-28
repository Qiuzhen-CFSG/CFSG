module

public import Theory.Representation.SL3.AdjointCubicCentralizer.FixedLevi
public import Theory.SpecificGroups.PSL3.RootPlaneGeometry
public import Theory.SpecificGroups.PSL3.ExtensionBorel.Linear

/-!
# Fixed points for a root-plane-preserving outer cubic

The diagonal fixed-space calculation applies to an arbitrary marked module once
the actual projective actor has been transported to a marked diagonal actor.
The root-plane condition keeps the source bridge visible, while the concrete
projective conjugacy below records the remaining matrix-normal-form obligation.

The theorem below retains the original module marking `e`; it composes that
marking with the induced projective transport only for the fixed-point estimate.
Source: Aschbacher--Smith B.4.14, printed p.98, with the root-plane
normalization used in the cubic parabolic calculation.
-/

@[expose] public noncomputable section
open Matrix Subgroup
open scoped MatrixGroups
open Matrix.PSL3.ExtensionBorel
namespace Representation.SL3.AdjointCubicCentralizer

variable (F : Type*) [Field F] [Finite F] [CharP F 2]

/-- A root-plane-preserving projective cubic together with a concrete matrix
conjugacy to the diagonal normal form. -/
structure OuterCubicFixedModel where
  actor : ProjGenLinGroup (Fin 3) F
  rootSide : Bool
  actor_cube : actor ^ 3 = 1
  outer : (pglEquivInnerDiagonal F actor).val ∉
    MulAut.innerSubgroup PSL(3,F)
  rootPlane_preserved :
    (Matrix.PSL3.RootPlaneGeometry.rootPlane F rootSide).map
        (pglEquivInnerDiagonal F actor).val.toMonoidHom =
      Matrix.PSL3.RootPlaneGeometry.rootPlane F rootSide
  diagonal : Fˣ
  /-- A matrix conjugator for the projective actor's diagonal normal form. -/
  conjugator : GL (Fin 3) F
  conjugacy :
    ProjGenLinGroup.mk conjugator * actor * (ProjGenLinGroup.mk conjugator)⁻¹ =
      ProjGenLinGroup.mk (diagonalUnit F diagonal)

omit [Finite F] [CharP F 2] in
theorem projectiveAdjointTransport_bijective (P : GL (Fin 3) F) :
    Function.Bijective (projectiveAdjoint F (ProjGenLinGroup.mk P)) := by
  exact Representation.apply_bijective _ _

/-- The trace-zero linear equivalence induced by projective conjugation by `P`.
The inverse is induced by the inverse projective matrix. -/
noncomputable def projectiveAdjointTransport (P : GL (Fin 3) F) :
    TraceZero F ≃ₗ[F] TraceZero F :=
  LinearEquiv.ofBijective (projectiveAdjoint F (ProjGenLinGroup.mk P))
    (projectiveAdjointTransport_bijective F P)

omit [Finite F] [CharP F 2] in
theorem projectiveAdjointTransport_action (P : GL (Fin 3) F)
    (actor : ProjGenLinGroup (Fin 3) F) (ω : Fˣ)
    (hconj : ProjGenLinGroup.mk P * actor * (ProjGenLinGroup.mk P)⁻¹ =
      ProjGenLinGroup.mk (diagonalUnit F ω)) (v : TraceZero F) :
    projectiveAdjointTransport F P (projectiveAdjoint F actor v) =
      projectiveAdjoint F (ProjGenLinGroup.mk (diagonalUnit F ω))
        (projectiveAdjointTransport F P v) := by
  change (projectiveAdjoint F (ProjGenLinGroup.mk P))
      (projectiveAdjoint F actor v) =
    (projectiveAdjoint F (ProjGenLinGroup.mk (diagonalUnit F ω)))
      ((projectiveAdjoint F (ProjGenLinGroup.mk P)) v)
  rw [← Module.End.mul_apply, ← Module.End.mul_apply]
  rw [← map_mul, ← map_mul]
  have hp : ProjGenLinGroup.mk P * actor =
      ProjGenLinGroup.mk (diagonalUnit F ω) * ProjGenLinGroup.mk P := by
    calc
      ProjGenLinGroup.mk P * actor =
          (ProjGenLinGroup.mk P * actor * (ProjGenLinGroup.mk P)⁻¹) *
            ProjGenLinGroup.mk P := by simp [mul_assoc]
      _ = ProjGenLinGroup.mk (diagonalUnit F ω) * ProjGenLinGroup.mk P := by
        rw [hconj]
  rw [hp]

namespace OuterCubicFixedModel

variable {A M : Type*} [Group A] [Group M] [Finite M]
  [MulDistribMulAction A M]

omit [CharP F 2] in
/-- The original marked action has at least 256 fixed points after the
root-plane cubic is transported to its diagonal normal form. -/
theorem fixed_card_ge (model : OuterCubicFixedModel F)
    (hF : Nat.card F = 4) (a : A)
    (hgen : Subgroup.zpowers a = ⊤) (e : M ≃ TraceZero F)
    (he : ∀ v, e (a • v) = projectiveAdjoint F model.actor (e v)) :
    256 ≤ Nat.card (FixedPoints.subgroup A M) := by
  let transport : TraceZero F ≃ₗ[F] TraceZero F :=
    projectiveAdjointTransport F model.conjugator
  let e' : M ≃ TraceZero F := e.trans transport.toEquiv
  have he' : ∀ v, e' (a • v) =
      projectiveAdjoint F (ProjGenLinGroup.mk (diagonalUnit F model.diagonal))
        (e' v) := by
    intro v
    change transport (e (a • v)) =
      projectiveAdjoint F (ProjGenLinGroup.mk (diagonalUnit F model.diagonal))
        (transport (e v))
    rw [he]
    exact projectiveAdjointTransport_action F model.conjugator model.actor
      model.diagonal model.conjugacy (e v)
  exact fixed_card_ge_of_adjoint_generator F hF a hgen model.diagonal e' he'

end OuterCubicFixedModel
end Representation.SL3.AdjointCubicCentralizer
