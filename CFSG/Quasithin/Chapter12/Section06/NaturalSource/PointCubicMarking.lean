module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.PointQuotient
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.CubicMovement
public import Theory.Representation.BinaryPermutation.EightPointTransport

/-!
# Canonical marking of the original singular point

The point selected in the original Sylow action is singular for the literal
half-weight form.  The full coordinates are injective because the original
fixed space vanishes, so the point is nonzero in the six-space.  Transitivity
of the even eight-point action then transports it to the canonical
four-coordinate point used by the cubic residual.

The statement keeps the original full-coordinate map.  A caller that uses the
older quotient-coordinate notation can recover it with
`OrthogonalMarking.fullCoordinates_apply`.

Source: Aschbacher--Smith, 12.6.24 and the cubic marking in the proof of
12.6.33, printed pp.830--831 and 837--838.
-/

public section
open Subgroup
open BinaryPermutation BinaryPermutation.TerminalOrthogonal
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06

variable {G : Type*} [Group G] [Finite G]
  {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]
  (S : SourceHypothesis K T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes)
  (hZ : ZV L V = ⊥) (z : V)

/-- The original singular point has the canonical cubic point coordinates. -/
theorem SourceHypothesis.original_point_cubic_marking
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer
      ((D.fullSetup hZ T z).V₁ : Set G)) :
    ∃ r : Equiv.Perm (Fin 8),
      (D.fullCoordinates hZ z).toAdd =
        naturalRepresentation (Fin 8) r
          TerminalOrthogonal.CubicMovement.point := by
  let _ := S.chosen.elementary
  let e := D.fullCoordinates hZ
  have he0 : (e z).toAdd ≠ 0 := by
    intro he
    apply hz
    apply e.injective
    apply Multiplicative.toAdd.injective
    simpa using he
  have hsing : ¬ D.Nonsingular z :=
    S.original_point_singular D hZ z hz hTz
  have hform : TerminalOrthogonal.Eight.form (e z).toAdd = 0 := by
    by_contra hn
    exact hsing ((D.fullCoordinates_nonsingular_iff hZ z).mp hn)
  obtain ⟨a, ha⟩ := EightGeometry.singular_transitive
    ((e z).toAdd) TerminalOrthogonal.CubicMovement.point he0
    TerminalOrthogonal.CubicMovement.point_ne_zero hform
    TerminalOrthogonal.CubicMovement.point_singular
  refine ⟨a.val⁻¹, ?_⟩
  have hh := congrArg (naturalRepresentation (Fin 8) a.val⁻¹) ha
  simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply] using hh

end CFSG.Quasithin.Chapter12.Section06
