module

public import Theory.AlgebraicGroup.BNPair.HexagonalGeometry.CycleConjugacy
public import Theory.AlgebraicGroup.BNPair.DihedralGeometry.Metric
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.DihedralWords

/-!
# Polygon geometry at the marked quotient boundary

The marked quotient's simple reflections and standard parabolics form the
marked hexagonal or octagonal datum required by the coset geometry modules.
The quotient Weyl equivalence is transported along the supplied order
equation; the original carrier remains arbitrary, while its quotient is
finite through `MarkedQuotient.finite`.
-/

public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.PolygonParameters
open Theory.AlgebraicGroup.TitsSystem
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}

abbrev endpointParabolics (Q : MarkedQuotient P) : Fin 2 → Subgroup (X ⧸ Q.D) :=
  fun i => Q.tits.standardParabolic {Q.simple i}

private def markedWeyl (Q : MarkedQuotient P) {m : ℕ} (hm : rotationOrder Q = m) :
    {e : Weyl Q ≃* DihedralGroup m //
      e (Q.simple 0) = DihedralGroup.sr 0 ∧
      e (Q.simple 1) = DihedralGroup.sr 1} := by
  subst m
  exact ⟨weylEquiv Q, weylEquiv_simple_zero Q, weylEquiv_simple_one Q⟩

def hexagonalDatum (Q : MarkedQuotient P) (hm : rotationOrder Q = 6) :
    HexagonalGeometry.HexagonalDatum Q.tits (endpointParabolics Q) where
  typeEquiv := finTwoEquiv
  simple := Q.simple
  simple_range := Q.simple_range
  weylEquiv := (markedWeyl Q hm).val
  map_simple := by
    intro i
    fin_cases i
    · change (markedWeyl Q hm).val (Q.simple 0) = DihedralGroup.sr 0
      exact (markedWeyl Q hm).property.1
    · change (markedWeyl Q hm).val (Q.simple 1) = DihedralGroup.sr 1
      exact (markedWeyl Q hm).property.2
  parabolic_eq := by intro i; rfl

def octagonalDatum (Q : MarkedQuotient P) (hm : rotationOrder Q = 8) :
    DihedralGeometry.OctagonalDatum Q.tits (endpointParabolics Q) where
  typeEquiv := finTwoEquiv
  simple := Q.simple
  simple_range := Q.simple_range
  weylEquiv := (markedWeyl Q hm).val
  map_simple := by
    intro i
    fin_cases i
    · change (markedWeyl Q hm).val (Q.simple 0) = DihedralGroup.sr 0
      exact (markedWeyl Q hm).property.1
    · change (markedWeyl Q hm).val (Q.simple 1) = DihedralGroup.sr 1
      exact (markedWeyl Q hm).property.2
  parabolic_eq := by intro i; rfl

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.PolygonParameters
