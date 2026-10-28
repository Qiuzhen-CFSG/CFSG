module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.PolygonParameters.Valence
public import Theory.AlgebraicGroup.BNPair.HexagonalGeometry.ApartmentCycle
public import Theory.AlgebraicGroup.BNPair.HexagonalGeometry.Girth
public import Theory.Combinatorics.SimpleGraph.PolygonParameters.Metric

/-!
# Finite marked polygon graph data

The marked quotient supplies the finite typed coset graph. Its colors,
cycle bounds, diameter and literal panel valences instantiate the generic
metric datum used by the spectral square argument.
-/

public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.PolygonParameters
open DihedralGeometry RootCoordinates
open SimpleGraph.OctagonShortPaths
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}

instance vertexFinite (Q : MarkedQuotient P) : Finite (CosetGeometry.Vertex (endpointParabolics Q)) :=
  Finite.of_surjective (fun x : Fin 2 × (X ⧸ Q.D) =>
    (⟨x.1,(x.2 : (X ⧸ Q.D) ⧸ endpointParabolics Q x.1)⟩ :
      CosetGeometry.Vertex (endpointParabolics Q))) (by
    rintro ⟨i,q⟩
    obtain ⟨a,rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨⟨i,a⟩,rfl⟩)

noncomputable instance vertexFintype (Q : MarkedQuotient P) :
    Fintype (CosetGeometry.Vertex (endpointParabolics Q)) := Fintype.ofFinite _

def vertexColor (Q : MarkedQuotient P) (v : CosetGeometry.Vertex (endpointParabolics Q)) : ZMod 2 :=
  v.type.val

private theorem vertexColor_adj (Q : MarkedQuotient P)
    {u v : CosetGeometry.Vertex (endpointParabolics Q)}
    (h : (graph (endpointParabolics Q)).Adj u v) :
    vertexColor Q u+1=vertexColor Q v := by
  have hh := h.1
  rcases u with ⟨i,a⟩
  rcases v with ⟨j,b⟩
  change i≠j at hh
  fin_cases i <;> fin_cases j <;> norm_num [vertexColor] at *
  decide

private theorem source_valence (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (v : CosetGeometry.Vertex (endpointParabolics Q)) :
    neighborCard (graph (endpointParabolics Q)) v =
      if vertexColor Q v=0 then Nat.card (simpleRoot Q split 0)+1
      else Nat.card (simpleRoot Q split 1)+1 := by
  classical
  have hc : neighborCard (graph (endpointParabolics Q)) v =
      Nat.card ((graph (endpointParabolics Q)).neighborSet v) := by
    rw [Nat.card_eq_fintype_card]
    dsimp [neighborCard]
    exact (Fintype.card_ofFinset _ (by intro w; simp)).symm
  rw [hc,source_neighbor_card Q split]
  rcases v with ⟨i,q⟩
  fin_cases i <;> norm_num [vertexColor,Nat.add_comm]

def hexagonMetricDatum (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (hm : rotationOrder Q=6) :
    SimpleGraph.PolygonParameters.Datum (graph (endpointParabolics Q)) 6
      (Nat.card (simpleRoot Q split 1)) (Nat.card (simpleRoot Q split 0)) where
  color := vertexColor Q
  color_adj := fun {u v} h => vertexColor_adj Q h
  connected := by
    have : Nonempty (CosetGeometry.Vertex (endpointParabolics Q)) :=
      ⟨CosetGeometry.base (endpointParabolics Q) 0⟩
    refine { preconnected := ?_ }
    intro u v
    obtain ⟨p,_⟩ := HexagonalGeometry.diameter_bound_of_standardApartmentCycle
      (endpointParabolics Q) Q.tits (hexagonalDatum Q hm).borel_le
      (hexagonalDatum Q hm).standardApartmentCycle u v
    exact ⟨p⟩
  cycle_bound := (hexagonalDatum Q hm).cycle_bound
  diameter := by
    intro u v
    obtain ⟨p,hp⟩ := HexagonalGeometry.diameter_bound_of_standardApartmentCycle
      (endpointParabolics Q) Q.tits (hexagonalDatum Q hm).borel_le
      (hexagonalDatum Q hm).standardApartmentCycle u v
    exact ((graph _).dist_le p).trans hp
  valence := source_valence Q split

theorem hexagonMetricDatum_point (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (hm : rotationOrder Q=6) :
    ∃ v, (hexagonMetricDatum Q split hm).color v=0 :=
  ⟨CosetGeometry.base (endpointParabolics Q) 0,rfl⟩

def octagonMetricDatum (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (hm : rotationOrder Q=8) :
    SimpleGraph.PolygonParameters.Datum (graph (endpointParabolics Q)) 8
      (Nat.card (simpleRoot Q split 1)) (Nat.card (simpleRoot Q split 0)) where
  color := vertexColor Q
  color_adj := fun u v h => vertexColor_adj Q (u:=u) (v:=v) h
  connected := (octagonalDatum Q hm).connected
  cycle_bound := (octagonalDatum Q hm).cycle_bound
  diameter := (octagonalDatum Q hm).dist_le_eight
  valence := source_valence Q split

theorem octagonMetricDatum_point (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (hm : rotationOrder Q=8) :
    ∃ v, (octagonMetricDatum Q split hm).color v=0 :=
  ⟨CosetGeometry.base (endpointParabolics Q) 0,rfl⟩

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.PolygonParameters
