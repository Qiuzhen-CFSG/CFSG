module

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Apartments.PrefixCompletion
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification.Transitivity

/-!
# Normalizing the initial half of a binary octonion hexagon

Point transitivity and the lower-stratum root reduction normalize the first
edge. Two further root reductions normalize the next two points while fixing
the preceding ones. Their denominators are nonzero because consecutive lines
of a point hexagon are distinct: a vanishing denominator would put the next
point on the preceding line. The imported completion then applies to this
actual octonion configuration.

Source: the split G₂ geometry underlying Aschbacher–Smith, Theorem 0.1.2(1),
printed pp.3–4, repeated on pp.481–482. Coordinates and root reductions are
from the licensed ATLAS port; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Atlas.G2 Atlas.G2.Explicit Atlas.SplitOctonion
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.Apartments
open scoped LinearAlgebra.Projectivization
namespace Atlas.G2.BinaryParabolicPair.BinaryCoverGeometry
local notation "K" => ZMod 2

private theorem smul_point_eq_coordinate (g : Model K) (p : SingularPoints K)
    (i : Fin 6) (a : K) (h : g.val p.val.rep = a • offDiagonalVector i) :
    g • p = coordinatePoint i := by
  rw [← singularPointMk_rep K p, singularPointMk_smul, coordinatePoint]
  apply Subtype.ext
  exact (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨a, h.symm⟩

private theorem fixes_coordinate (g : Model K) (i : Fin 6)
    (h : g.val (offDiagonalVector i) = offDiagonalVector i) :
    g • coordinatePoint (F := K) i = coordinatePoint i :=
  (coordinatePoint_fixed_iff g i).mpr ⟨1, by simpa using h⟩

private theorem first_pair (H : PointHexagon K) :
    ∃ g : Model K, (H.map g).point 0 = coordinatePoint 0 ∧
      (H.map g).point 1 = coordinatePoint 1 := by
  obtain ⟨a,ha⟩ := exists_smul_firstPoint (H.point 0)
  let J := H.map a
  have h0 : J.point 0 = coordinatePoint 0 := ha
  let x := (J.point 1).val.rep
  have hx : x = ![x 0,x 1,x 2,0,0,0,0,0] := by
    apply annihilator_basis_zero
    have hp := products_zero_of_coordinate_on 0 (h0 ▸ J.point_on 0) (J.next_on 0)
    exact hp
  have hp : x 1 ≠ 0 ∨ x 2 ≠ 0 := by
    by_contra! hz
    have he : x = x 0 • offDiagonalVector 0 := by
      rw [hx]
      ext i
      fin_cases i <;> simp [offDiagonalVector,offDiagonalIndex,basisVector,hz.1,hz.2]
    have heq : J.point 1 = coordinatePoint 0 := by
      simpa using smul_point_eq_coordinate 1 (J.point 1) 0 (x 0) he
    have h10 := J.point_injective (heq.trans h0.symm)
    exact (by decide : (1 : Fin 6) ≠ 0) h10
  obtain ⟨b,hb,c,_,hc⟩ := lower_vector_reduction x (J.point 1).property.1
    (J.point 1).property.2 (congrFun hx 5) (congrFun hx 6) (congrFun hx 7) hp
  refine ⟨b*a, ?_, ?_⟩
  · rw [PointHexagon.map_point, SemigroupAction.mul_smul, ha]
    exact parabolic_le_pointStabilizer hb
  · rw [PointHexagon.map_point, SemigroupAction.mul_smul]
    exact smul_point_eq_coordinate b (J.point 1) 1 c hc

private theorem third_coordinate (H : PointHexagon K)
    (h0 : H.point 0 = coordinatePoint 0) (h1 : H.point 1 = coordinatePoint 1) :
    ∃ g : Model K, (H.map g).point 0 = coordinatePoint 0 ∧
      (H.map g).point 1 = coordinatePoint 1 ∧
      (H.map g).point 2 = coordinatePoint 3 := by
  let x := (H.point 2).val.rep
  have hx : x = ![x 0,x 1,0,0,0,x 5,0,0] := by
    apply annihilator_basis_one
    exact products_zero_of_coordinate_on 1 (h1 ▸ H.point_on 1) (H.next_on 1)
  have h5 : x 5 ≠ 0 := by
    intro hz
    have hmem : x ∈ (H.line 0).val := by
      have hm0 := (coordinatePoint_on_iff 0 _).mp (h0 ▸ H.point_on 0)
      have hm1 := (coordinatePoint_on_iff 1 _).mp (h1 ▸ H.next_on 0)
      have he : x = x 0 • offDiagonalVector 0 + x 1 • offDiagonalVector 1 := by
        rw [hx]
        ext i
        fin_cases i <;> simp [offDiagonalVector,offDiagonalIndex,basisVector,hz]
      rw [he]
      exact (H.line 0).val.add_mem ((H.line 0).val.smul_mem _ hm0)
        ((H.line 0).val.smul_mem _ hm1)
    have he := line_eq_of_points (show H.point 1 ≠ H.point 2 from
      fun he => (by decide : (1 : Fin 6) ≠ 2) (H.point_injective he))
      (H.point_on 1) (H.next_on 1) (H.next_on 0) ((pointOnLine_iff _ _).mpr hmem)
    exact (by decide : (1 : Fin 6) ≠ 0) (H.line_injective he)
  refine ⟨thirdReducer x, ?_, ?_, ?_⟩
  · change thirdReducer x • H.point 0 = _
    rw [h0]
    exact fixes_coordinate _ 0 (thirdReducer_fixes x).1
  · change thirdReducer x • H.point 1 = _
    rw [h1]
    exact fixes_coordinate _ 1 (thirdReducer_fixes x).2
  · exact smul_point_eq_coordinate _ _ 3 (x 5) (thirdReducer_apply x hx h5)

private theorem fourth_coordinate (H : PointHexagon K)
    (h0 : H.point 0 = coordinatePoint 0) (h1 : H.point 1 = coordinatePoint 1)
    (h2 : H.point 2 = coordinatePoint 3) :
    ∃ g : Model K, HasCoordinatePrefix (H.map g) := by
  let x := (H.point 3).val.rep
  have hx : x = ![0,x 1,0,0,0,x 5,0,x 7] := by
    apply annihilator_basis_five
    exact products_zero_of_coordinate_on 3 (h2 ▸ H.point_on 2) (H.next_on 2)
  have h7 : x 7 ≠ 0 := by
    intro hz
    have hmem : x ∈ (H.line 1).val := by
      have hm1 := (coordinatePoint_on_iff 1 _).mp (h1 ▸ H.point_on 1)
      have hm2 := (coordinatePoint_on_iff 3 _).mp (h2 ▸ H.next_on 1)
      have he : x = x 1 • offDiagonalVector 1 + x 5 • offDiagonalVector 3 := by
        rw [hx]
        ext i
        fin_cases i <;> simp [offDiagonalVector,offDiagonalIndex,basisVector,hz]
      rw [he]
      exact (H.line 1).val.add_mem ((H.line 1).val.smul_mem _ hm1)
        ((H.line 1).val.smul_mem _ hm2)
    have he := line_eq_of_points (show H.point 2 ≠ H.point 3 from
      fun he => (by decide : (2 : Fin 6) ≠ 3) (H.point_injective he))
      (H.point_on 2) (H.next_on 2) (H.next_on 1) ((pointOnLine_iff _ _).mpr hmem)
    exact (by decide : (2 : Fin 6) ≠ 1) (H.line_injective he)
  refine ⟨fourthReducer x, ?_, ?_, ?_, ?_⟩
  · change fourthReducer x • H.point 0 = _
    rw [h0]
    exact fixes_coordinate _ 0 (fourthReducer_fixes x).1
  · change fourthReducer x • H.point 1 = _
    rw [h1]
    exact fixes_coordinate _ 1 (fourthReducer_fixes x).2.1
  · change fourthReducer x • H.point 2 = _
    rw [h2]
    exact fixes_coordinate _ 3 (fourthReducer_fixes x).2.2
  · exact smul_point_eq_coordinate _ _ 5 (x 7) (fourthReducer_apply x hx h7)

/-- Every binary point hexagon has a translate with the prescribed four coordinate points. -/
theorem coordinate_prefix (H : PointHexagon K) :
    ∃ g : Model K, HasCoordinatePrefix (H.map g) := by
  obtain ⟨a,ha0,ha1⟩ := first_pair H
  obtain ⟨b,hb0,hb1,hb2⟩ := third_coordinate (H.map a) ha0 ha1
  obtain ⟨c,hc⟩ := fourth_coordinate ((H.map a).map b) hb0 hb1 hb2
  refine ⟨c*b*a, ?_⟩
  simpa only [HasCoordinatePrefix, PointHexagon.map_point, SemigroupAction.mul_smul] using hc

end Atlas.G2.BinaryParabolicPair.BinaryCoverGeometry
