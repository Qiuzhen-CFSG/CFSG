module

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.CoordinateFrame
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.IntrinsicGeometry

/-!
# Cyclic configurations in the intrinsic octonion geometry

A point hexagon consists of six distinct singular projective points and six
distinct zero-product planes with the stated cyclic incidences. These are
geometric data, with no apartment-conjugacy or metric assertion attached.

The incidence action and uniqueness of a line through two distinct points
support coordinate normalization. The cyclic order of the coordinate vectors
is checked directly as `0, 1, 5, 7, 6, 2`.

Source context: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(1), printed pp.3--4, repeated as Theorem 0.1.1 on pp.481--482.
The concrete coordinates and automorphisms are from the imported ATLAS port;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/


@[expose] public section

open Atlas.G2 Atlas.SplitOctonion
open scoped LinearAlgebra.Projectivization

namespace Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.Apartments
variable {F : Type*} [Field F]

theorem pointOnLine_mk_iff (x : Carrier F) (hx : x ≠ 0)
    (ht : trace x = 0) (hn : SplitOctonion.norm x = 0) (L : ZeroProductLine F) :
    pointOnLine (singularPointMk F x hx ht hn) L ↔ x ∈ L.val := by
  change Submodule.span F {x} ≤ L.val ↔ x ∈ L.val
  rw [Submodule.span_singleton_le_iff_mem]

theorem pointOnLine_smul (g : Model F) {p : SingularPoints F} {L : ZeroProductLine F}
    (hp : pointOnLine p L) : pointOnLine (g • p) (g • L) := by
  rw [← singularPointMk_rep F p, singularPointMk_smul, pointOnLine_mk_iff]
  exact ⟨p.val.rep, (pointOnLine_iff p L).mp hp, rfl⟩

theorem pointOnLine_smul_iff (g : Model F) (p : SingularPoints F) (L : ZeroProductLine F) :
    pointOnLine (g • p) (g • L) ↔ pointOnLine p L := by
  constructor
  · intro h
    simpa only [inv_smul_smul] using pointOnLine_smul g⁻¹ h
  · exact pointOnLine_smul g

/-- Six distinct points and six distinct actual zero-product planes, cyclically incident. -/
structure PointHexagon (F : Type*) [Field F] where
  point : Fin 6 → SingularPoints F
  line : Fin 6 → ZeroProductLine F
  point_injective : Function.Injective point
  line_injective : Function.Injective line
  point_on : ∀ i, pointOnLine (point i) (line i)
  next_on : ∀ i, pointOnLine (point (i + 1)) (line i)

def PointHexagon.map (H : PointHexagon F) (g : Model F) : PointHexagon F where
  point i := g • H.point i
  line i := g • H.line i
  point_injective := fun _ _ h => H.point_injective (smul_left_cancel g h)
  line_injective := fun _ _ h => H.line_injective (smul_left_cancel g h)
  point_on i := pointOnLine_smul g (H.point_on i)
  next_on i := pointOnLine_smul g (H.next_on i)

theorem PointHexagon.map_point (H : PointHexagon F) (g : Model F) (i : Fin 6) :
    (H.map g).point i = g • H.point i := rfl

theorem PointHexagon.map_line (H : PointHexagon F) (g : Model F) (i : Fin 6) :
    (H.map g).line i = g • H.line i := rfl

theorem reps_independent {p q : SingularPoints F} (hpq : p ≠ q) :
    LinearIndependent F (![p.val.rep, q.val.rep] : Fin 2 → Carrier F) := by
  rw [linearIndependent_fin2]
  refine ⟨q.val.rep_nonzero, ?_⟩
  intro a ha
  apply hpq
  apply Subtype.ext
  rw [← Projectivization.mk_rep p.val, ← Projectivization.mk_rep q.val]
  apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr
  exact ⟨a, ha⟩

theorem line_eq_span {p q : SingularPoints F} (hpq : p ≠ q)
    {L : ZeroProductLine F} (hp : pointOnLine p L) (hq : pointOnLine q L) :
    L.val = Submodule.span F {p.val.rep, q.val.rep} := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact (pointOnLine_iff p L).mp hp
    · exact (pointOnLine_iff q L).mp hq
  · have hr : Set.range (![p.val.rep, q.val.rep] : Fin 2 → Carrier F) =
        {p.val.rep, q.val.rep} := by
      ext x
      simp [or_comm]
    have h := finrank_span_eq_card (reps_independent hpq)
    rw [hr] at h
    exact h.trans L.property.1.symm

theorem line_eq_of_points {p q : SingularPoints F} (hpq : p ≠ q)
    {L M : ZeroProductLine F} (hpL : pointOnLine p L) (hqL : pointOnLine q L)
    (hpM : pointOnLine p M) (hqM : pointOnLine q M) : L = M := by
  apply Subtype.ext
  rw [line_eq_span hpq hpL hqL, line_eq_span hpq hpM hqM]

theorem products_zero_of_pointOnLine {p q : SingularPoints F} {L : ZeroProductLine F}
    (hp : pointOnLine p L) (hq : pointOnLine q L) :
    mul p.val.rep q.val.rep = 0 ∧ mul q.val.rep p.val.rep = 0 := by
  have hp' := (pointOnLine_iff p L).mp hp
  have hq' := (pointOnLine_iff q L).mp hq
  exact ⟨L.property.2 _ hp' _ hq', L.property.2 _ hq' _ hp'⟩

theorem coordinatePoint_submodule (i : Fin 6) :
    (coordinatePoint (F := F) i).val.submodule = Submodule.span F {offDiagonalVector i} := rfl

theorem coordinatePoint_on_iff (i : Fin 6) (L : ZeroProductLine F) :
    pointOnLine (coordinatePoint (F := F) i) L ↔ offDiagonalVector i ∈ L.val := by
  rw [pointOnLine, coordinatePoint_submodule, Submodule.span_singleton_le_iff_mem]

theorem products_zero_of_coordinate_on (i : Fin 6) {q : SingularPoints F}
    {L : ZeroProductLine F} (hi : pointOnLine (coordinatePoint i) L)
    (hq : pointOnLine q L) :
    mul (offDiagonalVector i) q.val.rep = 0 ∧
      mul q.val.rep (offDiagonalVector i) = 0 := by
  have hi' := (coordinatePoint_on_iff i L).mp hi
  have hq' := (pointOnLine_iff q L).mp hq
  exact ⟨L.property.2 _ hi' _ hq', L.property.2 _ hq' _ hi'⟩

theorem offDiagonalIndex_injective : Function.Injective offDiagonalIndex := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [offDiagonalIndex]

theorem coordinatePoint_injective : Function.Injective (coordinatePoint (F := F)) := by
  intro i j h
  have h := congrArg Subtype.val h
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).mp h
  apply offDiagonalIndex_injective
  by_contra hij
  have he := congrFun ha (offDiagonalIndex i)
  simp [offDiagonalVector, basisVector, hij] at he

/-- Reindex the six coordinate points into their cyclic order, with basis indices
`0, 1, 5, 7, 6, 2`. -/
def coordinateCycleIndex : Fin 6 → Fin 6 := ![0, 1, 3, 5, 4, 2]

theorem coordinateCycleIndex_injective : Function.Injective coordinateCycleIndex := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [coordinateCycleIndex]

theorem coordinateCycleIndex_surjective : Function.Surjective coordinateCycleIndex :=
  Finite.surjective_of_injective coordinateCycleIndex_injective

/-- All consecutive vector products in the designated coordinate hexagon vanish,
in both orders. -/
theorem coordinateCycle_products (i : Fin 6) :
    mul (offDiagonalVector (F := F) (coordinateCycleIndex i))
      (offDiagonalVector (coordinateCycleIndex (i + 1))) = 0 ∧
    mul (offDiagonalVector (F := F) (coordinateCycleIndex (i + 1)))
      (offDiagonalVector (coordinateCycleIndex i)) = 0 := by
  fin_cases i <;> constructor <;> ext j <;> fin_cases j <;>
    simp [coordinateCycleIndex, offDiagonalVector, offDiagonalIndex, basisVector, mul]

/-- A normalized initial half of a point hexagon. This records four explicit
coordinate equalities; it does not assert apartment conjugacy. -/
def HasCoordinatePrefix (H : PointHexagon F) : Prop :=
  H.point 0 = coordinatePoint 0 ∧ H.point 1 = coordinatePoint 1 ∧
    H.point 2 = coordinatePoint 3 ∧ H.point 3 = coordinatePoint 5

end Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.Apartments
