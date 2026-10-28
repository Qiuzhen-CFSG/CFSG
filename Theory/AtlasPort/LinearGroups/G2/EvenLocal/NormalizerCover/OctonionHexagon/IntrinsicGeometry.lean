module

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.CosetGeometry

/-!
# Intrinsic split-octonion points and lines

A line is a two-dimensional subspace on which every octonion product vanishes.
Points are the existing trace-zero, norm-zero projective octonions. Incidence
means inclusion of a point's one-dimensional subspace in a line.

The coordinate span of vectors 0 and 1 is a line, and actual octonion
automorphisms act on the line type by linear images. This module supplies the
common definitions for the independent coset identification, graph metric,
and apartment-normalization proofs. It does not assert their conclusions.

Source context: the split G₂ geometry used in the defining-characteristic
rank-two case of Aschbacher--Smith, Theorem 0.1.2(1), printed pp.3--4, and
Theorem 0.1.1, printed pp.481--482. Coordinates and the actual automorphism
model are those of the imported licensed ATLAS port.
-/

@[expose] public section

open Atlas.G2 Atlas.SplitOctonion

namespace Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
variable {F : Type*} [Field F]

/-- A two-dimensional subspace on which every octonion product vanishes. -/
def IsZeroProductLine (L : Submodule F (Carrier F)) : Prop :=
  Module.finrank F L = 2 ∧ ∀ x ∈ L, ∀ y ∈ L, mul x y = 0

/-- The geometric line type, with no group-family label or incidence assumption. -/
def ZeroProductLine (F : Type*) [Field F] :=
  {L : Submodule F (Carrier F) // IsZeroProductLine L}

/-- The initial zero-product plane spanned by coordinate vectors 0 and 1. -/
def standardPlane : Submodule F (Carrier F) :=
  Submodule.span F {basisVector 0, basisVector 1}

theorem mem_standardPlane (x : Carrier F) :
    x ∈ standardPlane ↔ ∃ a b : F, a • basisVector 0 + b • basisVector 1 = x :=
  Submodule.mem_span_pair

theorem standardPlane_isZeroProductLine : IsZeroProductLine (standardPlane (F := F)) := by
  constructor
  · have hi : LinearIndependent F (![basisVector 0, basisVector 1] : Fin 2 → Carrier F) := by
      rw [linearIndependent_fin2]
      constructor
      · intro h
        have he := congrFun h 1
        simp [basisVector] at he
      · intro a h
        have he := congrFun h 0
        simp [basisVector] at he
    have hr : Set.range (![basisVector 0, basisVector 1] : Fin 2 → Carrier F) =
        {basisVector 0, basisVector 1} := by
      ext x
      constructor
      · rintro ⟨i,rfl⟩
        fin_cases i <;> simp
      · rintro (rfl | rfl)
        · exact ⟨0,rfl⟩
        · exact ⟨1,rfl⟩
    have he := finrank_span_eq_card hi
    change Module.finrank F (Submodule.span F
      (Set.range (![basisVector 0, basisVector 1] : Fin 2 → Carrier F))) = 2 at he
    rw [hr] at he
    exact he
  · intro x hx y hy
    obtain ⟨a,b,rfl⟩ := (mem_standardPlane x).mp hx
    obtain ⟨c,d,rfl⟩ := (mem_standardPlane y).mp hy
    ext i
    fin_cases i <;> simp [mul, basisVector]

def standardLine : ZeroProductLine F := ⟨standardPlane, standardPlane_isZeroProductLine⟩

def mapLine (g : Model F) (L : ZeroProductLine F) : ZeroProductLine F :=
  ⟨L.val.map g.val.toLinearMap, by
    constructor
    · rw [g.val.finrank_map_eq, L.property.1]
    · rintro x ⟨x,hx,rfl⟩ y ⟨y,hy,rfl⟩
      change mul (g.val x) (g.val y) = 0
      rw [← automorphism_mul, L.property.2 x hx y hy, map_zero]⟩

instance zeroProductLineAction : MulAction (Model F) (ZeroProductLine F) where
  smul := mapLine
  one_smul L := by
    apply Subtype.ext
    change L.val.map LinearMap.id = L.val
    exact Submodule.map_id _
  mul_smul g h L := by
    apply Subtype.ext
    change L.val.map (g.val.toLinearMap.comp h.val.toLinearMap) =
      (L.val.map h.val.toLinearMap).map g.val.toLinearMap
    exact Submodule.map_comp h.val.toLinearMap g.val.toLinearMap L.val

theorem line_smul_val (g : Model F) (L : ZeroProductLine F) :
    (g • L).val = L.val.map g.val.toLinearMap := rfl

/-- Incidence is inclusion of the actual singular projective point in the plane. -/
def pointOnLine (p : SingularPoints F) (L : ZeroProductLine F) : Prop :=
  p.val.submodule ≤ L.val

theorem pointOnLine_iff (p : SingularPoints F) (L : ZeroProductLine F) :
    pointOnLine p L ↔ p.val.rep ∈ L.val := by
  rw [pointOnLine, Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem]

/-- Vertices of the intrinsic split-octonion incidence geometry. -/
abbrev GeometryVertex (F : Type*) [Field F] := ZeroProductLine F ⊕ SingularPoints F

instance geometryAction : MulAction (Model F) (GeometryVertex F) where
  smul g v := match v with
    | Sum.inl L => Sum.inl (g • L)
    | Sum.inr p => Sum.inr (g • p)
  one_smul v := by
    cases v with
    | inl L => exact congrArg Sum.inl (one_smul (Model F) L)
    | inr p => exact congrArg Sum.inr (one_smul (Model F) p)
  mul_smul g h v := by
    cases v with
    | inl L => exact congrArg Sum.inl (SemigroupAction.mul_smul g h L)
    | inr p => exact congrArg Sum.inr (SemigroupAction.mul_smul g h p)

/-- The graph joins a singular point and a zero-product plane containing it. -/
def geometryGraph : SimpleGraph (GeometryVertex F) where
  Adj x y := match x, y with
    | Sum.inl L, Sum.inr p => pointOnLine p L
    | Sum.inr p, Sum.inl L => pointOnLine p L
    | _, _ => False
  symm := by
    constructor
    intro x y
    cases x <;> cases y <;> exact id
  loopless := by
    constructor
    intro x
    cases x <;> exact id

end Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
