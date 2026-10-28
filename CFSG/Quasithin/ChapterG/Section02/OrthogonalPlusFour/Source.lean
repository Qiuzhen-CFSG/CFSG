module

public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Layers
public import Theory.Representation.OrthogonalFourPlusMatrix.Action
public import Mathlib.Algebra.Field.ZMod

/-!
# The source hypotheses on the actual plus-four action

The model is the two SL₂(2) factors acting on two-by-two matrices by
A X B⁻¹, preserving the determinant form. This is an actual representation
on V_L, intertwined with the literal star quotient of LU. The existing
FourPlusMatrix comparison identifies this carrier with Ω₄⁺(2).

The point has order two, and membership in V is specified by the polar
form against that point. No point-stabilizer, generation, core-product,
irreducibility or quotient-module conclusion is assumed here.

Source: Aschbacher–Smith, Hypothesis G.2.1 with the replacement in
G.2.6, printed pp.332,336. The matrix model is from the cited existing
ATLAS-adapted determinant-action module.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open Setup ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G]

/-- Restriction of the literal LT/O₂(LT) map, retaining its actual image. -/
def starProjection (D : Setup G) (A : Subgroup G) (hA : A ≤ D.LT) : A →* D.star A :=
  ((QuotientGroup.mk' (pCore 2 D.LT)).comp (inclusion hA)).codRestrict _
    (fun a => mem_map.mpr ⟨⟨a, hA a.property⟩, a.property, rfl⟩)

theorem starProjection_surjective (D : Setup G) (A : Subgroup G) (hA : A ≤ D.LT) :
    Function.Surjective (starProjection D A hA) := by
  intro q
  obtain ⟨a, ha, he⟩ := q.property
  exact ⟨⟨a, ha⟩, Subtype.ext he⟩

/-- The exact additional data printed in G.2.6. -/
structure Hypothesis [Finite G] (D : Setup G) (g : G) where
  base : D.BaseHypothesis
  closure : ClosureConclusions D
  L_model : D.star D.L ≃* Multiplicative (Fin 2 → ZMod 3)
  model : D.star (D.L ⊔ D.U) ≃* PairSL (F := ZMod 2)
  coordinates : D.VL ≃* Multiplicative (Mat (F := ZMod 2))
  equivariant (a : (D.L ⊔ D.U : Subgroup G)) (v : D.VL) :
    (coordinates.symm (Multiplicative.ofAdd
      (matrixAction (model (starProjection D (D.L ⊔ D.U)
        (sup_le le_sup_left (closure.normal.1.trans le_sup_right)) a))
          (coordinates v).toAdd)) : G) = (a : G) * v * (a : G)⁻¹
  point_card : Nat.card D.V₁ = 2
  V_le_VL : D.V ≤ D.VL
  perpendicular (v : D.VL) : (v : G) ∈ D.V ↔
    ∀ z : D.V₁, (determinantForm (F := ZMod 2)).polarBilin
      (coordinates v).toAdd (coordinates ⟨z, point_le_VL D z.property⟩).toAdd = 0
  g_mem : g ∈ D.L
  nonorthogonal : ¬ conjugate D.V₁ g ≤ D.V

namespace Hypothesis
variable [Finite G] {D : Setup G} {g : G} (d : Hypothesis D g)
include d

/-- Equivariance supplies actual ambient normalization of V_L. -/
theorem LU_normalizes_VL : D.L ⊔ D.U ≤ normalizer (D.VL : Set G) := by
  apply le_normalizer_iff.mpr
  intro a ha v hv
  rw [← d.equivariant ⟨a, ha⟩ ⟨v, hv⟩]
  exact Subtype.property _

/-- Both marked conjugates are in LU, without using the generation conclusion. -/
theorem I_le_LU : D.I g ≤ D.L ⊔ D.U := by
  apply sup_le le_sup_right
  rintro _ ⟨u, hu, rfl⟩
  exact (D.L ⊔ D.U).mul_mem
    ((D.L ⊔ D.U).mul_mem ((D.L ⊔ D.U).inv_mem (mem_sup_left d.g_mem))
      (mem_sup_right hu)) ((D.L ⊔ D.U).inv_mem
        ((D.L ⊔ D.U).inv_mem (mem_sup_left d.g_mem)))

/-- This discharges the invariance input of the proved layer calculation. -/
theorem I_normalizes_VL : D.I g ≤ normalizer (D.VL : Set G) :=
  d.I_le_LU.trans d.LU_normalizes_VL

/-- The actual natural module is contained in LU. -/
theorem VL_le_LU : D.VL ≤ D.L ⊔ D.U :=
  conjugateSpanBy_le
    (d.base.point_le.trans ((le_conjugateSpanBy _ _).trans le_sup_right))
    ((show D.L ≤ D.L ⊔ D.U from le_sup_left).trans (D.L ⊔ D.U).le_normalizer)

/-- The actual four-dimensional coordinates make V_L elementary abelian. -/
theorem VL_elementary : IsElementaryAbelian 2 D.VL := by
  refine { toIsMulCommutative := ⟨⟨fun x y => d.coordinates.injective ?_⟩⟩
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  · simp only [map_mul, mul_comm]
  · intro x
    apply d.coordinates.injective
    rw [map_pow, map_one, pow_two]
    apply Multiplicative.toAdd.injective
    change (d.coordinates x).toAdd + (d.coordinates x).toAdd = 0
    ext i j
    exact CharTwo.add_self_eq_zero _

/-- The layer theorems applied to the genuine source hypothesis need
only the earlier generation calculation. -/
theorem layers (hgen : D.I g = D.L ⊔ D.U) :
    D.VL ≤ S₂ D g ∧ S₂ D g ≤ D.S g ∧
      (D.VL.subgroupOf (D.I g)).Normal ∧ ((S₂ D g).subgroupOf (D.I g)).Normal ∧
      ⁅S₂ D g, D.I g⁆ ≤ D.VL := by
  let := d.VL_elementary
  exact normal_layers d.base d.closure d.g_mem (IsElementaryAbelian.isPGroup 2 _)
    (hgen.symm ▸ d.VL_le_LU) d.I_normalizes_VL

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
