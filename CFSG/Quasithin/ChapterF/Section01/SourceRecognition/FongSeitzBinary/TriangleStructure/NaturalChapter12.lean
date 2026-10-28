module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TriangleStructure.NaturalCores
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Natural coordinates for the original Chapter 12 triangle cores

The actual proper-K/full KnownSimple preparation supplies F.1.1. A single
original PSL₂ factor and rotation three then give natural coordinates on
both full parabolic two-cores and transitivity on their nonidentity elements.
Conjugation is evaluated using the original full endpoint maps of the same
marked split quotient. No natural-action or core-structure premise remains.

These are the natural-module inputs to the triangle's projective-plane
recognition. The final marked A₂ comparison is a separate assembly step.
Source: AS 12.2.2 and F.1.1--3; Fong--Seitz I (3E), printed p.14;
DGS, Groups and Graphs (1985), (5.12), (10.5), pp.113--114,156.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
  (split : SplitData Q.tits)
include D h hmany hn hpsl d hTH e split

/-- Natural coordinates on each original Chapter 12 triangle core, with
conjugation evaluated through the same full endpoint marking. -/
theorem rankOne_triangle_natural_cores (hm : rotationOrder Q = 3) (i : Fin 2) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2^n ∧
      ∃ (μ : rankOne Q split i ≃* SL(2,F))
        (c : (parabolic ![L,R] (Global.sourceS L H) i).pCoreIn 2 ≃*
          Multiplicative (Fin 2 → F)),
        ∀ (a : parabolic ![L,R] (Global.sourceS L H) i) (r : rankOne Q split i),
          MarkedLocal.endpointMap Q e i a = r →
          ∀ v : (parabolic ![L,R] (Global.sourceS L H) i).pCoreIn 2,
            ∃ w : (parabolic ![L,R] (Global.sourceS L H) i).pCoreIn 2,
              (w : G) = (a : G)*(v : G)*(a : G)⁻¹ ∧
              (c w).toAdd = Matrix.mulVec (μ r).val (c v).toAdd := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact TriangleStructure.original_natural_cores Q e hf split hm 0 hpsl i

/-- The actual rank-one actor is transitive on nonidentity elements of each
original core; the given full endpoint map identifies every conjugator. -/
theorem rankOne_triangle_core_nonidentity_conjugate (hm : rotationOrder Q = 3)
    (i : Fin 2) (x y : (parabolic ![L,R] (Global.sourceS L H) i).pCoreIn 2)
    (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ a : parabolic ![L,R] (Global.sourceS L H) i,
      MarkedLocal.endpointMap Q e i a ∈ rankOne Q split i ∧
      (a : G)*(x : G)*(a : G)⁻¹ = (y : G) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact TriangleStructure.original_core_nonidentity_conjugate Q e hf split hm 0 hpsl i x y hx hy
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
