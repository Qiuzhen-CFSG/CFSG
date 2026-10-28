module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.CubicBound
public import Theory.GroupAction.CyclicAuxiliaryIndex.Overgroup

/-!
# Marked torus and commutator bounds in an explicit overgroup

Use N = C O₂(J) as the auxiliary subgroup, where B and C are normal
relative to J and t normalizes both B and J. The sufficient containment
O³(B) ≤ C O₂(B) puts the residual in N. Displacement of C into O₂(C)
extends to N, then descends through the actual star map with all cores
retained. The intrinsic Borel in K* and its original marked actor are
identified by the existing equivariant transports.

For the commutator bound use the explicit supplement D with B join D = J.
The source covered case takes D = L₁, while its marked cubic group is
L₁,+. Thus no placement of C or L₀ in B L₁,+ is needed.

Source: Aschbacher–Smith 13.8.20, printed p.954/PDF p.971.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation
open TorusModels.Assembly Theory.GroupAction.CyclicAuxiliaryIndex
variable {G : Type*} [Group G] [Finite G]

/-- Saturating by the overgroup's two-core supplies both marked endpoints.
The two t-normalizations and the two relative normalities are separate inputs. -/
theorem marked_calculation_of_overgroup
    (H K T C J D : Subgroup G) [(Source.starImage H K).Normal]
    (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 T H)
    (hJD : borel H K T hKH hT ⊔ D = J) (hCJ : C ≤ J) (hJH : J ≤ H)
    (hJB : J ≤ normalizer (borel H K T hKH hT : Set G))
    (hJC : J ≤ normalizer (C : Set G))
    (hR : residualIn 3 (borel H K T hKH hT) ≤ C ⊔ (borel H K T hKH hT).pCoreIn 2)
    (hab : ⁅borel H K T hKH hT, borel H K T hKH hT⁆ ≤ (borel H K T hKH hT).pCoreIn 2)
    (hindex : (C ⊔ J.pCoreIn 2).relIndex J = 3)
    (t : H) (ht : t.val ∈ T)
    (htB : t.val ∈ normalizer (borel H K T hKH hT : Set G))
    (htJ : t.val ∈ normalizer (J : Set G))
    (hCt : ⁅C, zpowers t.val⁆ ≤ C.pCoreIn 2) :
    FixesTorus (residualAt (sourceSylow H K T hT)) (markedActor H K T t ht) ∧
      commutatorOrder (residualAt (sourceSylow H K T hT)) (markedActor H K T t ht) ≤ 3 := by
  let B := borel H K T hKH hT
  let N := C ⊔ J.pCoreIn 2
  have hBJ : B ≤ J := hJD ▸ le_sup_left
  have hBH : B ≤ H := hBJ.trans hJH
  have hNH : N ≤ H := (sup_le hCJ (pCoreIn_le 2 J)).trans hJH
  have hBN : B ≤ normalizer (N : Set G) :=
    hBJ.trans (overgroup_normalizes_auxiliary C J hJC)
  have hRN : residualIn 3 B ≤ N := hR.trans
    (sup_le le_sup_left (core_le_auxiliary B C J hBJ hJB))
  have hNt : ⁅N, zpowers t.val⁆ ≤ N.pCoreIn 2 :=
    auxiliary_commutator_core C J hCJ hJC t.val htJ hCt
  constructor
  · apply markedActor_fixes_of_centralizer H K T hKH hT t ht (Source.starImage H N)
    · exact starImage_normalizes H B N hBN
    · rw [← starImage_residualIn 3 H B hBH]
      exact map_mono (comap_mono hRN)
    · exact starImage_displacement H N hNH t hNt
  · apply markedActor_commutatorOrder_le H K T hKH hT t ht 3
    exact (commutator_twoCore_card_le_overgroup B C J D hJD hCJ hJB hJC
      hab t.val htB htJ hCt).trans_eq hindex

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation
