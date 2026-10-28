module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearCenterAlternative
public import Theory.GroupTheory.PushingUp.BaumannBinary.AmbientCenter

/-!
# Excluding the central-center alternative over the field of two

The contrary relative-normality assumption and the original linear local
marking supply all 6.4 premises on the actual adjacent-core closure.
Its Baumann module has faithful S₃ action. Coprime movement of the cubic
residual meets every ambient Sylow omega-center, so the neighboring
Sylow-center span cannot centralize the closure.

The reduced F1.11 application constructs the marking from the original
local PSL₂ quotient. No finite completion, equality of the local kernel
and two-core, or noncentrality input is imposed.

Source: DGS, Groups and Graphs (1985), 6.5, printed p.121, q_lambda = 2.
The larger-field central case and the subsequent two-core contradiction
remain separate steps in the same source proof.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open CFSG.Quasithin.ChapterF.DGS85.BaumannApplication
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The field-of-two 6.5 central case is impossible for the literal adjacent closure. -/
theorem source_binary_neighbor_center_noncentral (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2) (d : LocalRankOneData (P (other i)) B)
    (hn : localEnlargement d ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    (q : localEnlargement d →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (localEnlargement d)) (hF : Nat.card F = 2) :
    ¬ sylowCenterSpan (P (other i)) ≤ centralizer
      (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) : Set G) := by
  let := d.finite_P
  let C := coreClosure (P i) (P (other i))
  let : C.Normal := normalClosure_normal
  have hAP : (P i).pCoreIn 2 ≤ P (other i) :=
    (source_core_le_borel (Classical.choice (h.local_data i))).trans
      (le_sup_right.trans d.supplement.le)
  obtain ⟨hi,qX,hqX,hkX,_⟩ := source_linear_closure_premises h hB hS i d hn q hq hk
  obtain ⟨T⟩ := Sylow.nonempty (p := 2) (G := P (other i))
  have hnc := BaumannBinary.ambient_sylow_omega_noncentral_two C
    (coreSylow (P i) (P (other i)) hi) T (MarkedClosure.selfCentralizing h i)
    (MarkedClosure.noCharacteristicNormal h hB i d hn) qX hqX hkX hF
  intro hz
  apply hnc
  intro z hzT c hc
  have hzspan : (z : G) ∈ sylowCenterSpan (P (other i)) := by
    apply (le_iSup (fun R : Sylow 2 (P (other i)) =>
      omegaCenterIn ((R : Subgroup (P (other i))).map (P (other i)).subtype)) T)
    rw [←NilesRankOneKernel.omegaCenterIn_map_injective _ (P (other i)).subtype_injective]
    exact mem_map_of_mem (P (other i)).subtype hzT
  have hcX : (c : G) ∈ conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) := by
    rw [←MarkedClosure.coreClosure_image (P i) (P (other i)) hAP]
    exact mem_map_of_mem (P (other i)).subtype hc
  exact Subtype.ext (hz hzspan c hcX)

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The original F1.11 binary quotient discharges noncentrality on its reduced graph. -/
theorem reduced_binary_neighbor_center_noncentral (h : HypothesisF11 L S) (i : Fin 2)
    (hn : localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤
      normalizer (↑(((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
        ((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2) : Set (G₀ L S)))
    (e : (L (other i) ⧸ pCore 2 (L (other i))) ≃* PSL(2,F)) (hF : Nat.card F = 2) :
    ¬ sylowCenterSpan ((P₀ L S (other i)).subgroupOf (G₀ L S)) ≤ centralizer
      (conjugateSpanBy (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2)
        ((P₀ L S (other i)).subgroupOf (G₀ L S)) : Set (G₀ L S)) := by
  let d := Classical.choice ((reduced_triple h).local_data (other i))
  let f := reduced_linearEnlargementQuotient h (other i) d e
  let q := f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localEnlargement d)))
  have hq : Function.Surjective q := f.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 (localEnlargement d) := by
    rw [MonoidHom.ker_comp_of_injective _ _ f.injective,QuotientGroup.ker_mk']
  exact source_binary_neighbor_center_noncentral (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) i d hn q hq hk hF

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
