module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearCoreProduct
public import Theory.GroupTheory.PushingUp.BaumannBinary.AmbientNaturalCenter

/-!
# Excluding the central-center alternative for every binary linear field

Under contrary adjacent-core normality, the source linear (6.4) product
places an ambient Sylow in X O₂(G_lambda). The natural Baumann module has
a noncentral Sylow-fixed vector in its moving part; the ambient two-core
centralizes this part. Hence the original Sylow-center span cannot
centralize X. This removes the field-size restriction from the central
case of (6.5), without assuming a split module or a finite completion.

Source: DGS, Groups and Graphs (1985), (6.4)--(6.5), pp.120--122.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open CFSG.Quasithin.ChapterF.DGS85.BaumannApplication
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The linear 6.5 central case is impossible for the literal adjacent closure. -/
theorem source_linear_neighbor_center_noncentral (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2) (d : LocalRankOneData (P (other i)) B)
    (hn : localEnlargement d ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    (q : localEnlargement d →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (localEnlargement d)) :
    ¬ sylowCenterSpan (P (other i)) ≤ centralizer
      (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) : Set G) := by
  let := d.finite_P
  let C := coreClosure (P i) (P (other i))
  let : C.Normal := normalClosure_normal
  have hAP : (P i).pCoreIn 2 ≤ P (other i) :=
    (source_core_le_borel (Classical.choice (h.local_data i))).trans
      (le_sup_right.trans d.supplement.le)
  obtain ⟨hi,qX,hqX,hkX,_⟩ := source_linear_closure_premises h hB hS i d hn q hq hk
  obtain ⟨T,hTB⟩ := hS (other i)
  have hT := sylow_image_eq_edge_core (P (other i)) B
    (le_sup_right.trans d.supplement.le) hB T hTB
  have hprod := (source_linear_core_product h hB hS i d hn q hq hk).1
  have hcover : (T : Subgroup (P (other i))) ≤ C ⊔ pCore 2 (P (other i)) := by
    apply (map_le_map_iff_of_injective (P (other i)).subtype_injective).mp
    rw [Subgroup.map_sup,hT,MarkedClosure.coreClosure_image (P i) (P (other i)) hAP,←hprod]
    exact sup_le_sup (le_conjugateSpanBy _ _) le_rfl
  have hnc := BaumannBinary.ambient_sylow_omega_noncentral_of_core_cover C
    (coreSylow (P i) (P (other i)) hi) T (MarkedClosure.selfCentralizing h i)
    (MarkedClosure.noCharacteristicNormal h hB i d hn) qX hqX hkX hcover
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

/-- The original F1.11 linear quotient discharges noncentrality on its reduced graph. -/
theorem reduced_linear_neighbor_center_noncentral (h : HypothesisF11 L S) (i : Fin 2)
    (hn : localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤
      normalizer (↑(((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
        ((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2) : Set (G₀ L S)))
    (e : (L (other i) ⧸ pCore 2 (L (other i))) ≃* PSL(2,F)) :
    ¬ sylowCenterSpan ((P₀ L S (other i)).subgroupOf (G₀ L S)) ≤ centralizer
      (conjugateSpanBy (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2)
        ((P₀ L S (other i)).subgroupOf (G₀ L S)) : Set (G₀ L S)) := by
  let d := Classical.choice ((reduced_triple h).local_data (other i))
  let f := reduced_linearEnlargementQuotient h (other i) d e
  let q := f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localEnlargement d)))
  have hq : Function.Surjective q := f.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 (localEnlargement d) := by
    rw [MonoidHom.ker_comp_of_injective _ _ f.injective,QuotientGroup.ker_mk']
  exact source_linear_neighbor_center_noncentral (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) i d hn q hq hk

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
