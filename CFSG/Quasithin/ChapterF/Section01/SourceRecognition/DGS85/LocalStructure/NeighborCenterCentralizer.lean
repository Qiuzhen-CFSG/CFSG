module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.BinaryCenterExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearCoreProduct
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# Exact centralizers of the neighboring center in the linear 6.5 branch

In the noncentral alternative Z_lambda covers the Baumann module modulo
its central part. Consequently its centralizer in X is the Baumann action
kernel O₂(X). Intersecting with the original Sylow Q_delta retains exactly
that same core. The marked linear quotient also gives the literal index
[Q_delta:O₂(X)] = |F|.

The reduced binary F1.11 application uses the central-case exclusion, so
its two centralizer identities and index-two conclusion need no separate
noncentrality hypothesis. Relative normality is still the contrary
assumption in the proof of 6.5.

Source: DGS, Groups and Graphs (1985), 6.5, pp.121–122. These centralizers
are the input to the subsequent conjugate-core and Frattini calculation.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open CFSG.Quasithin.ChapterF.DGS85.BaumannApplication
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The neighboring center has exactly the closure core as its centralizer in X and Q_delta. -/
theorem source_linear_neighbor_center_centralizer (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2) (d : LocalRankOneData (P (other i)) B)
    (hn : localEnlargement d ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    (q : localEnlargement d →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (localEnlargement d))
    (hnc : ¬ sylowCenterSpan (P (other i)) ≤ centralizer
      (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) : Set G)) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    X ⊓ centralizer (sylowCenterSpan (P (other i)) : Set G) = X.pCoreIn 2 ∧
      (P i).pCoreIn 2 ⊓ centralizer (sylowCenterSpan (P (other i)) : Set G) = X.pCoreIn 2 := by
  let := d.finite_P
  let C := coreClosure (P i) (P (other i))
  let ι := originalEmbedding (P i) (P (other i))
  let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
  let V := conjugateSpanBy (omegaCenterIn ((P i).pCoreIn 2)) X
  let Z := sylowCenterSpan (P (other i))
  have hAP : (P i).pCoreIn 2 ≤ P (other i) :=
    (source_core_le_borel (Classical.choice (h.local_data i))).trans
      (le_sup_right.trans d.supplement.le)
  obtain ⟨hi,qX,hqX,hkX,_⟩ := source_linear_closure_premises h hB hS i d hn q hq hk
  let T := coreSylow (P i) (P (other i)) hi
  let Vi := BaumannBinary.centerClosure (T : Subgroup C)
  let := Fintype.ofFinite F
  obtain ⟨n,_,hF⟩ := FiniteField.card F 2
  have hker : centralizer (Vi : Set C) = pCore 2 C :=
    BaumannBinary.centerClosure_centralizer T (MarkedClosure.selfCentralizing h i)
      (MarkedClosure.noCharacteristicNormal h hB i d hn) qX hqX hkX n.property
      ((Nat.card_eq_fintype_card (α := F)).trans hF)
  have hVC : X ⊓ centralizer (V : Set G) = X.pCoreIn 2 := by
    have hVi : Vi.map ι = V := MarkedClosure.centerClosure_image _ _ hAP
    have htop : (⊤ : Subgroup C).map ι = X := by
      rw [←MonoidHom.range_eq_map]
      exact MarkedClosure.originalEmbedding_range _ _ hAP
    have hm := map_inf_centralizer_of_injective ι
      (MarkedClosure.originalEmbedding_injective _ _) ⊤ Vi
    rw [hVi,htop,top_inf_eq,hker] at hm
    exact hm.trans (MarkedClosure.core_image _ _ hAP)
  have hZV : Z ≤ V := source_neighbor_center_le_baumann h hB hS i
    ((inter_core_local_normal_iff h i d).mp hn)
  have hcover : Z ⊔ (V ⊓ centralizer (X : Set G)) = V :=
    (source_linear_neighbor_center_alternative h hB hS i d hn q hq hk).resolve_left hnc
  have he : X ⊓ centralizer (Z : Set G) = X.pCoreIn 2 := by
    rw [←hVC]
    apply le_antisymm ?_ (inf_le_inf_left _ (centralizer_le hZV))
    intro x hx
    refine ⟨hx.1,?_⟩
    have hv : V ≤ centralizer ({x} : Set G) := by
      rw [←hcover]
      apply sup_le
      · intro z hz
        exact mem_centralizer_singleton_iff.mpr (hx.2 z hz)
      · intro z hz
        exact mem_centralizer_singleton_iff.mpr ((hz.2 x hx.1).symm)
    intro v hv'
    exact mem_centralizer_singleton_iff.mp (hv hv')
  refine ⟨he,?_⟩
  apply le_antisymm
  · exact (inf_le_inf_right _ (le_conjugateSpanBy _ _)).trans he.le
  · exact le_inf ((source_linear_core_product h hB hS i d hn q hq hk).2.le.trans inf_le_left)
      (he.ge.trans inf_le_right)

/-- The original Sylow/core index is the cardinality of the marked field. -/
theorem source_linear_closure_core_relIndex (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2) (d : LocalRankOneData (P (other i)) B)
    (hn : localEnlargement d ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    (q : localEnlargement d →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (localEnlargement d)) :
    ((conjugateSpanBy ((P i).pCoreIn 2) (P (other i))).pCoreIn 2).relIndex
      ((P i).pCoreIn 2) = Nat.card F := by
  let := d.finite_P
  obtain ⟨hi,qX,hqX,hkX,_⟩ := source_linear_closure_premises h hB hS i d hn q hq hk
  have hAP : (P i).pCoreIn 2 ≤ P (other i) :=
    (source_core_le_borel (Classical.choice (h.local_data i))).trans
      (le_sup_right.trans d.supplement.le)
  have hm := relIndex_map_map_of_injective
    (pCore 2 (coreClosure (P i) (P (other i))))
    (coreSylow (P i) (P (other i)) hi : Subgroup _)
    (MarkedClosure.originalEmbedding_injective (P i) (P (other i)))
  rw [MarkedClosure.core_image _ _ hAP,coreSylow_image _ _ hAP] at hm
  exact hm.trans (Matrix.SpecialLinearGroup.sylow_core_relIndex qX hqX hkX
    (coreSylow (P i) (P (other i)) hi))

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The reduced binary branch has an index-two closure core, exactly the
centralizer of its neighboring center inside the original adjacent core. -/
theorem reduced_binary_neighbor_center_centralizer (h : HypothesisF11 L S) (i : Fin 2)
    (hn : localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤
      normalizer (↑(((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
        ((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2) : Set (G₀ L S)))
    (e : (L (other i) ⧸ pCore 2 (L (other i))) ≃* PSL(2,F)) (hF : Nat.card F = 2) :
    let A := ((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2
    let X := conjugateSpanBy A ((P₀ L S (other i)).subgroupOf (G₀ L S))
    let Z := sylowCenterSpan ((P₀ L S (other i)).subgroupOf (G₀ L S))
    X ⊓ centralizer (Z : Set (G₀ L S)) = X.pCoreIn 2 ∧
      A ⊓ centralizer (Z : Set (G₀ L S)) = X.pCoreIn 2 ∧
      (X.pCoreIn 2).relIndex A = 2 := by
  let d := Classical.choice ((reduced_triple h).local_data (other i))
  let f := reduced_linearEnlargementQuotient h (other i) d e
  let q := f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localEnlargement d)))
  have hq : Function.Surjective q := f.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 (localEnlargement d) := by
    rw [MonoidHom.ker_comp_of_injective _ _ f.injective,QuotientGroup.ker_mk']
  have hnc := reduced_binary_neighbor_center_noncentral h i hn e hF
  have hc := source_linear_neighbor_center_centralizer (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) i d hn q hq hk hnc
  exact ⟨hc.1,hc.2,(source_linear_closure_core_relIndex (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) i d hn q hq hk).trans hF⟩

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
