module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearClosure
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The two adjacent cores and the full Borel Sylow

With the original linear quotient marking and the contrary relative normality
of DGS 6.4, the adjacent-core closure maps onto the local quotient. Its proved
Sylow subgroup is the first core. Intersecting the full Borel Sylow with that
closure and factoring through the other core proves that the product of the
two cores is exactly O₂(B). The closure core is their literal intersection.
All subgroups remain inside the given completion, which may be infinite.

Source: DGS, Groups and Graphs (1985), 6.4(a,c), printed pp.120--121.
This is the linear case; model selection and the 6.5 contradiction remain.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative Pointwise
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open CFSG.Quasithin.ChapterF.DGS85.BaumannApplication
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The last product clause of DGS 6.4 in the marked linear case, and the exact closure core. -/
theorem source_linear_core_product (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2) (d : LocalRankOneData (P (other i)) B)
    (hn : localEnlargement d ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    (q : localEnlargement d →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (localEnlargement d)) :
    (P i).pCoreIn 2 ⊔ (P (other i)).pCoreIn 2 = B.pCoreIn 2 ∧
    (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))).pCoreIn 2 =
      (P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2 := by
  let := d.finite_P
  let J := localEnlargement d
  let : Finite J := Finite.of_injective (inclusion (localEnlargement_le d)) (inclusion_injective _)
  have hBP : B ≤ P (other i) := le_sup_right.trans d.supplement.le
  let : Finite B := Finite.of_injective (inclusion hBP) (inclusion_injective _)
  let A := (P i).pCoreIn 2
  let N := (P (other i)).pCoreIn 2
  let X := conjugateSpanBy A (P (other i))
  have hAJ : A ≤ J := (pGroup_le_core_of_core_sylow B A
    (source_core_le_borel (Classical.choice (h.local_data i))) (isPGroup_pCoreIn 2 _) hB).trans le_sup_right
  have hAP := hAJ.trans (localEnlargement_le d)
  have hXJ : X ≤ J := core_closure_le_localEnlargement h hB i d
  have hXP : X ≤ P (other i) := hXJ.trans (localEnlargement_le d)
  have hNJ : N ≤ J := (source_core_le_star d).trans le_sup_left
  have hNS : N ≤ B.pCoreIn 2 := pGroup_le_core_of_core_sylow B N
    (source_core_le_borel d) (isPGroup_pCoreIn 2 _) hB
  have hAS : A ≤ B.pCoreIn 2 := pGroup_le_core_of_core_sylow B A
    (source_core_le_borel (Classical.choice (h.local_data i))) (isPGroup_pCoreIn 2 _) hB
  obtain ⟨hi,qX,hqX,hkX,hcompat⟩ := source_linear_closure_premises h hB hS i d hn q hq hk
  let W := coreSylow (P i) (P (other i)) hi
  have hWA : (W : Subgroup (coreClosure (P i) (P (other i)))).map
      (originalEmbedding (P i) (P (other i))) = A := coreSylow_image _ _ hAP hi
  have hcore : X.pCoreIn 2 = A ⊓ N := by
    apply le_antisymm _ (core_inter_le_closure_core h i)
    refine le_inf ?_ (pCoreIn_mono_of_normalizes hXP (le_normalizer_conjugateSpanBy _ _))
    rw [← MarkedClosure.core_image (P i) (P (other i)) hAP]
    exact (map_mono (pCore_isPGroup.le_sylow_of_normal W)).trans_eq hWA
  have hXq : (X.subgroupOf J).map q = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨x,rfl⟩ := hqX y
    obtain ⟨a,ha,he⟩ := hcompat x
    refine mem_map.mpr ⟨a,?_,he.symm⟩
    change (a : G) ∈ X
    rw [ha]
    change originalEmbedding (P i) (P (other i)) x ∈ conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    rw [←MarkedClosure.originalEmbedding_range (P i) (P (other i)) hAP]
    exact ⟨x,rfl⟩
  have hXN : X ⊔ N = J := by
    have he := congrArg (Subgroup.comap q) hXq
    rw [comap_map_eq,hk,comap_top] at he
    have hm := congrArg (Subgroup.map J.subtype) he
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hXJ,←MonoidHom.range_eq_map,range_subtype] at hm
    change X ⊔ J.pCoreIn 2 = J at hm
    rwa [localEnlargement_core d] at hm
  have hSXA : B.pCoreIn 2 ⊓ X ≤ A := by
    let f := originalEmbedding (P i) (P (other i))
    have hp : IsPGroup 2 ((B.pCoreIn 2).comap f) :=
      (isPGroup_pCoreIn 2 B).comap_of_injective f (MarkedClosure.originalEmbedding_injective _ _)
    have hW : (B.pCoreIn 2).comap f = W := W.is_maximal' hp (by
      intro x hx
      exact hAS (hWA ▸ mem_map_of_mem f hx))
    intro x hx
    change x ∈ B.pCoreIn 2 ⊓ conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) at hx
    rw [←MarkedClosure.originalEmbedding_range (P i) (P (other i)) hAP] at hx
    obtain ⟨a,ha⟩ := hx.2
    have haW : a ∈ (W : Subgroup (coreClosure (P i) (P (other i)))) := by
      rw [←hW]
      change f a ∈ B.pCoreIn 2
      rw [ha]
      exact hx.1
    exact hWA ▸ mem_map.mpr ⟨a,haW,ha⟩
  have hprod : A ⊔ N = B.pCoreIn 2 := by
    apply le_antisymm (sup_le hAS hNS)
    intro s hs
    have hsj : s ∈ X ⊔ N := hXN.symm ▸ (show s ∈ J from (show B.pCoreIn 2 ≤ J from le_sup_right) hs)
    have hnN : X ≤ normalizer (N : Set G) := hXP.trans
      ((P (other i)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (P (other i)))))
    have hset := coe_mul_of_left_le_normalizer_right X N hnN
    change s ∈ (↑(X ⊔ N) : Set G) at hsj
    rw [hset] at hsj
    obtain ⟨x,hx,n,hnN,rfl⟩ := hsj
    have hxs : x ∈ B.pCoreIn 2 := by
      have hh := (B.pCoreIn 2).mul_mem hs ((B.pCoreIn 2).inv_mem (hNS hnN))
      simpa only [mul_inv_cancel_right] using hh
    exact (A ⊔ N).mul_mem ((show A ≤ A ⊔ N from le_sup_left) (hSXA ⟨hxs,hx⟩))
      ((show N ≤ A ⊔ N from le_sup_right) hnN)
  exact ⟨hprod,hcore⟩
end CFSG.Quasithin.ChapterF.Source.DGS85

namespace CFSG.Quasithin.ChapterF.Source.DGS85
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The join in 6.4 is the literal subgroup product, and is Sylow at both full endpoints. -/
theorem source_linear_core_product_sylows (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2) (d : LocalRankOneData (P (other i)) B)
    (hn : localEnlargement d ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    (q : localEnlargement d →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (localEnlargement d)) :
    (↑(B.pCoreIn 2) : Set G) = ((P i).pCoreIn 2 : Set G) * ((P (other i)).pCoreIn 2 : Set G) ∧
      ∀ j, ∃ T : Sylow 2 (P j), (T : Subgroup (P j)).map (P j).subtype =
        (P i).pCoreIn 2 ⊔ (P (other i)).pCoreIn 2 := by
  have he := (source_linear_core_product h hB hS i d hn q hq hk).1
  constructor
  · rw [←he]
    apply coe_mul_of_left_le_normalizer_right
    exact ((source_core_le_borel (Classical.choice (h.local_data i))).trans
      (le_sup_right.trans d.supplement.le)).trans
        ((P (other i)).le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image _ (pCore 2 (P (other i)))))
  · intro j
    let := (Classical.choice (h.local_data j)).finite_P
    obtain ⟨T,hT⟩ := hS j
    refine ⟨T,?_⟩
    rw [he]
    exact sylow_image_eq_edge_core _ B
      (le_sup_right.trans (Classical.choice (h.local_data j)).supplement.le) hB T hT

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The linear 6.4 product on the original F1.11 parabolic cores equals the
original full Borel's actual two-core, without identifying it with original S. -/
theorem reduced_original_linear_core_product (h : HypothesisF11 L S) (i : Fin 2)
    (hn : enlargedEndpoint L S (other i) ≤ normalizer
      (↑((parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2) : Set G))
    (e : (L (other i) ⧸ pCore 2 (L (other i))) ≃* PSL(2,F)) :
    (parabolic L S i).pCoreIn 2 ⊔ (parabolic L S (other i)).pCoreIn 2 =
      (commonBorel L S).pCoreIn 2 := by
  have hPG (j : Fin 2) : P₀ L S j ≤ G₀ L S := by
    fin_cases j
    · exact le_sup_left
    · exact le_sup_right
  have hBG : B₀ L S ≤ G₀ L S :=
    (show B₀ L S ≤ P₀ L S 0 from le_sup_right).trans le_sup_left
  have hcore (j : Fin 2) : (((P₀ L S j).subgroupOf (G₀ L S)).pCoreIn 2).map
      (G₀ L S).subtype = (parabolic L S j).pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 _ _ (G₀ L S).subtype_injective,
      map_subgroupOf_eq_of_le (hPG j),P₀_core h j]
  have hD : ((((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
      ((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2) : Subgroup (G₀ L S)).map
      (G₀ L S).subtype = (parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2 := by
    rw [Subgroup.map_inf _ _ _ (G₀ L S).subtype_injective,hcore,hcore]
  let d := Classical.choice ((reduced_triple h).local_data (other i))
  have hn0 : localEnlargement d ≤ normalizer
      (↑(((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
        ((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2) : Set (G₀ L S)) := by
    intro x hx
    have hxl : (x : G) ∈ enlargedEndpoint L S (other i) := by
      rw [←reduced_localEnlargement_image h (other i) d]
      exact mem_map_of_mem (G₀ L S).subtype hx
    have hxn := le_normalizer_comap (G₀ L S).subtype (hn hxl)
    rwa [←hD,comap_map_eq_self_of_injective (G₀ L S).subtype_injective] at hxn
  let f := reduced_linearEnlargementQuotient h (other i) d e
  let q := f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localEnlargement d)))
  have hq : Function.Surjective q := f.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 (localEnlargement d) := by
    rw [MonoidHom.ker_comp_of_injective _ _ f.injective,QuotientGroup.ker_mk']
  have hm := congrArg (Subgroup.map (G₀ L S).subtype)
    (source_linear_core_product (reduced_triple h) (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) i d hn0 q hq hk).1
  rw [Subgroup.map_sup,hcore,hcore,map_pCoreIn_of_injective 2 _ _ (G₀ L S).subtype_injective,
    map_subgroupOf_eq_of_le hBG,B₀_core h] at hm
  exact hm
end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
