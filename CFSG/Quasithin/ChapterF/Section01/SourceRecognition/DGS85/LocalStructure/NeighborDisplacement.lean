module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.NeighborCenterCentralizer
public import Theory.Representation.SL2.TwoSubgroupFixedIndex

/-!
# Sharp actor displacement on the neighboring center

In the noncentral linear branch of DGS (6.5), the actual neighboring
center has centralizer O₂(X) in the closure X. Descending its conjugation
action along the original marked quotient therefore gives a faithful
SL₂ action. Every actor outside O₂(X) moves at least the field order,
which is exactly [Q_delta:O₂(X)]. For the field of two, nontriviality
of the action gives the same bound directly.

Both the action and the fixed-subgroup index are transported through
the literal closure embedding. No natural-module or displacement
assumption is added. The noncentrality hypothesis is the source branch
condition; the larger-field central exclusion remains separate.

Source: DGS, Groups and Graphs (1985), (6.5), pp.121--122; Niles,
Pushing-up in finite groups (1979), Lemma 4.3. The bound feeds the actual
core-pair contradiction in LinearNoncentralObstruction.
-/


open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open CFSG.Quasithin.ChapterF.DGS85.BaumannApplication
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem source_linear_neighbor_center_displacement_large (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2) (d : LocalRankOneData (P (other i)) B)
    (hn : localEnlargement d ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    (q : localEnlargement d →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (localEnlargement d))
    (hnc : ¬ sylowCenterSpan (P (other i)) ≤ centralizer
      (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) : Set G))
    {n : ℕ} (hnF : 1 < n) (hF : Nat.card F = 2^n) :
    let A := (P i).pCoreIn 2
    let X := conjugateSpanBy A (P (other i))
    ∀ a ∈ A, a ∉ X.pCoreIn 2 →
      (X.pCoreIn 2).relIndex A ≤
        (centralizer ({a} : Set G)).relIndex (sylowCenterSpan (P (other i))) := by
  let := d.finite_P
  let A := (P i).pCoreIn 2
  let X := conjugateSpanBy A (P (other i))
  let Z := sylowCenterSpan (P (other i))
  let C := coreClosure (P i) (P (other i))
  let ι := originalEmbedding (P i) (P (other i))
  have hinj := MarkedClosure.originalEmbedding_injective (P i) (P (other i))
  have hAP : A ≤ P (other i) :=
    (source_core_le_borel (Classical.choice (h.local_data i))).trans
      (le_sup_right.trans d.supplement.le)
  have hrange : ι.range = X := MarkedClosure.originalEmbedding_range _ _ hAP
  have hZX : Z ≤ X := source_center_le_core_closure h hB hS i
  obtain ⟨hi,qX,hqX,hkX,_⟩ := source_linear_closure_premises h hB hS i d hn q hq hk
  let T := coreSylow (P i) (P (other i)) hi
  let Vi := BaumannBinary.centerClosure (T : Subgroup C)
  let Zi := Z.comap ι
  let : IsElementaryAbelian 2 Vi :=
    (BaumannBinary.centerClosure_reduced T (MarkedClosure.selfCentralizing h i)).elementary
  have hVi : Vi.map ι = conjugateSpanBy (omegaCenterIn A) X :=
    MarkedClosure.centerClosure_image _ _ hAP
  have hZi : Zi.map ι = Z := by
    apply le_antisymm (map_comap_le _ _)
    intro z hz
    obtain ⟨x,rfl⟩ := (hrange.symm ▸ hZX hz : z ∈ ι.range)
    exact mem_map.mpr ⟨x,hz,rfl⟩
  have hZiVi : Zi ≤ Vi := (map_le_map_iff_of_injective hinj).mp (by
    rw [hZi,hVi]
    exact source_neighbor_center_le_baumann h hB hS i ((inter_core_local_normal_iff h i d).mp hn))
  let : IsElementaryAbelian 2 Zi := IsElementaryAbelian.of_le hZiVi
  have hZnorm : P (other i) ≤ normalizer (Z : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (sylowCenterSpan_le _)).mp (sylowCenterSpan_normal _)
  let : Zi.Normal := ⟨by
    intro z hz g
    change ι (g*z*g⁻¹) ∈ Z
    rw [map_mul,map_mul,map_inv]
    exact le_normalizer_iff.mp hZnorm (ι g) g.val.property (ι z) hz⟩
  have hcent : (centralizer (Zi : Set C)).map ι = X.pCoreIn 2 := by
    have hh := map_inf_centralizer_of_injective ι hinj ⊤ Zi
    rw [top_inf_eq,hZi,←MonoidHom.range_eq_map,hrange] at hh
    exact hh.symm.trans (source_linear_neighbor_center_centralizer h hB hS i d hn q hq hk hnc).1
  have hker : qX.ker = centralizer (Zi : Set C) := by
    apply map_injective hinj
    rw [hkX,hcent]
    exact MarkedClosure.core_image _ _ hAP
  dsimp only
  intro a ha hao
  obtain ⟨a',haT,hea⟩ := (show a ∈ (T : Subgroup C).map ι from
    (coreSylow_image (P i) (P (other i)) hAP hi).symm ▸ ha)
  have hna : ¬ zpowers a' ≤ qX.ker := by
    intro hh
    apply hao
    rw [←hea,←MarkedClosure.core_image (P i) (P (other i)) hAP,←hkX]
    exact mem_map_of_mem ι (hh (mem_zpowers a'))
  have hl := Representation.SL2.normal_two_subgroup_fixed_index_lower Zi qX hqX hker
    hnF hF (zpowers a') (T.isPGroup'.to_le (zpowers_le.mpr haT)) hna
  have hm := relIndex_map_map_of_injective (Zi ⊓ centralizer (zpowers a' : Set C)) Zi
    (f := ι) hinj
  rw [hZi,←map_inf_centralizer_of_injective ι hinj,hZi,MonoidHom.map_zpowers,
    hea,inf_relIndex_left,inf_relIndex_left,zpowers_eq_closure,centralizer_closure] at hm
  rw [hm,source_linear_closure_core_relIndex h hB hS i d hn q hq hk]
  exact hl
/-- Every escaping actor moves at least the marked field order on the actual neighboring center. -/
theorem source_linear_neighbor_center_displacement (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2) (d : LocalRankOneData (P (other i)) B)
    (hn : localEnlargement d ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    (q : localEnlargement d →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (localEnlargement d))
    (hnc : ¬ sylowCenterSpan (P (other i)) ≤ centralizer
      (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) : Set G)) :
    let A := (P i).pCoreIn 2
    let X := conjugateSpanBy A (P (other i))
    ∀ a ∈ A, a ∉ X.pCoreIn 2 →
      (X.pCoreIn 2).relIndex A ≤
        (centralizer ({a} : Set G)).relIndex (sylowCenterSpan (P (other i))) := by
  let := d.finite_P
  let := Fintype.ofFinite F
  obtain ⟨n,_,hFn⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2^n.val := (Nat.card_eq_fintype_card (α := F)).trans hFn
  by_cases hnF : 1 < n.val
  · exact source_linear_neighbor_center_displacement_large h hB hS i d hn q hq hk hnc hnF hF
  have hn1 : n.val = 1 := by
    have hnp : 0 < n.val := n.property
    omega
  have hF2 : Nat.card F = 2 := by simpa only [hn1,pow_one] using hF
  have hc := (source_linear_neighbor_center_centralizer h hB hS i d hn q hq hk hnc).2
  let Z := sylowCenterSpan (P (other i))
  let : Finite Z := Finite.of_injective (inclusion (sylowCenterSpan_le (P (other i))))
    (inclusion_injective _)
  dsimp only
  intro a ha hao
  rw [source_linear_closure_core_relIndex h hB hS i d hn q hq hk,hF2]
  have hne : (centralizer ({a} : Set G)).relIndex Z ≠ 1 := by
    intro hh
    apply hao
    rw [←hc]
    refine ⟨ha,?_⟩
    intro z hz
    exact (mem_centralizer_singleton_iff.mp (relIndex_eq_one.mp hh hz))
  have hp : (centralizer ({a} : Set G)).relIndex Z ≠ 0 := index_ne_zero_of_finite
  change 2 ≤ (centralizer ({a} : Set G)).relIndex Z
  omega

end CFSG.Quasithin.ChapterF.Source.DGS85
