module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearCenterAlternative
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearCoreProduct
public import Theory.GroupTheory.PResidual.SylowSupplement

open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
/-!
# A neighboring center escaping the adjacent closure core

Under the contrary 6.4 normality and the linear noncentral 6.5 alternative,
let X = <Q_delta^{G_lambda}>. If the span of Z_lambda under G_delta lay
in O₂(X), the core-residual commutator bound would make that span invariant
under O²(X). The actual Q_delta Sylow supplements O²(X), so the span is
normal in X and then in G_lambda = XB. Faithfulness kills it, contradicting
the nontrivial rank-one center. Thus a conjugate center escapes O₂(X).

The common full-Borel Sylow also proves that this neighbor span includes
Z_delta, and hence is the literal closed radius-one span V_delta. No finite
completion, tree, or equality of the core and local kernel is used.

Source: DGS, Groups and Graphs (1985), 6.5, printed p.122. This proves the
escape step in the noncentral linear case, not the final 6.5 contradiction.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open CFSG.Quasithin.ChapterF.DGS85.BaumannApplication
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The noncentral linear 6.5 center span escapes the actual closure core. -/
theorem source_linear_neighbor_span_escape (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2) (d : LocalRankOneData (P (other i)) B)
    (hn : localEnlargement d ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    (q : localEnlargement d →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (localEnlargement d))
    (hnc : ¬ sylowCenterSpan (P (other i)) ≤ centralizer
      (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) : Set G)) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    ¬ conjugateSpanBy (sylowCenterSpan (P (other i))) (P i) ≤ X.pCoreIn 2 := by
  let := d.finite_P
  let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
  let W := conjugateSpanBy (sylowCenterSpan (P (other i))) (P i)
  have hBP (j : Fin 2) : B ≤ P j := le_sup_right.trans (Classical.choice (h.local_data j)).supplement.le
  have hAP : (P i).pCoreIn 2 ≤ P (other i) :=
    (source_core_le_borel (Classical.choice (h.local_data i))).trans (hBP _)
  have hXP : X ≤ P (other i) := conjugateSpanBy_le_self hAP
  let : Finite X := Finite.of_injective (inclusion hXP) (inclusion_injective _)
  have hn' := (inter_core_local_normal_iff h i d).mp hn
  have hnW : P i ≤ normalizer (W : Set G) := le_normalizer_conjugateSpanBy _ _
  obtain ⟨hi,_,_,_,_⟩ := source_linear_closure_premises h hB hS i d hn q hq hk
  let e := MarkedClosure.coreClosureEquiv (P i) (P (other i)) hAP
  let T := (coreSylow (P i) (P (other i)) hi).mapSurjective (f := e.toMonoidHom) e.surjective
  have hT : (T : Subgroup X).map X.subtype = (P i).pCoreIn 2 := by
    change (((coreSylow (P i) (P (other i)) hi : Subgroup _).map e.toMonoidHom).map X.subtype) = _
    rw [map_map]
    exact coreSylow_image _ _ hAP hi
  have hs : (pResidual 2 X).map X.subtype ⊔ (P i).pCoreIn 2 = X := by
    have hm := congrArg (Subgroup.map X.subtype) (pResidual_sup_sylow_eq_top T)
    rwa [Subgroup.map_sup,hT,←MonoidHom.range_eq_map,range_subtype] at hm
  change ¬ W ≤ X.pCoreIn 2
  intro hW
  have hRN : (pResidual 2 X).map X.subtype ≤ normalizer (W : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact (commutator_mono hW le_rfl).trans
      ((source_linear_noncentral_residual_bound h hB hS i d hn q hq hk hnc).trans
        (le_conjugateSpanBy _ _))
  have hXN : X ≤ normalizer (W : Set G) := by
    rw [←hs]
    exact sup_le hRN ((pCoreIn_le 2 (P i)).trans hnW)
  have hPN : P (other i) ≤ normalizer (W : Set G) := by
    rw [←core_closure_sup_borel_of_inter_normal h hB i hn']
    exact sup_le hXN ((hBP i).trans hnW)
  have hgen : P i ⊔ P (other i) = ⊤ := by
    fin_cases i
    · exact h.generate
    · exact (sup_comm _ _).trans h.generate
  let : W.Normal := normalizer_eq_top_iff.mp
    (top_le_iff.mp (hgen ▸ sup_le hnW hPN))
  have hWB : W ≤ B := hW.trans
    ((source_linear_core_product h hB hS i d hn q hq hk).2.le.trans
      (inf_le_left.trans (source_core_le_borel (Classical.choice (h.local_data i)))))
  exact source_centerSpan_ne_bot d (eq_bot_iff.mpr
    ((le_conjugateSpanBy _ _).trans (h.faithful W inferInstance hWB).le))


/-- The common full-Borel Sylow ensures the neighbor span contains the center vertex. -/
theorem source_neighbor_span_absorbs_center (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2) : sylowCenterSpan (P i) ≤
      conjugateSpanBy (sylowCenterSpan (P (other i))) (P i) := by
  let := (Classical.choice (h.local_data i)).finite_P
  let := (Classical.choice (h.local_data (other i))).finite_P
  obtain ⟨R,hR⟩ := hS i
  obtain ⟨T,hT⟩ := hS (other i)
  have hRi := sylow_image_eq_edge_core (P i) B
    (le_sup_right.trans (Classical.choice (h.local_data i)).supplement.le) hB R hR
  have hTj := sylow_image_eq_edge_core (P (other i)) B
    (le_sup_right.trans (Classical.choice (h.local_data (other i))).supplement.le) hB T hT
  rw [sylowCenterSpan_eq_conjugateSpan (P i) (P i) le_rfl
    (fun _ => map_subtype_le _) R]
  apply conjugateSpanBy_mono _ le_rfl
  rw [hRi,←hTj]
  exact le_iSup (fun R : Sylow 2 (P (other i)) =>
    omegaCenterIn ((R : Subgroup (P (other i))).map (P (other i)).subtype)) T

open Subgroup.CosetGeometry.RankTwo
/-- The closed radius-one span is exactly the adjacent-center orbit span. -/
theorem source_base_radius_one_eq_span (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (j : Bool) : V (family P) (base (family P) j) 1 =
      conjugateSpanBy (sylowCenterSpan (family P (!j))) (family P j) := by
  let := finite_endpoints h
  have hst (j : Bool) : stabilizer (family P) (base (family P) j) = family P j :=
    Subgroup.CosetGeometry.stabilizer_base _ _
  have hz (j : Bool) : Z (family P) (base (family P) j) = sylowCenterSpan (family P j) := by
    change sylowCenterSpan (stabilizer (family P) (base (family P) j)) = _
    rw [hst]
  have hadj : (graph (family P)).Adj (base (family P) j) (base (family P) (!j)) :=
    ⟨by cases j <;> exact Bool.noConfusion,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hcenter : Z (family P) (base (family P) j) ≤
      conjugateSpanBy (sylowCenterSpan (family P (!j))) (family P j) := by
    rw [hz]
    cases j
    · exact source_neighbor_span_absorbs_center h hB hS 0
    · exact source_neighbor_span_absorbs_center h hB hS 1
  apply le_antisymm
  · apply iSup_le
    intro w
    apply iSup_le
    intro hw
    rcases (mem_ball_one (family P) (base (family P) j) w).mp hw with hw | rfl
    · obtain ⟨g,hg,rfl⟩ := locally_transitive (family P) hadj hw
      rw [Z_translate,hz]
      rw [hst] at hg
      rintro z ⟨a,ha,rfl⟩
      exact subset_closure ⟨g,hg,a,ha,rfl⟩
    · exact hcenter
  · apply conjugateSpanBy_le
    · rw [←hz (!j)]
      exact le_iSup_of_le _ (le_iSup_of_le
        ((mem_ball_one _ _ _).mpr (Or.inl hadj)) le_rfl)
    · intro g hg
      rw [mem_normalizer_iff_map_conj_eq]
      change (V (family P) (base (family P) j) 1).map (MulAut.conj g).toMonoidHom = _
      rw [←V_translate]
      have hfix : g • base (family P) j = base (family P) j :=
        (show g ∈ stabilizer (family P) (base (family P) j) from (hst j).symm ▸ hg)
      rw [hfix]

/-- An actual endpoint element carries the neighboring center outside the closure core, while keeping it in the original vertex core. -/
theorem source_linear_escaping_conjugate (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2) (d : LocalRankOneData (P (other i)) B)
    (hn : localEnlargement d ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    (q : localEnlargement d →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (localEnlargement d))
    (hnc : ¬ sylowCenterSpan (P (other i)) ≤ centralizer
      (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) : Set G)) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    ∃ g ∈ P i, (sylowCenterSpan (P (other i))).map (MulAut.conj g).toMonoidHom ≤ (P i).pCoreIn 2 ∧
      ¬ (sylowCenterSpan (P (other i))).map (MulAut.conj g).toMonoidHom ≤ X.pCoreIn 2 := by
  dsimp only
  have hesc := source_linear_neighbor_span_escape h hB hS i d hn q hq hk hnc
  have hZQ : sylowCenterSpan (P (other i)) ≤ (P i).pCoreIn 2 :=
    (source_center_le_closure_core_omega h hB hS i).trans ((map_subtype_le _).trans
      ((source_linear_core_product h hB hS i d hn q hq hk).2.le.trans inf_le_left))
  have hspan : conjugateSpanBy (sylowCenterSpan (P (other i))) (P i) ≤ (P i).pCoreIn 2 :=
    conjugateSpanBy_le hZQ ((P i).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (P i) (pCore 2 (P i))))
  have hex : ∃ g : P i, ¬ (sylowCenterSpan (P (other i))).map
      (MulAut.conj (g : G)).toMonoidHom ≤
        (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))).pCoreIn 2 := by
    by_contra! hh
    apply hesc
    rw [conjugateSpanBy_eq_iSup_conj]
    exact iSup_le hh
  obtain ⟨g,hg⟩ := hex
  refine ⟨g,g.property,?_,hg⟩
  exact (le_iSup (fun g : P i => (sylowCenterSpan (P (other i))).map
    (MulAut.conj (g : G)).toMonoidHom) g).trans
      ((conjugateSpanBy_eq_iSup_conj _ _).symm.le.trans hspan)
end CFSG.Quasithin.ChapterF.Source.DGS85
