module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.ClosureCenterGeneration
public import Theory.GroupTheory.ConjugateSpanCentralizer

/-!
# The literal replacement span in the noncentral DGS 6.4 case

Under the contrary relative normality of the core intersection, the common
Borel omega-center puts Z_lambda in both original cores. If X does not
centralize Z_lambda, 6.2(c) makes the neighboring core Sylow in its center
centralizer. Thus Z_delta also lies in the intersection, and
V = <Z_delta^X> lies in its elementary center. This is the actual replacement
span printed in 6.4, distinct from Z_lambda and the Baumann omega-center span.

The same span is normalized by the full neighboring endpoint, is generated
by its Q_delta-fixed subgroup, and has nontrivial X-action. The fixed-generation
statement does not assert that Q_delta is Sylow in X. The central case and
corrected 5.12's Sylow, faithful catalogue and residual premises remain open.
Only the endpoints are finite; no finite completion is assumed.

Source: DGS, Groups and Graphs (1985), 6.2(c) and 6.4, pp.119--121;
the fixed-space-generation correction to 5.12, pp.113--115.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem borel_le (h : LocallyRankOneTriple P B) (i : Fin 2) : B ≤ P i :=
  le_sup_right.trans (Classical.choice (h.local_data i)).supplement.le

private theorem seed_le_core (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2) : omegaCenterIn (B.pCoreIn 2) ≤ (P i).pCoreIn 2 := by
  let := (Classical.choice (h.local_data i)).finite_P
  obtain ⟨T,hT⟩ := hS i
  rw [←sylow_image_eq_edge_core _ B (borel_le h i) hB T hT]
  exact (le_iSup (fun R : Sylow 2 (P i) => omegaCenterIn
    ((R : Subgroup (P i)).map (P i).subtype)) T).trans
      ((sylowCenterSpan_le_coreOmega _ (source_core_selfCentralizing
        (Classical.choice (h.local_data i)))).trans (map_subtype_le _))

/-- Under the contrary relative normality, the neighboring center lies in
both original cores, before any Sylow assertion about the closure. -/
theorem source_neighbor_center_le_inter (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) :
    sylowCenterSpan (P (other i)) ≤ (P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2 := by
  rw [source_neighbor_center_eq_seed_span h hB hS i hn]
  apply conjugateSpanBy_le (le_inf (seed_le_core h hB hS i) (seed_le_core h hB hS (other i)))
  exact (conjugateSpanBy_le_self ((source_core_le_borel
    (Classical.choice (h.local_data i))).trans (borel_le h _))).trans hn

/-- The noncentral case puts the opposite source center in the normal
intersection, using the actual 6.2(c) centralizer Sylow. -/
theorem source_opposite_center_le_inter_of_noncentral (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    (hnc : ¬ sylowCenterSpan (P (other i)) ≤ centralizer
      (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) : Set G)) :
    sylowCenterSpan (P i) ≤ (P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2 := by
  let d := Classical.choice (h.local_data (other i))
  let := d.finite_P
  let : Finite B := Finite.of_injective (inclusion (borel_le h (other i))) (inclusion_injective _)
  let Z := sylowCenterSpan (P i)
  let W := sylowCenterSpan (P (other i))
  let C := P (other i) ⊓ centralizer (W : Set G)
  have hZomega := sylowCenterSpan_le_coreOmega (P i)
    (source_core_selfCentralizing (Classical.choice (h.local_data i)))
  have hZQ : Z ≤ (P i).pCoreIn 2 := hZomega.trans (map_subtype_le _)
  have hWQ : W ≤ (P i).pCoreIn 2 := (source_neighbor_center_le_inter h hB hS i hn).trans inf_le_left
  have hZC : Z ≤ C := le_inf (hZQ.trans
    ((source_core_le_borel (Classical.choice (h.local_data i))).trans (borel_le h _)))
      (fun z hz => centralizer_le hWQ ((mem_omegaCenterIn_iff _ _).mp (hZomega hz)).2.1)
  have hnW : P (other i) ≤ normalizer (W : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (sylowCenterSpan_le _)).mp (sylowCenterSpan_normal _)
  rcases centralizer_sylow_or_span_eq (P (other i)) B (borel_le h _) (source_borel_maximal d)
      hB (hS (other i)) (source_core_selfCentralizing d) with hs | he
  · obtain ⟨T,hT⟩ := hs
    have hnC : P (other i) ≤ normalizer (C : Set G) :=
      (le_inf (P (other i)).le_normalizer
        (hnW.trans (normalizer_le_normalizer_centralizer W))).trans inf_normalizer_le_normalizer_inf
    have hQC : (P (other i)).pCoreIn 2 ≤ C := by
      rw [←hT]
      exact map_subtype_le _
    have hcore : C.pCoreIn 2 = (P (other i)).pCoreIn 2 := by
      apply le_antisymm (pCoreIn_mono_of_normalizes inf_le_left hnC)
      have hh := inf_pCoreIn_le_of_le 2 (show C ≤ P (other i) from inf_le_left)
      rwa [inf_eq_right.mpr hQC] at hh
    have hTc : (T : Subgroup C) = pCore 2 C := by
      apply map_injective C.subtype_injective
      exact hT.trans hcore.symm
    let : Finite C := Finite.of_injective (inclusion (show C ≤ P (other i) from inf_le_left))
      (inclusion_injective _)
    have hZp : IsPGroup 2 Z := (isPGroup_pCoreIn 2 (P i)).to_le hZQ
    exact le_inf hZQ ((pGroup_le_core_of_core_sylow C Z hZC hZp ⟨T,hTc⟩).trans_eq hcore)
  · exfalso
    apply hnc
    apply le_centralizer_conjugateSpanBy_of_normalizes W ((P i).pCoreIn 2) (P (other i)) hnW
    obtain ⟨T,hT⟩ := hS (other i)
    have hAS : (P i).pCoreIn 2 ≤ B.pCoreIn 2 :=
      pGroup_le_core_of_core_sylow B _ (source_core_le_borel
        (Classical.choice (h.local_data i))) (isPGroup_pCoreIn 2 _) hB
    rw [show W = omegaCenterIn (B.pCoreIn 2) from
      (he T).trans (congrArg omegaCenterIn (sylow_image_eq_edge_core _ B (borel_le h _) hB T hT))]
    exact fun z hz => centralizer_le hAS ((mem_omegaCenterIn_iff _ _).mp hz).2.1

/-- The literal replacement span from printed 6.4 is elementary and lies
in the center omega of the original core intersection in the noncentral case. -/
theorem source_replacement_span_le_inter_omega (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (i : Fin 2)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G))
    (hnc : ¬ sylowCenterSpan (P (other i)) ≤ centralizer
      (conjugateSpanBy ((P i).pCoreIn 2) (P (other i)) : Set G)) :
    conjugateSpanBy (sylowCenterSpan (P i))
      (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))) ≤
        omegaCenterIn ((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) := by
  apply conjugateSpanBy_le
  · intro z hz
    obtain ⟨_,hc,hp⟩ := (mem_omegaCenterIn_iff _ _).mp
      (sylowCenterSpan_le_coreOmega _ (source_core_selfCentralizing
        (Classical.choice (h.local_data i))) hz)
    exact (mem_omegaCenterIn_iff _ _).mpr
      ⟨source_opposite_center_le_inter_of_noncentral h hB hS i hn hnc hz,
        centralizer_le inf_le_left hc,hp⟩
  · exact ((conjugateSpanBy_le_self ((source_core_le_borel
      (Classical.choice (h.local_data i))).trans (borel_le h _))).trans hn).trans
        (normalizer_le_normalizer_omegaCenterIn _)


/-- The source replacement span is the full neighboring orbit span; the
full Borel preserves its original seed. -/
theorem source_replacement_span_eq_full_span (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (i : Fin 2)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) :
    conjugateSpanBy (sylowCenterSpan (P i))
      (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))) =
        conjugateSpanBy (sylowCenterSpan (P i)) (P (other i)) := by
  let := (Classical.choice (h.local_data i)).finite_P
  have hnZ : P i ≤ normalizer (sylowCenterSpan (P i) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (sylowCenterSpan_le _)).mp (sylowCenterSpan_normal _)
  have he := conjugateSpanBy_sup_of_normalizes_seed (sylowCenterSpan (P i))
    (conjugateSpanBy ((P i).pCoreIn 2) (P (other i))) B
    ((borel_le h i).trans hnZ) ((borel_le h (other i)).trans (le_normalizer_conjugateSpanBy _ _))
  rw [core_closure_sup_borel_of_inter_normal h hB i hn] at he
  exact he.symm

/-- The replacement span is generated by its Q_delta-fixed subgroup.
This does not identify Q_delta with a Sylow of X. -/
theorem source_replacement_span_core_fixed_generation (h : LocallyRankOneTriple P B) (i : Fin 2) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    let V := conjugateSpanBy (sylowCenterSpan (P i)) X
    conjugateSpanBy (V ⊓ centralizer ((P i).pCoreIn 2 : Set G)) X = V := by
  dsimp only
  apply le_antisymm (conjugateSpanBy_le inf_le_left (le_normalizer_conjugateSpanBy _ _))
  apply conjugateSpanBy_mono _ le_rfl
  exact le_inf (le_conjugateSpanBy _ _)
    (fun z hz => ((mem_omegaCenterIn_iff _ _).mp
      (sylowCenterSpan_le_coreOmega _ (source_core_selfCentralizing
        (Classical.choice (h.local_data i))) hz)).2.1)

/-- Faithfulness makes X act nontrivially on the literal replacement span,
including in the central neighboring-center branch. -/
theorem source_replacement_span_not_central (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (i : Fin 2)
    (hn : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set G)) :
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    ¬ conjugateSpanBy (sylowCenterSpan (P i)) X ≤ centralizer (X : Set G) := by
  let := (Classical.choice (h.local_data i)).finite_P
  let Z := sylowCenterSpan (P i)
  let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
  change ¬ conjugateSpanBy Z X ≤ centralizer (X : Set G)
  intro hc
  have hnZ : P i ≤ normalizer (Z : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (sylowCenterSpan_le _)).mp (sylowCenterSpan_normal _)
  have hXZ : X ≤ normalizer (Z : Set G) :=
    (le_centralizer_iff.mp ((le_conjugateSpanBy Z X).trans hc)).trans (Subgroup.centralizer_le_normalizer _)
  have hnZ' : P (other i) ≤ normalizer (Z : Set G) := by
    rw [←core_closure_sup_borel_of_inter_normal h hB i hn]
    exact sup_le hXZ ((borel_le h i).trans hnZ)
  have hgen : P i ⊔ P (other i) = ⊤ := by
    fin_cases i
    · exact h.generate
    · exact (sup_comm _ _).trans h.generate
  let : Z.Normal := normalizer_eq_top_iff.mp (top_le_iff.mp (hgen ▸ sup_le hnZ hnZ'))
  have hZB : Z ≤ B := (sylowCenterSpan_le_coreOmega _
    (source_core_selfCentralizing (Classical.choice (h.local_data i)))).trans
      ((map_subtype_le _).trans (source_core_le_borel (Classical.choice (h.local_data i))))
  exact source_centerSpan_ne_bot (Classical.choice (h.local_data i)) (h.faithful Z inferInstance hZB)

end CFSG.Quasithin.ChapterF.Source.DGS85
