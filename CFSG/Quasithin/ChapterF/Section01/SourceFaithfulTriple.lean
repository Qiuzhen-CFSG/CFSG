module
public import CFSG.Quasithin.ChapterF.Section01.SourceStarredParabolic
public import Theory.GroupTheory.AmalgamLocalCores
/-!
# The faithful source triple in its generated group

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed
pp.261–262, Proposition F.1.9. The actual parabolics generate G₀ and
intersect in B. A subgroup of B normal in both parabolics has its
embedded two-core normal in G₀, hence trivial. Self-centralization of
the core in either parabolic then makes that subgroup trivial.

The genuine F.1.1 hypotheses restrict to G₀ without a finite-completion
assumption. Applying the starred-parabolic construction there gives the
finite local data and faithful generating triple. The displayed quotient
maps retain the original local factor under both restriction and the
inclusion into its starred parabolic. Rank-two recognition is separate.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The source overlap has no nontrivial subgroup normal in both parabolics. -/
theorem HypothesisF11.common_normal_eq_bot (h : HypothesisF11 L S)
    (N : Subgroup G) (hNB : N ≤ commonBorel L S)
    (hN : ∀ i, parabolic L S i ≤ normalizer (N : Set G)) : N = ⊥ := by
  let := h.finite_parabolic 0
  apply Theory.GroupTheory.AmalgamLocalCores.common_normal_eq_bot
    (parabolic L S 0) (parabolic L S 1) N
    (le_inf (hNB.trans (commonBorel_le_parabolic 0))
      (hNB.trans (commonBorel_le_parabolic 1))) (hN 0) (hN 1)
  · rw [parabolics_generate]
    exact h.twoCore_free
  · exact (ChapterA.generalizedFitting_eq_pCore_iff 2).mp (h.characteristic_two 0)

/-- F.1.9 when the source generators fill the ambient group. -/
theorem HypothesisF11.locallyRankOneTriple_of_generated_eq_top (h : HypothesisF11 L S)
    (hgen : generated L S = ⊤) : LocallyRankOneTriple (parabolic L S) (commonBorel L S) := by
  refine ⟨(parabolics_generate L S).trans hgen, lemma_F_1_3_6 h, ?_, h.localRankOneData⟩
  intro N hN hNB
  exact h.common_normal_eq_bot N hNB (fun _ => le_normalizer_of_normal)


/-- Each original local factor lies in its source completion. -/
theorem local_le_generated (i : Fin 2) : L i ≤ generated L S := by
  fin_cases i
  · exact le_sup_left.trans le_sup_left
  · exact le_sup_right.trans le_sup_left

private theorem borel_subgroupOf (W A R : Subgroup G) (hA : A ≤ W) :
    borel (A.subgroupOf W) (R.subgroupOf W) = (borel A R).subgroupOf W := by
  unfold borel
  change A.subgroupOf W ⊓ normalizer ((R ⊓ A).subgroupOf W : Set W) = _
  rw [← subgroupOf_normalizer_eq (inf_le_right.trans hA)]
  rfl

private theorem parabolic_subgroupOf (W : Subgroup G)
    (hL : ∀ i, L i ≤ W) (hS : S ≤ W) (i : Fin 2) :
    parabolic (fun j => (L j).subgroupOf W) (S.subgroupOf W) i =
      (parabolic L S i).subgroupOf W := by
  unfold parabolic
  rw [borel_subgroupOf W (L (other i)) S (hL (other i)),
    ← subgroupOf_sup (hL i) hS,
    ← subgroupOf_sup (sup_le (hL i) hS) ((borel_le _ _).trans (hL _))]

/-- All six genuine F.1.1 clauses hold in the literal generated subgroup. -/
theorem HypothesisF11.subgroupOf_generated (h : HypothesisF11 L S) :
    HypothesisF11 (fun i => (L i).subgroupOf (generated L S))
      (S.subgroupOf (generated L S)) := by
  let W := generated L S
  have hL (i : Fin 2) : L i ≤ W := local_le_generated i
  have hS : S ≤ W := le_sup_right
  have hgen : generated (fun i => (L i).subgroupOf W) (S.subgroupOf W) = ⊤ := by
    change (L 0).subgroupOf (generated L S) ⊔ (L 1).subgroupOf (generated L S) ⊔
      S.subgroupOf (generated L S) = ⊤
    rw [← subgroupOf_sup (hL 0) (hL 1),
      ← subgroupOf_sup (sup_le (hL 0) (hL 1)) hS]
    exact subgroupOf_self W
  let e (i : Fin 2) := subgroupOfEquivOfLe (hL i)
  refine ⟨?_, h.S_isP.comap_subtype, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · let := h.finite_S
    exact Finite.of_injective (subgroupOfEquivOfLe hS) (subgroupOfEquivOfLe hS).injective
  · intro i
    rw [← subgroupOf_normalizer_eq (hL i)]
    exact comap_mono (h.S_normalizes i)
  · intro i
    let := h.finite_local i
    obtain ⟨T, hT⟩ := h.sylow i
    let U : Sylow 2 ((L i).subgroupOf W) :=
      T.mapSurjective (f := (e i).symm.toMonoidHom) (e i).symm.surjective
    refine ⟨U, ?_⟩
    apply map_injective W.subtype_injective
    rw [map_map, Subgroup.map_inf _ _ _ W.subtype_injective,
      map_subgroupOf_eq_of_le hS, map_subgroupOf_eq_of_le (hL i)]
    change ((T : Subgroup (L i)).map (e i).symm.toMonoidHom).map
      (W.subtype.comp ((L i).subgroupOf W).subtype) = _
    rw [map_map]
    change (T : Subgroup (L i)).map (L i).subtype = _
    exact hT
  · intro i
    exact (h.quotient i).of_equiv
      (QuotientGroup.congr _ _ (e i) (pCore_map_iso 2 (e i)))
  · intro i
    rw [borel_subgroupOf W (L (other i)) S (hL _),
      ← subgroupOf_normalizer_eq (hL i)]
    exact comap_mono (h.cross i)
  · rw [hgen]
    have hmap := pCore_map_iso 2 (topEquiv : (⊤ : Subgroup W) ≃* W)
    rw [h.twoCore_free] at hmap
    exact (map_eq_bot_iff_of_injective _ topEquiv.injective).mp hmap
  · intro i
    let := h.finite_parabolic i
    have hP : parabolic L S i ≤ W := by
      change parabolic L S i ≤ generated L S
      rw [← parabolics_generate L S]
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    rw [parabolic_subgroupOf W hL hS]
    let : Finite ((parabolic L S i).subgroupOf W) :=
      Finite.of_injective (subgroupOfEquivOfLe hP) (subgroupOfEquivOfLe hP).injective
    apply (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hP)).mpr
      ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp (h.characteristic_two i))

private theorem commonBorel_subgroupOf (W : Subgroup G)
    (hL : ∀ i, L i ≤ W) (hS : S ≤ W) :
    commonBorel (fun i => (L i).subgroupOf W) (S.subgroupOf W) =
      (commonBorel L S).subgroupOf W := by
  unfold commonBorel
  rw [borel_subgroupOf W (L 0) S (hL 0),
    borel_subgroupOf W (L 1) S (hL 1),
    ← subgroupOf_sup ((borel_le _ _).trans (hL 0)) ((borel_le _ _).trans (hL 1)),
    ← subgroupOf_sup (sup_le ((borel_le _ _).trans (hL 0))
      ((borel_le _ _).trans (hL 1))) hS]

/-- F.1.9: the actual finite parabolics form a faithful triple in G₀. -/
theorem HypothesisF11.generatedLocallyRankOneTriple (h : HypothesisF11 L S) :
    LocallyRankOneTriple
      (fun i => (parabolic L S i).subgroupOf (generated L S))
      ((commonBorel L S).subgroupOf (generated L S)) := by
  have hL (i : Fin 2) : L i ≤ generated L S := local_le_generated i
  have hS : S ≤ generated L S := le_sup_right
  have hg : generated (fun i => (L i).subgroupOf (generated L S))
      (S.subgroupOf (generated L S)) = ⊤ := by
    change (L 0).subgroupOf (generated L S) ⊔ (L 1).subgroupOf (generated L S) ⊔
      S.subgroupOf (generated L S) = ⊤
    rw [← subgroupOf_sup (hL 0) (hL 1),
      ← subgroupOf_sup (sup_le (hL 0) (hL 1)) hS]
    exact subgroupOf_self (generated L S)
  have ht := h.subgroupOf_generated.locallyRankOneTriple_of_generated_eq_top hg
  have hp : parabolic (fun i => (L i).subgroupOf (generated L S))
      (S.subgroupOf (generated L S)) =
      fun i => (parabolic L S i).subgroupOf (generated L S) := by
    funext i
    exact parabolic_subgroupOf (generated L S) hL hS i
  rw [hp, commonBorel_subgroupOf (generated L S) hL hS] at ht
  exact ht

/-- The original local quotient survives restriction to the actual source group. -/
noncomputable def generatedLocalQuotientEquiv (L : Fin 2 → Subgroup G)
    (S : Subgroup G) (i : Fin 2) :
    (L i ⧸ pCore 2 (L i)) ≃*
      ((L i).subgroupOf (generated L S) ⧸
        pCore 2 ((L i).subgroupOf (generated L S))) :=
  let e := (subgroupOfEquivOfLe (local_le_generated (L := L) (S := S) i)).symm
  QuotientGroup.congr _ _ e (pCore_map_iso 2 e)

@[simp] theorem generatedLocalQuotientEquiv_mk
    (i : Fin 2) (x : L i) :
    generatedLocalQuotientEquiv L S i (QuotientGroup.mk x) =
      QuotientGroup.mk ((subgroupOfEquivOfLe
        (local_le_generated (L := L) (S := S) i)).symm x) := rfl

/-- Both actual source transports, before any rank-two classification. -/
noncomputable def HypothesisF11.generatedStarredQuotientEquiv
    (h : HypothesisF11 L S) (i : Fin 2) :
    (L i ⧸ pCore 2 (L i)) ≃*
      (starredParabolic (fun j => (L j).subgroupOf (generated L S))
        (S.subgroupOf (generated L S)) i ⧸
      pCore 2 (starredParabolic (fun j => (L j).subgroupOf (generated L S))
        (S.subgroupOf (generated L S)) i)) :=
  (generatedLocalQuotientEquiv L S i).trans
    (h.subgroupOf_generated.starredQuotientEquiv i)

end CFSG.Quasithin.ChapterF.Source
