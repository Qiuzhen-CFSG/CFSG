module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairSemilinear

/-!
# Core control for the original alternating-five pair

The conclusion needed from the recognition argument in F.1.12 is equality
of the two embedded cores of Li and Li S. It does not require a complement
to Li. Here this conclusion is connected to the literal conjugation action
on Li/O2(Li): the kernel lies in Li exactly when the two cores agree.

Core equality first gives containment at the normalized Borel. F.1.3 then
makes the common Borel normalize S, so the second containment follows.
`A5PairCoreRecognition` retains all the original recognition hypotheses;
it is an explicit unproved source obligation, not a recognition theorem.
The existing marked semilinear condition implies this weaker obligation.

Source: Aschbacher--Smith, F.1.1 and F.1.12, printed pp.259 and 262--264.
The core equality occurs on printed p.264 after the DGS85 Theorem A
reduction and analysis of the marked rank-two Lie extensions.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source

variable {G : Type*} [Group G] [Finite G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}

omit [Finite G] in
/-- Controlling the actual quotient-action kernel suffices without a splitting. -/
theorem HypothesisF11.join_core_eq_of_action_kernel_le
    (h : HypothesisF11 L S) (i : Fin 2)
    (hk : (pCoreJoinAction 2 (h.S_normalizes i)).ker ≤
      (L i).subgroupOf (L i ⊔ S)) :
    twoCore (L i ⊔ S) = twoCore (L i) := by
  have hle : twoCore (L i ⊔ S) ≤ L i := by
    rintro x ⟨y, hy, rfl⟩
    exact hk (pCore_le_pCoreJoinAction_kernel 2 (h.S_normalizes i) hy)
  apply le_antisymm
  · exact le_pCoreIn_of_normalizes (pCore_isPGroup.map (L i ⊔ S).subtype) hle
      ((le_sup_left.trans (L i ⊔ S).le_normalizer).trans
        (normalizer_le_normalizer_characteristic_image (L i ⊔ S)
          (pCore 2 (L i ⊔ S : Subgroup G))))
  · exact le_pCoreIn_of_normalizes (pCore_isPGroup.map (L i).subtype)
      ((map_subtype_le _).trans le_sup_left)
      ((sup_le (L i).le_normalizer (h.S_normalizes i)).trans
        (normalizer_le_normalizer_characteristic_image (L i) (pCore 2 (L i))))

omit [Finite G] in
/-- In the A5 case, kernel control is exactly the required core equality.
The relative subgroup here is the original Li inside its literal join with S. -/
theorem HypothesisF11.a5_join_core_eq_iff_action_kernel_le
    (h : HypothesisF11 L S) (i : Fin 2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)) :
    twoCore (L i ⊔ S) = twoCore (L i) ↔
      (pCoreJoinAction 2 (h.S_normalizes i)).ker ≤
        (L i).subgroupOf (L i ⊔ S) := by
  constructor
  · intro heq
    have hc : center (L i ⧸ pCore 2 (L i)) = ⊥ := by
      apply bot_unique
      intro x hx
      have he : e x ∈ center (alternatingGroup (Fin 5)) :=
        (centerCongr e ⟨x, hx⟩).property
      rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at he
      exact mem_bot.mpr (e.injective (he.trans (map_one e).symm))
    rw [pCoreJoinAction_kernel 2 (h.S_normalizes i) h.S_isP hc]
    intro x hx
    have hx' : (x : G) ∈ twoCore (L i ⊔ S) := mem_map_of_mem _ hx
    rw [heq] at hx'
    change (x : G) ∈ L i
    exact map_subtype_le (pCore 2 (L i)) hx'
  · exact h.join_core_eq_of_action_kernel_le i

/-- Failure of containment supplies an actual kernel element outside Li.
This locates the obstruction in the literal quotient action, rather than
in a proposed choice of semidirect complement. -/
theorem HypothesisF11.a5_local_action_kernel_escape_of_not_contained
    (h : HypothesisF11 L S) (i : Fin 2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5))
    (hn : borel (L i) S ≤ normalizer (S : Set G))
    (hout : ¬ S ≤ L i) :
    ∃ x : (L i ⊔ S : Subgroup G),
      pCoreJoinAction 2 (h.S_normalizes i) x = 1 ∧ (x : G) ∉ L i := by
  have hk : ¬ (pCoreJoinAction 2 (h.S_normalizes i)).ker ≤
      (L i).subgroupOf (L i ⊔ S) := by
    intro hk
    exact hout ((h.a5_local_containment_iff_core_eq i e hn).mpr
      (h.join_core_eq_of_action_kernel_le i hk))
  exact SetLike.not_le_iff_exists.mp hk

/-- Core equality at the two original indices gives the p.264 containment,
starting with only one normalized Borel. -/
theorem HypothesisF11.a5_pair_containment_of_core_eq
    (h : HypothesisF11 L S)
    (he : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    (hn : ∃ j, borel (L j) S ≤ normalizer (S : Set G))
    (hc : ∀ i, twoCore (L i ⊔ S) = twoCore (L i)) :
    ∀ i, S ≤ L i := by
  obtain ⟨j, hj⟩ := hn
  obtain ⟨ej⟩ := he j
  have hSj := (h.a5_local_containment_iff_core_eq j ej hj).mpr (hc j)
  have hB : commonBorel L S ≤ normalizer (S : Set G) := by
    simpa only [inf_eq_left.mpr hSj] using h.commonBorel_normalizes_localSylow j
  intro i
  obtain ⟨ei⟩ := he i
  exact (h.a5_local_containment_iff_core_eq i ei ((borel_le_commonBorel i).trans hB)).mpr
    (hc i)

/-- The source core-control obligation. No complement or ambient Sylow
hypothesis is added; proving this proposition remains the recognition step. -/
@[expose] def A5PairCoreRecognition (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (L : Fin 2 → Subgroup G) (S : Subgroup G),
    HypothesisF11 L S → IsQuasithin (generated L S) →
    (∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5))) →
    (∃ j, borel (L j) S ≤ normalizer (S : Set G)) →
    ∀ i, twoCore (L i ⊔ S) = twoCore (L i)

/-- Compatibility with the earlier, stronger marked semilinear route. -/
theorem A5PairSemilinearRecognition.core_recognition
    (recognition : A5PairSemilinearRecognition G) : A5PairCoreRecognition G := by
  intro L S h hqt he hn i
  obtain ⟨m⟩ := recognition L S h hqt he hn i
  exact h.a5_join_core_eq_of_semilinear_model i m

/-- Conditional containment from exactly the core-control source obligation. -/
theorem a5_pair_containment_of_core_recognition
    (recognition : A5PairCoreRecognition G)
    (h : HypothesisF11 L S) (hqt : IsQuasithin (generated L S))
    (he : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    (hn : ∃ j, borel (L j) S ≤ normalizer (S : Set G)) : ∀ i, S ≤ L i :=
  h.a5_pair_containment_of_core_eq he hn (recognition L S h hqt he hn)

end CFSG.Quasithin.ChapterF.Source
