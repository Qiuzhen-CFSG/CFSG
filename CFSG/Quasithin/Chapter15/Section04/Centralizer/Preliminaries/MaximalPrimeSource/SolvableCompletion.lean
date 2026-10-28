module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.BlockControl
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.SolvableCompletion.OutsideBlock

/-!
# The maximal-prime source family from solvable pushing up

The actual solvable maximal two-local supplies the outside block through the
proved solvable C.1.29 theorem in its literal Fitting-preimage join. This
replaces the C.2.6 parameter in 15.4.3(1--3). Every other original source
hypothesis and the iterated-core maps are retained. The genuine earlier
15.4.2 implication remains with its existing source producer.

Source: Aschbacher--Smith, printed pp.1155--1157.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.SolvableCompletion
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Every maximal two-local over XT equals the selected overgroup of N_G(X).
Solvable pushing up is applied only after constructing its literal local setup. -/
theorem source_maximal_overgroup_eq (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G))
    {X : Subgroup G} (hX : X ∈ Xi (T : Subgroup G))
    (hp : 3 < (pCore 2 X).index)
    (hmax : ∀ Y ∈ Xi (T : Subgroup G), (pCore 2 Y).index ≤ (pCore 2 X).index)
    {M H : Subgroup G} (hM : IsMaximalTwoLocal M) (hH : IsMaximalTwoLocal H)
    (hXM : X ⊔ (T : Subgroup G) ≤ M) (hXH : X ⊔ (T : Subgroup G) ≤ H)
    (hNH : normalizer (X : Set G) ≤ H) : M = H := by
  let p := (pCore 2 X).index
  let : Fact p.Prime := ⟨hX.2.2.2.1⟩
  have hTM := le_sup_right.trans hXM
  have hTH := le_sup_right.trans hXH
  have hXF := (source_iterated_core_containment T h h42 hX hp hmax hM hXM).1.trans
    (twoPrimePreimage_le_twoFittingPreimage p M)
  have hYM := (normalizerResidual_bounds T hX hXF hNH).2
  have hcoreT : M.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM] using
      pCoreIn_le_sylow M (T.subtype hTM)
  have hAI : normalizerResidual M X ⊔ M.pCoreIn 2 ≤ M ⊓ H :=
    sup_le hYM (le_inf (pCoreIn_le 2 M) (hcoreT.trans hTH))
  have ha := normalizerResidual_intersectionAlternative T hX hXM ((h42 T h).solvable M hM hTM) hXF
  by_cases hk : twoFittingPreimage H ≤ M ⊓ H
  · apply ChapterA.Section04.lemma_A_4_4_3 M H
      (normalizerResidual M X ⊔ M.pCoreIn 2) le_sup_right hAI ha hM hH
    rw [← twoFittingPreimage_eq_generalized H ((h42 T h).solvable H hH hTH)]
    exact hk.trans inf_le_left
  · have hsetup := source_pushingUp_setup T h h42 hX hp hmax hM hH hXM hXH hNH
    obtain ⟨L, hLK, hout, hb, halt⟩ := outside_block_of_solvable_pushingUp hsetup
      ((h42 T h).solvable H hH hTH) (h.simpleQTKE.evenCharacteristic T H hH hTH) hk
    obtain ⟨_, _, hYI, hYp, _, hYN, hYs⟩ := source_centralResidual T h h42 hX hp hmax hM hXM hNH
    have hLH : L ≤ H := hLK.trans (map_subtype_le _)
    have hLM := alternatingThree_block_le T hX.2.2.2.1 hX.2.2.2.2 hp hTM hTH
      (hYI.trans inf_le_right) hYp hYs hYN.symm.le hYN
      (h.simpleQTKE.twoLocal_sqtk hH.1) hLH hb halt
    exact (hout (le_inf hLM hLH)).elim

/-- Source 15.4.3(1): existence and uniqueness concern maximal two-locals. -/
theorem source_unique_maximal_twoLocal (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G))
    {X : Subgroup G} (hX : X ∈ Xi (T : Subgroup G))
    (hp : 3 < (pCore 2 X).index)
    (hmax : ∀ Y ∈ Xi (T : Subgroup G), (pCore 2 Y).index ≤ (pCore 2 X).index) :
    ∃! M : Subgroup G, IsMaximalTwoLocal M ∧ X ⊔ (T : Subgroup G) ≤ M := by
  obtain ⟨H, hH, hNH, hXH⟩ := exists_maximal_normalizer_overgroup h.simpleQTKE T hX
  exact ⟨H, ⟨hH, hXH⟩, fun M hm => source_maximal_overgroup_eq
    T h h42 hX hp hmax hm.1 hH hm.2 hXH hNH⟩

/-- The selected original lowercase ξ member belongs to ξ*. -/
theorem source_xiStar (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G))
    {X : Subgroup G} (hX : X ∈ Xi (T : Subgroup G))
    (hp : 3 < (pCore 2 X).index)
    (hmax : ∀ Y ∈ Xi (T : Subgroup G), (pCore 2 Y).index ≤ (pCore 2 X).index) :
    X ∈ XiStar (T : Subgroup G) :=
  ⟨hX, source_unique_maximal_twoLocal T h h42 hX hp hmax⟩

/-- Source 15.4.3(3), using the actual two distinct maximal two-local
overgroups of C_G(Z) from Hypothesis 15.4.1. -/
theorem source_noncentral (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G))
    {X : Subgroup G} (hX : X ∈ Xi (T : Subgroup G))
    (hp : 3 < (pCore 2 X).index)
    (hmax : ∀ Y ∈ Xi (T : Subgroup G), (pCore 2 Y).index ≤ (pCore 2 X).index) :
    ¬ X ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  obtain ⟨M₁, M₂, h₁, h₂, hc₁, hc₂, hne⟩ := h.centralizer_overgroups
  have hT : (T : Subgroup G) ≤
      centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
    apply le_centralizer_iff.mp
    intro z hz
    exact mem_centralizer_iff.mpr
      ((Stellmacher.mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp hz).2.2
  exact XiStar.not_le_centralizer (source_xiStar T h h42 hX hp hmax) hT h₁ h₂ hc₁ hc₂ hne

/-- One coherent conditional family containing all of 15.4.3(1–3), with
no additional local classifier, core-containment or uniqueness premise. -/
theorem source_lemma_15_4_3_one_to_three (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G))
    {X : Subgroup G} (hX : X ∈ Xi (T : Subgroup G))
    (hp : 3 < (pCore 2 X).index)
    (hmax : ∀ Y ∈ Xi (T : Subgroup G), (pCore 2 Y).index ≤ (pCore 2 X).index) :
    X ∈ XiStar (T : Subgroup G) ∧
    (∀ M : Subgroup G, IsMaximalTwoLocal M → X ⊔ (T : Subgroup G) ≤ M →
      X ≤ twoPrimePreimage (pCore 2 X).index M ∧ X.pCoreIn 2 ≤ M.pCoreIn 2) ∧
    (¬ X ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)) ∧
    ⁅Stellmacher.omegaOneCenterAmbient (T : Subgroup G), X⁆ ≠ ⊥ := by
  have hnc := source_noncentral T h h42 hX hp hmax
  refine ⟨source_xiStar T h h42 hX hp hmax,
    fun M hM hXM => source_iterated_core_containment T h h42 hX hp hmax hM hXM, hnc, ?_⟩
  intro he
  exact hnc (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he))
end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.SolvableCompletion
