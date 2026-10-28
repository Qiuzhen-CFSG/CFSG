module

public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalUniqueness
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Source523
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.Hypothesis1311
public import CFSG.Quasithin.ClassificationModels
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The earlier rank-one theorem on the original outside A₅ subgroup

The original Context supplies every hypothesis of 5.2.3 independent of H.
If H moves Ω₁Z(T), its two-residual also moves that subgroup, since the
original Sylow T centralizes it and supplements the residual in H. Thus
the centralizing local alternative of 5.2.3 is impossible. The original
ambient exclusions eliminate M₂₃ and all larger-field global alternatives.

This leaves precisely a field-two rank-two model when n(H)>1. It does not
prove 13.2.8(1): the genuine 5.2.3 theorem, the lower bound on n(H), and
the exclusion of these small global models remain separate source inputs.
In particular the unmarked global alternative of the current 5.2.3 interface
does not connect its field parameter to the original A₅ quotient.

Source: Aschbacher--Smith 13.2.8(1), printed p.880, and 5.2.3, p.649.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
open Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original outside residual moves the omega center whenever H does. -/
theorem residual_moves_omegaCenter (T : Sylow 2 G) {H : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H)
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    ¬ (pResidual 2 H).map H.subtype ≤
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  intro hc
  apply hZ
  have hgen := congrArg (map H.subtype)
    (pResidual_sup_sylow_eq_top (T.subtype hTH))
  rw [Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH,
    ← MonoidHom.range_eq_map, range_subtype] at hgen
  rw [← hgen]
  refine sup_le hc ?_
  intro t ht z hz
  exact (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht).symm

/-- No centralizing local output of 5.2.3 can occur for this outside H. -/
theorem not_source523_local_of_omega_movement (T : Sylow 2 G)
    {L H V : Subgroup G} {n : ℕ} (hTH : (T : Subgroup G) ≤ H)
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    ¬ Source523.LocalAlternative T L H V n := by
  rintro ⟨_, _, K, _, hK, _⟩
  exact residual_moves_omegaCenter T hTH hZ (hK.trans (map_subtype_le K))

/-- The unchanged A₅ Context supplies the original rank-one source setup. -/
theorem source523_setup_of_context
    {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃) :
    Source523.Setup KnownSimple.IsKnownSimple T L (normalizer (L : Set G)) V 2 := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    d.hypothesis.qtke T d.maximal_local
  have horbit : componentOrbit L (T : Subgroup G) = L := by
    apply le_antisymm _ (le_componentOrbit L _)
    apply iSup_le
    intro t
    exact (mem_normalizer_iff_map_conj_eq.mp (d.normalizes_L t.property)).le
  have hmax : IsMaximalTwoLocal (normalizer (L : Set G)) := by
    simpa only [horbit] using hu.normalizer_maximal
  refine ⟨d.hypothesis.qtke, d.maximal_local,
    ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
      d.hypothesis.local_component).2, ?_, L.le_normalizer,
    normal_subgroupOf_of_le_normalizer le_rfl, ⟨hmax, d.normalizes_L⟩,
    d.chosen.le_sylow.trans le_sup_right, d.reduced, ?_⟩
  · obtain ⟨e⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (show Nat.card (GaloisField 2 2) = 4 from GaloisField.card 2 2 (by decide))
    exact ⟨GaloisField 2 2, inferInstance, inferInstance,
      GaloisField.card 2 2 (by decide), ⟨d.quotient.trans e.symm⟩⟩
  · intro hzero
    exact d.chosen.ne_bot (d.chosen.eq_commutator.trans hzero)

/-- The actual moving outside subgroup forces a global 5.2.3 alternative. -/
theorem source523_global_of_omega_movement
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hn : 1 < ChapterE.generationParameter H) : Source523.GlobalAlternative G :=
  (h523 G T L (normalizer (L : Set G)) V 2 (source523_setup_of_context d) H hH hn).resolve_left
    (not_source523_local_of_omega_movement T hH.1.1.2 hZ)

/-- Original ambient exclusions reduce that global alternative to field two. -/
theorem fieldTwo_rankTwo_of_source523
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hn : 1 < ChapterE.generationParameter H) : ClassificationModels.IsRankTwoModel G 1 := by
  have h := d.hypothesis.hypothesis1311
  rcases source523_global_of_omega_movement d h523 hH hZ hn with hm | ⟨f, hf⟩
  · exact (h.no_M23 hm).elim
  · have hle : f ≤ 1 := by
      by_contra! hgt
      exact h.no_rankTwo f hgt hf
    have hpos : 1 ≤ f := by
      cases hf <;> omega
    have he : f = 1 := by omega
    exact he ▸ hf

/-- For the final classification, the surviving global models are already
successful outputs, so no local exclusion of the field-two models is needed. -/
theorem main_model_of_source523_omega_movement
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hn : 1 < ChapterE.generationParameter H) : ClassificationModels.IsQTKEModel G :=
  .rank_two 1 (fieldTwo_rankTwo_of_source523 d h523 hH hZ hn)

end CFSG.Quasithin.Chapter13.Section02.A5Outside
