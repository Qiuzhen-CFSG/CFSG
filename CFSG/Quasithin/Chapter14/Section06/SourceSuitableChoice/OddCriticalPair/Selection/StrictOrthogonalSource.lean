module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Selection.FullOrthogonalSource
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Selection.PreservingGeometry
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Alternatives.Quadratic
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Selection.StrictDisplacement

/-!
# The preserving strict endpoint and its remaining source alternatives

The selected endpoint has a quadratic actor. If that actor preserves the
two exchanged summands and the moved section has dimension four, the literal
endpoint geometry constructs the marked orthogonal critical pair and the
suitable terminal witness. The original exchanger preserves the chosen
H, M and Mc and keeps reverse containment for the same left conjugator.

The remaining alternatives are retained explicitly: a preserving actor in
dimension eight, with actor and denominator ranks at most two and every
displacement rank at most three; or a cyclic swapping actor in dimension
four. Neither alternative is discarded by definition. Their ambient
exclusion and rank-eight point placement remain with
qt-e-suitable-orthogonal-marking. The earlier exchanged-factor, fitting and
normalizer inputs are ultimately discharged by qt-e-suitable-existence.

Source: Aschbacher--Smith 14.6.13, printed pp.1031--1032, and the suitable
construction of 14.6.17, printed pp.1035--1036.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
open OddNormalizer OrthogonalSource SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter13.Section08 Chapter13.Section08.CriticalGeometry
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
include hG hempty hM hunique hmany hcard e hab hH

/-- The preserving, rank-four case of the strict selected endpoint gives
the marked orthogonal pair with the literal original first factor. -/
theorem source_rankTwo_orthogonal_of_preserving_selected
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
    let : IsElementaryAbelian 2 D.UH :=
      ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    ∀ c : SelectedQuadraticEndpoint h a, c.endpoint.representative ∉ Mc →
      actorImage H (c.endpoint.conjugate D.UH) ≤ actorImage H H0 →
      Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⊤) = 4 →
      p = 3 ∧ ∃ o : SourceOrthogonalFourAction H D.UH D.V₁ (H.pCoreIn 2),
        ∃ critical : SourceOrthogonalCriticalPair o Mc,
          o.plane critical.first = firstSupport a H1 := by
  dsimp only
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  intro c hout hkeep hdim
  have hHMc : H ≤ Mc := by
    have hHZ := (Section02.source_lemma_14_2_3 hG T hempty hM hunique hmany hcard e H hH.1 hH.2).1
    have hm : Mc ∈ maximalTwoLocalOvergroups H := hHZ ▸ Set.mem_singleton _
    exact hm.2
  have hf (g : H ⧸ pCore 2 H)
      (hfix : ∀ v ∈ subspaceCommutator a.representation ⊤ ⊤, a.representation g v = v) : g = 1 := by
    apply source_rankTwo_residual_moved_faithful hG T hempty hM hunique hmany hcard e hab H hH a g
    rw [← source_rankTwo_whole_moved_eq_residual hG T hempty hM hunique hmany hcard e hab H hH a]
    exact hfix
  obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hunique hmany hcard e hab H hH
  obtain ⟨geo⟩ := four_geometry_of_preserving_endpoint a h.H_centralizes
    (T : Subgroup G) hH.1.2 p H0 H1 H2 d Mc hHMc c.endpoint.representative hout
    (c.endpoint.large_le hb) (c.endpoint.reverse_le hb) hkeep c.quadratic.1.1 hdim hf
  obtain ⟨hp,o,i,hi⟩ := source_rankFour_orthogonal_action hG T hempty hM hunique hmany hcard e hab
    H hH a p H0 H1 H2 d geo.dimension
  refine ⟨hp,o,⟨i,geo.g,geo.outside,?_,geo.reverse,?_⟩,hi⟩
  · change _ ≤ H ⊓ normalizer (o.plane i : Set G)
    rw [hi]
    exact geo.normalizes
  · change ¬ ⁅o.plane i,_⁆ ≤ centralInvolutions T
    rw [hi]
    exact geo.noncentral

/-- Discharge both full-denominator endpoints and preserving rank-four
strict endpoints. The remaining source obligations retain the selected endpoint:
a preserving rank-eight actor, or a cyclic swapping actor in dimension four.
This is a reduction of 14.6.13, not the completed source alternatives. -/
theorem source_rankTwo_marked_or_quadratic_obstruction
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
    let : IsElementaryAbelian 2 D.UH :=
      ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    (p = 3 ∧ ∃ o : SourceOrthogonalFourAction H D.UH D.V₁ (H.pCoreIn 2),
      ∃ critical : SourceOrthogonalCriticalPair o Mc,
        o.plane critical.first = firstSupport a H1) ∨
    (∃ c : SelectedQuadraticEndpoint h a, c.endpoint.representative ∉ Mc ∧
      let B := actorImage H (c.endpoint.conjugate D.UH)
      (Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⊤) = 8 ∧
        B ≤ actorImage H H0 ∧ rank B ≤ 2 ∧
        Nat.log 2 ((commutatorPreimage D.UH (c.endpoint.conjugate D.UH)
          (c.endpoint.conjugate D.V₁)).relIndex D.UH) ≤ 2 ∧
        ∀ t ∈ B, Module.finrank (ZMod 2)
          (LinearMap.range (a.representation t - LinearMap.id)) ≤ 3) ∨
      (p = 3 ∧ Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⊤) = 4 ∧
        ∃ t ∈ B, B = zpowers t ∧ Nat.card B = 2 ∧ rank B = 1 ∧
          (subspaceCommutator a.representation ⊤ (actorImage H H1)).map (a.representation t) =
            subspaceCommutator a.representation ⊤ (actorImage H H2) ∧
          (subspaceCommutator a.representation ⊤ (actorImage H H2)).map (a.representation t) =
            subspaceCommutator a.representation ⊤ (actorImage H H1))) := by
  dsimp only
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
  rcases source_rankTwo_marked_or_strict hG T hempty hM hunique hmany hcard e hab H hH a
    p H0 H1 H2 d with hmarked | ⟨c,hout⟩
  · exact Or.inl hmarked
  · have hf (g : H ⧸ pCore 2 H)
        (hfix : ∀ v ∈ subspaceCommutator a.representation ⊤ ⊤, a.representation g v = v) : g = 1 := by
      apply source_rankTwo_residual_moved_faithful hG T hempty hM hunique hmany hcard e hab H hH a g
      rw [← source_rankTwo_whole_moved_eq_residual hG T hempty hM hunique hmany hcard e hab H hH a]
      exact hfix
    rcases exchanged_quadratic_preserves_or_swaps a (T : Subgroup G) hH.1.2
        p H0 H1 H2 d hf _ c.quadratic with hkeep | hswap
    · rcases exchanged_moved_dimension a (T : Subgroup G) hH.1.2 p H0 H1 H2 d with ⟨_,hdim⟩ | hdim
      · exact Or.inl (source_rankTwo_orthogonal_of_preserving_selected
          hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 d c hout hkeep hdim)
      · let := c.quadratic.1.2
        have hr := exchanged_preserving_actor_rank a (T : Subgroup G) p H0 H1 H2 d _ hkeep
        obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds
          hG T hempty hM hunique hmany hcard e hab H hH
        refine Or.inr ⟨c,hout,Or.inl ⟨hdim,hkeep,hr,c.comparison.trans hr,?_⟩⟩
        intro t ht
        have htbound := c.displacement_rank_le hb ht
        have hd := c.comparison.trans hr
        exact htbound.trans (Nat.add_le_add_right hd 1)
    · exact Or.inr ⟨c,hout,Or.inr hswap⟩

/-- The preserving strict rank-four endpoint supplies the actual suitable
terminal witness. Only the permitted earlier-source fitting and normalizer
inputs remain, along with the stated branch conditions. -/
theorem source_terminal_witness_of_preserving_selected
    (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (hF : residual H ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc)
    (hN : Mc ⊓ normalizer
      (((T : Subgroup G) ⊓ normalizer (H1 : Set G) : Subgroup G) : Set G) = (T : Subgroup G)) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
    let : IsElementaryAbelian 2 D.UH :=
      ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    ∀ c : SelectedQuadraticEndpoint h a, c.endpoint.representative ∉ Mc →
      actorImage H (c.endpoint.conjugate D.UH) ≤ actorImage H H0 →
      Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⊤) = 4 →
      SourceTerminalWitness hG T hempty hM hunique hmany hcard e hab := by
  dsimp only
  intro c hout hkeep hdim
  obtain ⟨_,o,critical,hi⟩ := source_rankTwo_orthogonal_of_preserving_selected
    hG T hempty hM hunique hmany hcard e hab H hH a 3 H0 H1 H2 d c hout hkeep hdim
  exact source_terminal_witness_of_marked_orthogonal_pair hG T hempty hM hunique hmany hcard e hab
    H hH o critical a H0 H1 H2 d hi hF hN

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
