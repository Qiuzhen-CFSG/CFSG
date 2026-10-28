module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Selection.FactorAlignment
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Selection.SwappingSource

/-!
# Original 14.6.13: both marked critical-pair alternatives

The full-denominator endpoint gives a transvection and hence the orthogonal
four-space. For a strict quadratic endpoint, the abelian Mc-span excludes
interchange of the two summands. A preserving actor gives either the same
four-space or rank eight. In rank eight, the displacement bound confines the
actor to one dihedral factor; rank-one reversal supplies the reverse point.
Independent left and right translations align both ends with H1 while
retaining one normalized endpoint and its strict literal denominator.

The first theorem provides the endpoint contract before recognition. The
final theorem also constructs the full orthogonal action, its exact kernels,
and the original first-factor marking. Only the earlier 14.6.12 exchanged
factors remain explicit, with final discharge by qt-e-suitable-existence.
No 14.6.14--16 conclusion enters these alternatives. Their later rank-eight
exclusion and suitable-element consumer are in Selection.SwappingTerminal.

Source: Aschbacher--Smith 14.6.13, printed pp.1031--1032.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
open OddNormalizer OrthogonalSource SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter13.Section08 Chapter13.Section08.SourceCompletion Chapter13.Section08.CriticalGeometry
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Selection
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

/-- The selected rank-eight branch with both point containments marked
by the original first factor and one normalized critical endpoint. -/
theorem source_rankEight_selected_placement
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
    let : IsElementaryAbelian 2 D.UH :=
      ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    ∀ _c : SelectedQuadraticEndpoint h a,
      Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⊤) = 8 →
      Nonempty (RankEightCriticalPlacement h a Mc H1) := by
  dsimp only
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  intro c hdim
  obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hunique hmany hcard e hab H hH
  have hp := source_rankEight_selected_point hG T hempty hM hunique hmany hcard e hab
    H hH a p H0 H1 H2 d c hdim
  have hr := source_rankEight_reverse_point_either hG T hempty hM hunique hmany hcard e hab
    H hH a p H0 H1 H2 d c hdim
  obtain ⟨j,hs,ha,hp,hr⟩ := align_critical_first_support h a p H0 H1 H2 d c.endpoint hb c.strict hp hr
  exact ⟨⟨hdim,j,source_rankTwo_critical_not_mem_Mc hG T hempty hM hunique hmany hcard e hab H hH j,
    hs,ha,hp,hr⟩⟩

/-- Original 14.6.13 endpoint selection, before action recognition and before
any use of 14.6.14--16. Both alternatives retain their literal geometric clauses. -/
theorem source_critical_geometry_alternatives
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
    let : IsElementaryAbelian 2 D.UH :=
      ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    (p = 3 ∧ Nonempty (FourCriticalGeometry a Mc H1)) ∨
      ((p = 3 ∨ p = 5) ∧ Nonempty (RankEightCriticalPlacement h a Mc H1)) := by
  dsimp only
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  have hHMc : H ≤ Mc := by
    have hHZ := (Section02.source_lemma_14_2_3 hG T hempty hM hunique hmany hcard e H hH.1 hH.2).1
    have hm : Mc ∈ maximalTwoLocalOvergroups H := hHZ ▸ Set.mem_singleton _
    exact hm.2
  have hf (g : H ⧸ pCore 2 H)
      (hfix : ∀ v ∈ subspaceCommutator a.representation ⊤ ⊤, a.representation g v = v) : g = 1 := by
    apply source_rankTwo_residual_moved_faithful hG T hempty hM hunique hmany hcard e hab H hH a g
    rw [← source_rankTwo_whole_moved_eq_residual hG T hempty hM hunique hmany hcard e hab H hH a]
    exact hfix
  rcases source_rankTwo_endpoint_selection hG T hempty hM hunique hmany hcard e hab H hH a with
      ⟨l,hout⟩ | ⟨c,hout⟩
  · exact Or.inl (returned_line_four_geometry a h.H_centralizes h.point_card
      (T : Subgroup G) hH.1.2 p H0 H1 H2 d Mc hHMc l hout hf)
  · rcases exchanged_moved_dimension a (T : Subgroup G) hH.1.2 p H0 H1 H2 d with ⟨hp,hdim⟩ | hdim
    · have hkeep := source_selected_actor_preserves hG T hempty hM hunique hmany hcard e hab
        H hH a p H0 H1 H2 d c hout
      obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hunique hmany hcard e hab H hH
      exact Or.inl ⟨hp,four_geometry_of_preserving_endpoint a h.H_centralizes
        (T : Subgroup G) hH.1.2 p H0 H1 H2 d Mc hHMc c.endpoint.representative hout
        (c.endpoint.large_le hb) (c.endpoint.reverse_le hb) hkeep c.quadratic.1.1 hdim hf⟩
    · exact Or.inr ⟨d.prime,source_rankEight_selected_placement hG T hempty hM hunique hmany
        hcard e hab H hH a p H0 H1 H2 d c hdim⟩

/-- Original 14.6.13, with the actual orthogonal action and its first-factor
marking in the four-dimensional branch and both points in the rank-eight branch.
Only the earlier 14.6.12 exchanged-factor setup remains explicit. -/
theorem source_critical_alternatives
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
    let : IsElementaryAbelian 2 D.UH :=
      ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    SourceCriticalAlternatives h a Mc H1 p := by
  dsimp only
  rcases source_critical_geometry_alternatives hG T hempty hM hunique hmany hcard e hab
      H hH a p H0 H1 H2 d with ⟨hp,⟨geo⟩⟩ | hr
  · obtain ⟨_,o,i,hi⟩ := source_rankFour_orthogonal_action hG T hempty hM hunique hmany hcard e hab
      H hH a p H0 H1 H2 d geo.dimension
    refine Or.inl ⟨hp,o,⟨i,geo.g,geo.outside,?_,geo.reverse,?_⟩,hi⟩
    · change (conjugateSpanBy (localModule T M) H).map (MulAut.conj geo.g).toMonoidHom ≤
        H ⊓ normalizer (o.plane i : Set G)
      rw [hi]
      exact geo.normalizes
    · change ¬ ⁅o.plane i,(conjugateSpanBy (localModule T M) H).map
        (MulAut.conj geo.g).toMonoidHom⁆ ≤ centralInvolutions T
      rw [hi]
      exact geo.noncentral
  · exact Or.inr hr

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
