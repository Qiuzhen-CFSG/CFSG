module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Selection.SwappingGeometry
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.OrthogonalSource.Recognition
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Alternatives.Selection
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Alternatives.Quadratic
/-!
# The selected endpoint preserves the original two planes

The rank-one denominator of a cyclic swapping endpoint has codimension
strictly smaller than its fixed-space codimension. Its commutator therefore
fills the transported central line and puts that line inside [U_H,H].
The point-centralizer lifting and abelian-span obstruction then rule out
plane interchange. All quotient maps and the actual endpoint are retained.

These conclusions use the original rank-two hypotheses and 14.6.12 alone.
The rank-eight reverse-point marking is assembled in Alternatives.Source.
The terminal consumer is in
Selection.SwappingTerminal, with earlier 14.6.14--16 discharge retained by
qt-e-suitable-existence.

Source: Aschbacher--Smith 14.6.13, printed pp.1031--1032.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
open OddNormalizer OrthogonalSource SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter13.Section08 Chapter13.Section08.SourceCompletion Chapter13.Section08.CriticalGeometry
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

/-- The cyclic swapping alternative is impossible for the actual selected
endpoint. The strict denominator places its central point in the moved group;
then the abelian Mc-span contradicts the full point-stabilizer action. -/
theorem source_selected_not_swapping
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
    let : IsElementaryAbelian 2 D.UH :=
      ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    ∀ c : SelectedQuadraticEndpoint h a, c.endpoint.representative ∉ Mc →
      Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⊤) = 4 →
      rank (actorImage H (c.endpoint.conjugate D.UH)) = 1 →
      ∀ t ∈ actorImage H (c.endpoint.conjugate D.UH),
        (subspaceCommutator a.representation ⊤ (actorImage H H1)).map (a.representation t) ≠
          subspaceCommutator a.representation ⊤ (actorImage H H2) := by
  dsimp only
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  intro c hout hdim hr t ht hswap
  obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hunique hmany hcard e hab H hH
  let B := c.endpoint.conjugate D.UH
  let C := c.endpoint.conjugate D.V₁
  have hBH : B ≤ H := c.endpoint.large_le hb
  have hnorm : D.UH ≤ normalizer (C : Set G) := by
    have hh := map_mono (f := (MulAut.conj c.endpoint.representative).toMonoidHom)
      (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    rw [map_equiv_normalizer_eq] at hh
    exact (c.endpoint.reverse_le hb).trans hh
  have hC : Nat.card C = 2 := by
    change Nat.card (D.V₁.map (MulAut.conj c.endpoint.representative).toMonoidHom) = 2
    rw [card_map_of_injective (MulAut.conj c.endpoint.representative).injective,h.point_card]
  have hfirst : Module.finrank (ZMod 2)
      (subspaceCommutator a.representation ⊤ (actorImage H H1)) = 2 := by
    have he := exchanged_dimensions_eq a (T : Subgroup G) hH.1.2 p H0 H1 H2 d
    have hh := Submodule.finrank_sup_add_finrank_inf_eq
      (subspaceCommutator a.representation ⊤ (actorImage H H1))
      (subspaceCommutator a.representation ⊤ (actorImage H H2))
    rw [d.split,d.disjoint.eq_bot,finrank_bot,add_zero,hdim] at hh
    omega
  have hcodim := finrank_le_fixedCodim_of_disjoint_map a.representation
    (subspaceCommutator a.representation ⊤ (actorImage H H1)) ht
    (by rw [hswap]; exact d.disjoint)
  rw [hfirst] at hcodim
  have hden := c.comparison
  rw [hr] at hden
  let s := ModuleBound.OriginalF916.conjugationSection a h.H_centralizes
  have hcomm : ⁅commutatorPreimage D.UH B C,B⁆ = C :=
    f9_denominator_commutator_eq_point s hBH hnorm hC (by
      change Nat.log 2 ((commutatorPreimage D.UH B C).relIndex D.UH) <
        fixedCodim a.representation (actorImage H B)
      exact lt_of_le_of_lt hden (lt_of_lt_of_le (by decide : 1 < 2) hcodim))
  have hCK : C ≤ ⁅D.UH,H⁆ := by
    rw [←hcomm]
    exact commutator_mono (commutatorPreimage_le _ _ _) hBH
  have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
    (source_lemma_14_1_18 hG T hempty hM hunique hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hdis : centralInvolutions T ⊓ C = ⊥ := by
    apply inf_eq_bot_of_card_two_of_ne _ _ h.point_card hC
    intro he
    apply hout
    apply hMc.ge
    exact normalizer_le_centralizer_of_card_two _ h.point_card
      (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  obtain ⟨z,hz,hzn⟩ := C.bot_or_exists_ne_one.resolve_left (by
    intro he
    rw [he,card_bot] at hC
    omega)
  have hzZ : z ∉ centralInvolutions T := by
    intro hh
    exact hzn (hdis.le ⟨hh,hz⟩)
  obtain ⟨_,o,i,hi⟩ := source_rankFour_orthogonal_action hG T hempty hM hunique hmany hcard e hab
    H hH a p H0 H1 H2 d hdim
  obtain ⟨x,hx,rfl⟩ := ht
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hx2 : x^2=1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := B) (x : G) hx)
  have hno := source_swapping_impossible_of_point_in_moved hG T hempty hM hunique hmany hcard e hab
    H hH a p H0 H1 H2 d o i hi c.endpoint.representative (c.endpoint.reverse_le hb)
    z hz hzn hzZ (hCK hz) x hx hx2
  exact exchanging_actor_has_shift a (T : Subgroup G) p H0 H1 H2 d o i hi x hswap hno

/-- Every selected quadratic endpoint preserves the original two summands.
The swapping alternative is excluded using the source abelian Mc-span. -/
theorem source_selected_actor_preserves
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
    let : IsElementaryAbelian 2 D.UH :=
      ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    ∀ c : SelectedQuadraticEndpoint h a, c.endpoint.representative ∉ Mc →
      actorImage H (c.endpoint.conjugate D.UH) ≤ actorImage H H0 := by
  dsimp only
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
  intro c hout
  have hf (g : H ⧸ pCore 2 H)
      (hfix : ∀ v ∈ subspaceCommutator a.representation ⊤ ⊤, a.representation g v = v) : g = 1 := by
    apply source_rankTwo_residual_moved_faithful hG T hempty hM hunique hmany hcard e hab H hH a g
    rw [← source_rankTwo_whole_moved_eq_residual hG T hempty hM hunique hmany hcard e hab H hH a]
    exact hfix
  rcases exchanged_quadratic_preserves_or_swaps a (T : Subgroup G) hH.1.2 p H0 H1 H2 d hf
      _ c.quadratic with hkeep | ⟨_,hdim,t,ht,_,_,hr,hswap,_⟩
  · exact hkeep
  · exact False.elim (source_selected_not_swapping hG T hempty hM hunique hmany hcard e hab
      H hH a p H0 H1 H2 d c hout hdim hr t ht hswap)

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
