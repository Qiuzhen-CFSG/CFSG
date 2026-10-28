module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Selection.StrictOrthogonalSource
public import Theory.Representation.BinaryOffender.DihedralProductDisplacement

/-!
# Confinement and central-point placement for the rank-eight endpoint

The original moved module has a globally fixed supplement. Displacements
in its two dihedral summands therefore have additive ranks. An elementary
actor moving both four-dimensional summands would have a displacement of
rank at least four, contradicting the selected denominator's bound of three.
Thus the actual endpoint actor lies in one factor, and its rank and the
literal denominator codimension both equal one.

A nontrivial involution of that factor has displacement rank at least two.
The denominator commutator consequently fills the transported central line,
placing it in the same covering support. The actual factor exchanger aligns
both the actor and the point while transporting the strict two-core
intersection. Under the separately supplied fitting and normalizer inputs
of 14.6.14--16, this contradicts the suitable point's non-two-centrality.

The final consumer reduces suitable-element existence to the cyclic swapping
endpoint. It does not claim the full alternatives of 14.6.13: their swapping
exclusion and reverse-point clause remain with qt-e-suitable-orthogonal-marking.
The earlier exchanged-factor, fitting and normalizer inputs retain final
discharge with qt-e-suitable-existence.

Source: Aschbacher--Smith 14.6.13, equation (*) and the last paragraph on
printed p.1032; 14.6.17(1--2), printed pp.1035--1036.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
open OddNormalizer Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open Chapter13.Section08.SourceCompletion Chapter13.Section08.CriticalGeometry
variable {G : Type*} [Group G] [Finite G]
variable {H U Z : Subgroup G} [IsElementaryAbelian 2 U]

omit [Finite G] in
/-- Actual commutators of an actor confined to a factor lie in its covering support. -/
theorem commutator_le_support_of_actor_le
    (a : LocalQuotientAction H U Z) (hz : H ≤ centralizer (Z : Set G))
    (K B : Subgroup G) (hBH : B ≤ H) (hB : actorImage H B ≤ actorImage H K) :
    ⁅U,B⁆ ≤ firstSupport a K := by
  let s := ModuleBound.OriginalF916.conjugationSection a hz
  rw [commutator_comm]
  apply commutator_le.mpr
  intro b hb u hu
  let bH : H := ⟨b,hBH hb⟩
  let uU : U := ⟨u,hu⟩
  apply (mem_supportPreimage a _ ⟨⁅b,u⁆,s.commutator_mem bH uU⟩).mpr
  change (s.quotient ⟨⁅b,u⁆,s.commutator_mem bH uU⟩).toAdd ∈ _
  rw [← s.displacement bH uU]
  exact Submodule.subset_span ⟨QuotientGroup.mk' (pCore 2 H) bH,
    hB (mem_map_of_mem _ hb),(s.quotient uU).toAdd,Submodule.mem_top,rfl⟩

/-- A nontrivial elementary actor in a dihedral factor moving four dimensions
has fixed codimension at least two. -/
theorem factor_fixedCodim_ge_two
    (a : LocalQuotientAction H U Z) (p : ℕ) (hp : p = 3 ∨ p = 5)
    (K B : Subgroup G) (he : actorImage H K ≃* DihedralGroup p)
    [IsElementaryAbelian 2 (actorImage H B)]
    (hne : actorImage H B ≠ ⊥) (hle : actorImage H B ≤ actorImage H K)
    (hdim : Module.finrank (ZMod 2)
      (subspaceCommutator a.representation ⊤ (actorImage H K)) = 4) :
    2 ≤ fixedCodim a.representation (actorImage H B) := by
  obtain ⟨t,ht,htne⟩ : ∃ t ∈ actorImage H B, t ≠ 1 := by
    by_contra! hh
    exact hne (eq_bot_iff.mpr (fun t ht => mem_bot.mpr (hh t ht)))
  let tK : actorImage H K := ⟨t,hle ht⟩
  have hd := dihedral_moved_le_twice_displacement a.representation hp _ he tK
    (fun hh => htne (congrArg Subtype.val hh))
    (Subtype.ext (elemPow_eq_one_of_isElementaryAbelian t ht))
  rw [hdim] at hd
  have hf := Submodule.finrank_mono (fixedSpace_antitone a.representation (zpowers_le.mpr ht))
  have hh := fixedCodim_add_finrank a.representation (actorImage H B)
  have hj := fixedCodim_add_finrank a.representation (zpowers t)
  rw [fixedCodim_zpowers_eq_displacement_rank] at hj
  change 4 ≤ 2 * Module.finrank (ZMod 2) (LinearMap.range (a.representation t - LinearMap.id)) at hd
  omega

/-- A codimension-one denominator and the rank-four factor force the opposite
central line into that factor's actual covering support. -/
theorem point_le_support_of_confined_actor
    (a : LocalQuotientAction H U Z) (hz : H ≤ centralizer (Z : Set G))
    (p : ℕ) (hp : p = 3 ∨ p = 5) (K B C : Subgroup G)
    (he : actorImage H K ≃* DihedralGroup p)
    [IsElementaryAbelian 2 (actorImage H B)]
    (hBH : B ≤ H) (hne : actorImage H B ≠ ⊥)
    (hle : actorImage H B ≤ actorImage H K)
    (hdim : Module.finrank (ZMod 2)
      (subspaceCommutator a.representation ⊤ (actorImage H K)) = 4)
    (hUC : U ≤ normalizer (C : Set G)) (hC : Nat.card C = 2)
    (hr : Nat.log 2 ((commutatorPreimage U B C).relIndex U) = 1) :
    C ≤ firstSupport a K := by
  let s := ModuleBound.OriginalF916.conjugationSection a hz
  have hcodim := factor_fixedCodim_ge_two a p hp K B he hne hle hdim
  have hc := f9_denominator_commutator_eq_point s hBH hUC hC (by
    change Nat.log 2 ((commutatorPreimage U B C).relIndex U) < _
    rw [hr]
    exact hcodim)
  rw [← hc]
  exact (commutator_mono (commutatorPreimage_le U B C) le_rfl).trans
    (commutator_le_support_of_actor_le a hz K B hBH hle)

omit [Finite G] in
/-- The original factor exchanger aligns the actor and point simultaneously.
Conjugation transports the strict intersection with the actual two-core. -/
theorem first_factor_point_of_either_factor
    (a : LocalQuotientAction H U Z) (T : Subgroup G) (hTH : T ≤ H)
    (p : ℕ) (H0 H1 H2 : Subgroup G) (d : ExchangedFactorSetup a T p H0 H1 H2)
    (Mc : Subgroup G) (hHMc : H ≤ Mc) (g : G) (hout : g ∉ Mc)
    (hBH : U.map (MulAut.conj g).toMonoidHom ≤ H)
    (hstrict : U.map (MulAut.conj g).toMonoidHom ⊓ H.pCoreIn 2 <
      U.map (MulAut.conj g).toMonoidHom)
    (hcase : (actorImage H (U.map (MulAut.conj g).toMonoidHom) ≤ actorImage H H1 ∧
        Z.map (MulAut.conj g).toMonoidHom ≤ firstSupport a H1) ∨
      (actorImage H (U.map (MulAut.conj g).toMonoidHom) ≤ actorImage H H2 ∧
        Z.map (MulAut.conj g).toMonoidHom ≤ firstSupport a H2)) :
    ∃ k : G, k ∉ Mc ∧ U.map (MulAut.conj k).toMonoidHom ≤ H ∧
      actorImage H (U.map (MulAut.conj k).toMonoidHom) ≤ actorImage H H1 ∧
      U.map (MulAut.conj k).toMonoidHom ⊓ H.pCoreIn 2 <
        U.map (MulAut.conj k).toMonoidHom ∧
      Z.map (MulAut.conj k).toMonoidHom ≤ firstSupport a H1 := by
  rcases hcase with ⟨hfirst,hpoint⟩ | ⟨hsecond,hpoint⟩
  · exact ⟨g,hout,hBH,hfirst,hstrict,hpoint⟩
  · obtain ⟨x,hx,_,hex⟩ := d.exchanged
    let xH : H := ⟨x,hTH hx⟩
    have hHconj : H.map (MulAut.conj x).toMonoidHom = H :=
      mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer xH.property)
    have hQconj : (H.pCoreIn 2).map (MulAut.conj x).toMonoidHom = H.pCoreIn 2 := by
      rw [← AmalgamLocalCores.pCoreIn_map_of_injective
        2 (MulAut.conj x).toMonoidHom (MulAut.conj x).injective H,hHconj]
    have hm (K : Subgroup G) : (K.map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj x).toMonoidHom = K.map (MulAut.conj (x*g)).toMonoidHom :=
      (conjBy_mul K x g).symm
    have hout' : x*g ∉ Mc := by
      intro hh
      have hh' := Mc.mul_mem (Mc.inv_mem (hHMc xH.property)) hh
      exact hout (by simpa only [show (xH:G) = x from rfl,inv_mul_cancel_left] using hh')
    have hBH' := map_mono (f := (MulAut.conj x).toMonoidHom) hBH
    rw [hm U,hHconj] at hBH'
    have hstrict' := (map_lt_map_iff_of_injective
      (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective).mpr hstrict
    rw [map_inf _ _ _ (MulAut.conj x).injective,hQconj,hm U] at hstrict'
    have hfirst := exchange_factor_actor_transport a p d hTH x hx hex _ hsecond
    have he := actorImage_conjugate (U.map (MulAut.conj g).toMonoidHom) hBH xH
    change actorImage H ((U.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj x).toMonoidHom) = _ at he
    rw [hm U] at he
    have hpoint' := exchange_factor_support_transport a p d hTH x hx hex _ hpoint
    rw [hm Z] at hpoint'
    exact ⟨x*g,hout',hBH',he.symm ▸ hfirst,hstrict',hpoint'⟩

open Theory.GroupTheory OrthogonalSource SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter13.Section08
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

/-- In the rank-eight action, the selected actor is confined to one of the
literal original factors, and both ranks in (*) equal one. -/
theorem source_rankEight_selected_confinement
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
    let : IsElementaryAbelian 2 D.UH :=
      ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    ∀ c : SelectedQuadraticEndpoint h a,
      Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⊤) = 8 →
      let B := actorImage H (c.endpoint.conjugate D.UH)
      (B ≤ actorImage H H1 ∨ B ≤ actorImage H H2) ∧ rank B = 1 ∧
        Nat.log 2 ((commutatorPreimage D.UH (c.endpoint.conjugate D.UH)
          (c.endpoint.conjugate D.V₁)).relIndex D.UH) = 1 := by
  dsimp only
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
  intro c hdim
  let B := actorImage H (c.endpoint.conjugate D.UH)
  let : IsElementaryAbelian 2 B := c.quadratic.1.2
  have hf (g : H ⧸ pCore 2 H)
      (hfix : ∀ v ∈ subspaceCommutator a.representation ⊤ ⊤, a.representation g v = v) : g = 1 := by
    apply source_rankTwo_residual_moved_faithful hG T hempty hM hunique hmany hcard e hab H hH a g
    rw [← source_rankTwo_whole_moved_eq_residual hG T hempty hM hunique hmany hcard e hab H hH a]
    exact hfix
  have hkeep := exchanged_quadratic_preserves_of_eight a (T : Subgroup G) hH.1.2
    p H0 H1 H2 d hf B c.quadratic hdim
  have hr := exchanged_preserving_actor_rank a (T : Subgroup G) p H0 H1 H2 d B hkeep
  obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hunique hmany hcard e hab H hH
  have hdisp (t : H ⧸ pCore 2 H) (ht : t ∈ B) :
      Module.finrank (ZMod 2) (LinearMap.range (a.representation t - LinearMap.id)) ≤ 3 := by
    have hh := c.displacement_rank_le hb ht
    have hd := c.comparison.trans hr
    exact hh.trans (Nat.add_le_add_right hd 1)
  have heq := exchanged_dimensions_eq a (T : Subgroup G) hH.1.2 p H0 H1 H2 d
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (subspaceCommutator a.representation ⊤ (actorImage H H1))
    (subspaceCommutator a.representation ⊤ (actorImage H H2))
  rw [d.split,d.disjoint.eq_bot,finrank_bot,add_zero,hdim] at hsum
  have hfixsup : (subspaceCommutator a.representation ⊤ (actorImage H H1) ⊔
      subspaceCommutator a.representation ⊤ (actorImage H H2)) ⊔
      fixedSpace a.representation ⊤ = ⊤ := by
    rw [d.split,source_rankTwo_whole_moved_eq_residual
      hG T hempty hM hunique hmany hcard e hab H hH a]
    exact source_rankTwo_span_decomposition hG T hempty hM hunique hmany hcard e hab H hH a
  have hjoin : actorImage H H0 = actorImage H H1 ⊔ actorImage H H2 := by
    unfold actorImage
    rw [← Subgroup.map_sup,← subgroupOf_sup (d.first_le.trans d.zero_le)
      (d.second_le.trans d.zero_le),d.join_eq]
  have hfactor := dihedral_actor_le_factor_of_displacement_le_three a.representation d.prime
    (actorImage H H1) (actorImage H H2) B (hjoin ▸ hkeep)
    d.first_model.some d.second_model.some d.actors_disjoint d.actors_commute
    d.disjoint hfixsup (by omega) (by omega) hdisp
  have hr1 : rank B ≤ 1 := by
    rcases hfactor with hh | hh
    · exact elementary_rank_le_one_of_dihedral d.prime _ _ d.first_model.some hh
    · exact elementary_rank_le_one_of_dihedral d.prime _ _ d.second_model.some hh
  have hp := c.denominator_rank_pos
  have hc := c.comparison
  exact ⟨hfactor,le_antisymm hr1 (hp.trans_le hc),le_antisymm (hc.trans hr1) hp⟩

/-- The rank-eight selected endpoint has its central point in the support
of the same dihedral factor containing its actor. -/
theorem source_rankEight_selected_point
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
    let : IsElementaryAbelian 2 D.UH :=
      ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    ∀ c : SelectedQuadraticEndpoint h a,
      Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⊤) = 8 →
      (actorImage H (c.endpoint.conjugate D.UH) ≤ actorImage H H1 ∧
        c.endpoint.conjugate D.V₁ ≤ firstSupport a H1) ∨
      (actorImage H (c.endpoint.conjugate D.UH) ≤ actorImage H H2 ∧
        c.endpoint.conjugate D.V₁ ≤ firstSupport a H2) := by
  dsimp only
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  intro c hdim
  obtain ⟨hfactor,_,hr⟩ := source_rankEight_selected_confinement
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 d c hdim
  let : IsElementaryAbelian 2 (actorImage H (c.endpoint.conjugate D.UH)) := c.quadratic.1.2
  obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hunique hmany hcard e hab H hH
  have hBH : c.endpoint.conjugate D.UH ≤ H := c.endpoint.large_le hb
  have hnorm : D.UH ≤ normalizer (c.endpoint.conjugate D.V₁ : Set G) := by
    have hn := map_mono (f := (MulAut.conj c.endpoint.representative).toMonoidHom)
      (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    rw [map_equiv_normalizer_eq] at hn
    exact (c.endpoint.reverse_le hb).trans hn
  have hC : Nat.card (c.endpoint.conjugate D.V₁) = 2 := by
    change Nat.card (D.V₁.map (MulAut.conj c.endpoint.representative).toMonoidHom) = 2
    rw [card_map_of_injective (MulAut.conj c.endpoint.representative).injective,h.point_card]
  have heq := exchanged_dimensions_eq a (T : Subgroup G) hH.1.2 p H0 H1 H2 d
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (subspaceCommutator a.representation ⊤ (actorImage H H1))
    (subspaceCommutator a.representation ⊤ (actorImage H H2))
  rw [d.split,d.disjoint.eq_bot,finrank_bot,add_zero,hdim] at hsum
  rcases hfactor with hfirst | hsecond
  · exact Or.inl ⟨hfirst,point_le_support_of_confined_actor a h.H_centralizes p d.prime
      H1 _ _ d.first_model.some hBH c.quadratic.1.1 hfirst (by omega) hnorm hC hr⟩
  · exact Or.inr ⟨hsecond,point_le_support_of_confined_actor a h.H_centralizes p d.prime
      H2 _ _ d.second_model.some hBH c.quadratic.1.1 hsecond (by omega) hnorm hC hr⟩

/-- The rank-eight selected branch is excluded by the permitted earlier
14.6.14--16 inputs. Only the first point containment is needed for this
14.6.17 consumer; constructing the second containment of 14.6.13 remains
an independent obligation of this task. -/
theorem source_rankEight_selected_impossible
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
      Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⊤) ≠ 8 := by
  dsimp only
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  intro c hout hdim
  obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hunique hmany hcard e hab H hH
  have hBH : c.endpoint.conjugate D.UH ≤ H := c.endpoint.large_le hb
  have hstrict := c.strict
  rw [critical_denominator_eq h _ hBH] at hstrict
  have hcase := source_rankEight_selected_point hG T hempty hM hunique hmany hcard e hab
    H hH a 3 H0 H1 H2 d c hdim
  have hHMc : H ≤ Mc := by
    have hHZ := (Section02.source_lemma_14_2_3 hG T hempty hM hunique hmany hcard e H hH.1 hH.2).1
    have hm : Mc ∈ maximalTwoLocalOvergroups H := hHZ ▸ Set.mem_singleton _
    exact hm.2
  obtain ⟨g,hout',hBH',hfirst,hstrict',hpoint⟩ := first_factor_point_of_either_factor
    a (T : Subgroup G) hH.1.2 3 H0 H1 H2 d Mc hHMc c.endpoint.representative
    hout hBH hstrict hcase
  exact source_critical_point_not_le_first_support
    hG T hempty hM hunique hmany hcard e hab H hH a H0 H1 H2 d hF hN
    g hout' hBH' hfirst hstrict' hpoint

/-- With the allowed earlier-source inputs, the suitable terminal construction
is now reduced solely to excluding the cyclic swapping endpoint. This theorem
retains that actual endpoint and does not assert the unfinished source alternative. -/
theorem source_terminal_witness_or_swapping_endpoint
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
    SourceTerminalWitness hG T hempty hM hunique hmany hcard e hab ∨
      (∃ c : SelectedQuadraticEndpoint h a, c.endpoint.representative ∉ Mc ∧
        Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⊤) = 4 ∧
        let B := actorImage H (c.endpoint.conjugate D.UH)
        ∃ t ∈ B, B = zpowers t ∧ Nat.card B = 2 ∧ rank B = 1 ∧
          (subspaceCommutator a.representation ⊤ (actorImage H H1)).map (a.representation t) =
            subspaceCommutator a.representation ⊤ (actorImage H H2) ∧
          (subspaceCommutator a.representation ⊤ (actorImage H H2)).map (a.representation t) =
            subspaceCommutator a.representation ⊤ (actorImage H H1)) := by
  dsimp only
  rcases source_rankTwo_marked_or_quadratic_obstruction
      hG T hempty hM hunique hmany hcard e hab H hH a 3 H0 H1 H2 d with
      ⟨_,o,critical,hi⟩ | ⟨c,hout,he | he⟩
  · exact Or.inl (source_terminal_witness_of_marked_orthogonal_pair
      hG T hempty hM hunique hmany hcard e hab H hH o critical a H0 H1 H2 d hi hF hN)
  · exact False.elim (source_rankEight_selected_impossible
      hG T hempty hM hunique hmany hcard e hab H hH a H0 H1 H2 d hF hN c hout he.1)
  · exact Or.inr ⟨c,hout,he.2⟩

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
