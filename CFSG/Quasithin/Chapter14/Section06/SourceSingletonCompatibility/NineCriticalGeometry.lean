module
public import CFSG.Quasithin.Chapter14.Section06.SourceSingletonCompatibility.NineQuotient
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Alternatives.Selection

/-!
# Strict endpoint geometry in the elementary-nine singleton

Cubic ratio two excludes the full-denominator selection: conjugating its
returned-line action back would put the same critical span in the original
two-core. The genuine strict quadratic endpoint therefore exists.

In the elementary-nine singleton its actual actor has order two. The F.9
comparison gives denominator codimension one, whereas the quadratic bound
and cubic ratio give fixed codimension two. The strict inequality forces
the denominator commutator to equal the entire opposite central point and
places that point in the original span. The original quotient, endpoint
and conjugator are retained. This supplies endpoint geometry for the
singleton-exclusion argument; it does not itself exclude that branch.

Source: Aschbacher--Smith 14.6.12--13, printed p.1031, and F.9.13--17,
printed pp.322--324 of refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open OddCriticalPair.Selection
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab

/-- Ratio two forces a genuine strict quadratic endpoint with its original
conjugator outside the same maximal point centralizer. -/
theorem source_rankTwo_strict_endpoint_of_ratio_two
    (J : Subgroup G) (hJ : J ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (hq : cubicRatio a.representation = 2) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    letI : IsElementaryAbelian 2 D.UH :=
      ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)›
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ
    ∃ c : SelectedQuadraticEndpoint h a, c.endpoint.representative ∉ Mc := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)›
  change ∃ c : SelectedQuadraticEndpoint h a, c.endpoint.representative ∉ Mc
  obtain ⟨hb,ho,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hu hmany hcard e hab J hJ
  rcases full_or_selected D h rfl a hb ho
      (source_rankTwo_intersecting_conjugates_commute hG T hempty hM hu hmany hcard e hab) with
    ⟨i,t,ht⟩ | hselected
  · exfalso
    apply source_rankTwo_critical_core_escape_of_ratio_two
      hG T hempty hM hu hmany hcard e hab J hJ a hq i
    have hc := congrArg (fun A : Subgroup G => A.map
      (MulAut.conj i.representative).toMonoidHom) t.commutator
    rw [map_commutator,ht] at hc
    change ⁅i.conjugate D.UH,(D.UH.conjBy i.representative⁻¹).conjBy i.representative⁆ =
      (D.V₁.conjBy i.representative⁻¹).conjBy i.representative at hc
    rw [conjBy_inv',conjBy_inv',commutator_comm] at hc
    rw [←h.kernel_UH_eq_QH]
    intro x hx
    exact (h.mem_kernel_iff h.UH_le_H).mpr
      ⟨i.large_le hb hx,fun u hu => hc.le (commutator_mem_commutator hu hx)⟩
  · obtain ⟨c⟩ := hselected
    exact ⟨c,source_rankTwo_critical_not_mem_Mc hG T hempty hM hu hmany hcard e hab J hJ c.endpoint⟩

/-- The original elementary-nine singleton supplies the exact selected ranks
and a moving denominator whose commutator is the opposite central point. -/
theorem source_singleton_nine_selected_geometry
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    letI : IsElementaryAbelian 2 D.UH :=
      ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)›
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
    ∃ c : SelectedQuadraticEndpoint h a,
      c.endpoint.representative ∉ Mc ∧
      rank (actorImage J (c.endpoint.conjugate D.UH)) = 1 ∧
      Nat.log 2 ((commutatorPreimage D.UH (c.endpoint.conjugate D.UH)
        (c.endpoint.conjugate D.V₁)).relIndex D.UH) = 1 ∧
      fixedCodim a.representation (actorImage J (c.endpoint.conjugate D.UH)) = 2 ∧
      ⁅commutatorPreimage D.UH (c.endpoint.conjugate D.UH)
          (c.endpoint.conjugate D.V₁), c.endpoint.conjugate D.UH⁆ =
        c.endpoint.conjugate D.V₁ ∧
      c.endpoint.conjugate D.V₁ ≤ D.UH := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)›
  obtain ⟨hq,hb,_,_⟩ := source_singleton_nine_critical_reciprocity
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine
  have hselected : ∃ c : SelectedQuadraticEndpoint h a, c.endpoint.representative ∉ Mc :=
    source_rankTwo_strict_endpoint_of_ratio_two
      hG T hempty hM hu hmany hcard e hab J hJ.1 a hq
  obtain ⟨c,hout⟩ := hselected
  have hr : rank (actorImage J (c.endpoint.conjugate D.UH)) = 1 := by
    obtain ⟨hc,_⟩ := source_singleton_nine_critical_image
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine c.endpoint
    change Nat.card (actorImage J (c.endpoint.conjugate D.UH)) = 2 at hc
    change Nat.log 2 _ = 1
    rw [hc]
    decide
  have hden : Nat.log 2 ((commutatorPreimage D.UH (c.endpoint.conjugate D.UH)
      (c.endpoint.conjugate D.V₁)).relIndex D.UH) = 1 := by
    have hp : 0 < Nat.log 2 ((commutatorPreimage D.UH (c.endpoint.conjugate D.UH)
        (c.endpoint.conjugate D.V₁)).relIndex D.UH) := c.denominator_rank_pos
    have hl : Nat.log 2 ((commutatorPreimage D.UH (c.endpoint.conjugate D.UH)
        (c.endpoint.conjugate D.V₁)).relIndex D.UH) ≤
        rank (actorImage J (c.endpoint.conjugate D.UH)) := c.comparison
    rw [hr] at hl
    omega
  have hcod : fixedCodim a.representation (actorImage J (c.endpoint.conjugate D.UH)) = 2 := by
    have hl : cubicRatio a.representation ≤ actionRatio a.representation
        (actorImage J (c.endpoint.conjugate D.UH)) :=
      iInf_le_of_le _ (iInf_le_of_le ⟨c.quadratic.1,
        isCubic_of_isQuadratic c.quadratic.2.1⟩ le_rfl)
    have hl' : 2 ≤ (fixedCodim a.representation
        (actorImage J (c.endpoint.conjugate D.UH)) : ENNReal) := by
      simpa only [hq,actionRatio,hr,Nat.cast_one,div_one] using hl
    have hl'' : 2 ≤ fixedCodim a.representation
        (actorImage J (c.endpoint.conjugate D.UH)) := by exact_mod_cast hl'
    have hu : fixedCodim a.representation (actorImage J (c.endpoint.conjugate D.UH)) ≤
        2 * rank (actorImage J (c.endpoint.conjugate D.UH)) := c.quadratic.2.2
    rw [hr] at hu
    omega
  have hnorm : D.UH ≤ normalizer (c.endpoint.conjugate D.V₁ : Set G) := by
    have hn := map_mono (f := (MulAut.conj c.endpoint.representative).toMonoidHom)
      (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    rw [map_equiv_normalizer_eq] at hn
    exact (c.endpoint.reverse_le hb).trans hn
  have hpoint : Nat.card (c.endpoint.conjugate D.V₁) = 2 :=
    (card_map_of_injective (MulAut.conj c.endpoint.representative).injective).trans h.point_card
  have hA : c.endpoint.conjugate D.UH ≤ D.H := c.endpoint.large_le hb
  have hstrict : Nat.log 2 ((commutatorPreimage D.UH (c.endpoint.conjugate D.UH)
      (c.endpoint.conjugate D.V₁)).relIndex D.UH) <
      fixedCodim a.representation (actorImage J (c.endpoint.conjugate D.UH)) := by
    rw [hden,hcod]
    decide
  have hmove := Chapter13.Section08.SourceCompletion.f9_denominator_commutator_eq_point
    (ModuleBound.OriginalF916.conjugationSection a h.H_centralizes)
    hA hnorm hpoint hstrict
  refine ⟨c,hout,hr,hden,hcod,hmove,?_⟩
  rw [←hmove]
  exact (commutator_mono (commutatorPreimage_le _ _ _) le_rfl).trans
    ((c.endpoint.commutator hb).trans inf_le_left)

end CFSG.Quasithin.Chapter14.Section06
