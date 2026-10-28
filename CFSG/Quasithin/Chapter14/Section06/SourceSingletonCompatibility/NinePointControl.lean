module
public import CFSG.Quasithin.Chapter14.Section06.SourceSingletonCompatibility.CoreCentralizers
public import CFSG.Quasithin.Chapter14.Section06.SourceSingletonCompatibility.NineCriticalGeometry

/-!
# Point-centralizer control at the original elementary-nine endpoint

The abelian Mc-span, conjugated by the actual critical representative,
contains the critical span and is normalized by the opposite point
centralizer. Its intersection with J is a normal two-subgroup of that
centralizer. Thus the critical span lies in its literal two-core.

For the selected elementary-nine endpoint, the strict denominator places
the opposite point in [U,J]. It differs from Z because the same critical
representative leaves Mc. `CoreCentralizers` therefore lifts every quotient
stabilizer element to an element of J centralizing this actual point.
All actions, quotients and critical representatives remain unchanged.

These are ambient restrictions on the order-36 case, not an exclusion of
that case or a proof of the full original 14.6.12.
Source: Aschbacher--Smith 14.6.12--13, printed pp.1031--1032,
and F.9.13--17, printed pp.322--324 of refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open OddNormalizer OddCriticalPair.OrthogonalSource
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

/-- The genuine abelian ambient span puts each original critical conjugate
in the two-core of its opposite-point centralizer inside the same J. -/
theorem source_critical_span_le_point_core
    (J : Subgroup G) (hJ : J ∈ Chapter1.HOutside G (T : Set G) (M : Set G)) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ
    ∀ i : h.CriticalEndpoint,
      i.conjugate D.UH ≤ (J ⊓ centralizer (i.conjugate D.V₁ : Set G)).pCoreIn 2 := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ
  change ∀ i : h.CriticalEndpoint, _
  intro i
  obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hu hmany hcard e hab J hJ
  have hJMc : J ≤ Mc := by
    have he := (Section02.source_lemma_14_2_3 hG T hempty hM hu hmany hcard e J hJ.1 hJ.2).1
    exact (show Mc ∈ maximalTwoLocalOvergroups J from he ▸ Set.mem_singleton Mc).2
  let W := conjugateSpanBy (localModule T M) Mc
  let A := i.conjugate W
  let B := J ⊓ A
  let C := J ⊓ centralizer (i.conjugate D.V₁ : Set G)
  let : IsElementaryAbelian 2 (localModule T M) := h.elementary
  let : IsMulCommutative W := hab
  let : IsElementaryAbelian 2 W := conjugateSpanBy_elementary_of_commutative _ _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hp : IsPGroup 2 B := (IsElementaryAbelian.isPGroup 2 A).to_le inf_le_right
  have hZA : i.conjugate D.V₁ ≤ A :=
    map_mono (h.point_lt.le.trans (le_conjugateSpanBy _ _))
  have hAC : A ≤ centralizer (i.conjugate D.V₁ : Set G) :=
    (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hZA)
  have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
    (source_lemma_14_1_18 hG T hempty hM hu hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcn : centralizer (i.conjugate D.V₁ : Set G) ≤ normalizer (A : Set G) := by
    have hn := map_mono (f := (MulAut.conj i.representative).toMonoidHom)
      (le_normalizer_conjugateSpanBy (localModule T M) Mc)
    rw [map_equiv_normalizer_eq,hMc,map_centralizer_equiv] at hn
    rw [←hMc] at hn
    simpa only [D,A,W,ChapterF.Section09.Setup.Hypothesis.CriticalEndpoint.conjugate,coe_map,MulEquiv.coe_toMonoidHom] using hn
  have hn : C ≤ normalizer (B : Set G) :=
    (le_inf (inf_le_left.trans J.le_normalizer) (inf_le_right.trans hcn)).trans
      inf_normalizer_le_normalizer_inf
  have hBC : B ≤ C := le_inf inf_le_left (inf_le_right.trans hAC)
  apply (show i.conjugate D.UH ≤ B from le_inf (i.large_le hb)
    (map_mono (conjugateSpanBy_mono le_rfl hJMc))).trans
  exact le_pCoreIn_of_normalizes hp hBC hn

open OddCriticalPair.Selection in
/-- The elementary-nine selected endpoint has full quotient-stabilizer lifting
and the actual critical-span containment in its point-centralizer two-core. -/
theorem source_singleton_nine_selected_point_control
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
    ∃ (c : SelectedQuadraticEndpoint h a) (u : D.UH),
      c.endpoint.representative ∉ Mc ∧
      (u : G) ∈ c.endpoint.conjugate D.V₁ ∧ (u : G) ∉ D.V₁ ∧
      (∀ t : J ⧸ pCore 2 J,
        a.representation t (Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u)) =
          Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u) →
        ∃ k : J, QuotientGroup.mk' (pCore 2 J) k = t ∧
          (k : G) ∈ centralizer ({(u : G)} : Set G)) ∧
      c.endpoint.conjugate D.UH ≤
        (J ⊓ centralizer ({(u : G)} : Set G)).pCoreIn 2 := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)›
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  change ∃ (c : SelectedQuadraticEndpoint h a) (u : D.UH), _
  obtain ⟨c,hout,_,_,_,hmove,hpoint⟩ := source_singleton_nine_selected_geometry
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine
  have hpCard : Nat.card (c.endpoint.conjugate D.V₁) = 2 :=
    (card_map_of_injective (MulAut.conj c.endpoint.representative).injective).trans h.point_card
  obtain ⟨z,hz,hzne⟩ := (c.endpoint.conjugate D.V₁).bot_or_exists_ne_one.resolve_left (by
    intro hz
    rw [hz,card_bot] at hpCard
    omega)
  have hzZ : z ∉ D.V₁ := by
    intro hzz
    have he : D.V₁ = c.endpoint.conjugate D.V₁ := by
      have hi := inf_eq_bot_of_card_two_of_ne D.V₁ (c.endpoint.conjugate D.V₁)
        h.point_card hpCard
      by_contra hn
      exact hzne ((hi hn).le ⟨hzz,hz⟩)
    apply hout
    have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
      (source_lemma_14_1_18 hG T hempty hM hu hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
    apply hMc.ge
    exact normalizer_le_centralizer_of_card_two D.V₁ h.point_card
      (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  let u : D.UH := ⟨z,hpoint hz⟩
  have huW : (u : G) ∈ ⁅D.UH,J⁆ := by
    have hb := (source_rankTwo_critical_track_bounds hG T hempty hM hu hmany hcard e hab J hJ.1).1
    have hp : c.endpoint.conjugate D.V₁ ≤ ⁅D.UH,J⁆ := by
      rw [←hmove]
      exact commutator_mono (commutatorPreimage_le _ _ _) (c.endpoint.large_le hb)
    exact hp hz
  refine ⟨c,u,hout,hz,hzZ,?_,?_⟩
  · exact source_solvable_moved_point_centralizer_lifts
      hG T hempty hM hu hmany hcard e hab J hJ hs a u huW hzZ
  · have hline : zpowers (u : G) = c.endpoint.conjugate D.V₁ := by
      apply eq_of_le_of_card_ge (zpowers_le.mpr hz)
      rw [hpCard]
      exact Nat.succ_le_of_lt ((zpowers (u : G)).one_lt_card_iff_ne_bot.mpr
        (fun hb => hzne (Subgroup.zpowers_eq_bot.mp hb)))
    have he : centralizer ({(u : G)} : Set G) = centralizer (c.endpoint.conjugate D.V₁ : Set G) := by
      rw [←centralizer_closure,←zpowers_eq_closure,hline]
    rw [he]
    exact source_critical_span_le_point_core hG T hempty hM hu hmany hcard e hab J hJ.1 c.endpoint

end CFSG.Quasithin.Chapter14.Section06
