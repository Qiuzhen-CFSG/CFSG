module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.TwoComponents
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.ActorData
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.Alternatives
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SectionCentralizers
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic

/-!
# The conditional projection argument for 15.3.39

In a strict component orbit, the two-conjugate reduction gives a swapping
element and commuting components. Multiplication coordinates prove the
inner-action premise of 15.3.12(2). Quasisimplicity makes the two-core central,
so the section centralizer in that lemma equals the ordinary centralizer.
The residual splitting then supplies the two conjugate factors, each with
a normal two-subgroup and simple quotient. The projection theorem constructs
equal actor images and contradicts the nontrivial plane commutator.

The center/rank comparison and the construction of `PlaneActorPair` are still
explicit geometric premises of the exported conditional theorem. This is not
yet the source-only statement of 15.3.39. Identification of the two actors
with the component factors for 15.3.40 is also a separate obligation.
Only the three-part and order-nine quotient clauses of 15.3.12 are used;
the printed stronger order assertion for Y_C is not used.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.12(2),
15.3.37 and 15.3.39, printed pp.1125 and 1135--1138.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo
variable {G : Type*} [Group G]

private theorem relative_component_quasisimple {L I : Subgroup G}
    (hLI : L ≤ I) (hL : IsComponent I (L.subgroupOf I)) : IsQuasisimple L := by
  let := hL.2
  exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLI)

private theorem twoCore_le_center_of_quasisimple [Finite G] [IsQuasisimple G] :
    pCore 2 G ≤ center G := by
  rcases IsQuasisimple.normal_le_center_or_eq_top (pCore 2 G) with h | h
  · exact h
  · have hp : IsPGroup 2 G := by
      have hp : IsPGroup 2 (⊤ : Subgroup G) := h ▸ pCore_isPGroup (p := 2) (G := G)
      exact hp.of_surjective (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom
        (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).surjective
    let := hp.isNilpotent
    let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
    let : Nontrivial G := (QuotientGroup.mk'_surjective (center G)).nontrivial
    exact (Group.IsPerfect.not_isSolvable G inferInstance).elim

/-- In the actual component product, conjugation on the first factor is
inner. This supplies the action premise of 15.3.12(2). -/
theorem inner_on_twoCoreQuotient_of_component_product {Y L K : Subgroup G}
    (hd : Disjoint L K) (hc : L ≤ centralizer (K : Set G))
    (hY : Y ≤ L ⊔ K) : ComponentIntersection.InducesInnerOnTwoCoreQuotient Y L := by
  have hCK : centralizer (L : Set G) ≤ Chapter4.sectionCentralizer L := by
    apply le_commutatorPreimage (Subgroup.centralizer_le_normalizer _)
    exact (commutator_eq_bot_iff_le_centralizer.mpr le_rfl).le.trans bot_le
  intro y hy
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting L K hd hc
  let ab := e.symm ⟨y, hY hy⟩
  have hab : (ab.1 : G) * (ab.2 : G) = y :=
    (he ab.1 ab.2).symm.trans (congrArg Subtype.val (e.apply_symm_apply ⟨y, hY hy⟩))
  refine ⟨ab.1, ab.1.property, hCK ?_⟩
  rw [← hab, inv_mul_cancel_left]
  exact (le_centralizer_iff.mp hc) ab.2.property

/-- The strict-orbit consequence of the actual alternatives 15.3.37. -/
theorem le_componentOrbit_of_strict_of_alternatives {Yplus L S : Subgroup G}
    (h : Candidates.Alternatives15337 Yplus L (componentOrbit L S))
    (hlt : L < componentOrbit L S) : Yplus ≤ componentOrbit L S := by
  rcases h with h | h | h
  · exact h
  · exact (hlt.ne h.orbit_eq).elim
  · exact (hlt.ne h.1).elim

/-- The projection contradiction in 15.3.39 with its two remaining geometric
inputs exposed. The source model comparison must prove `hcompare`, and the
natural action must construct `actors`; this is not the assembled source
lemma. The residual splitting, innerness premise, simple quotient, swapping
map, normality, and equal projections are all derived here. -/
theorem componentOrbit_eq_of_centerless_comparison_of_planeActors [Finite G]
    {M Y Yplus L I S V V₁ V₂ : Subgroup G}
    (hLI : L ≤ I) (hSI : S ≤ I) (hL : IsComponent I (L.subgroupOf I))
    (hindex : (normalizer (L.subgroupOf I : Set I)).index ≤ 2)
    (hSY : S ≤ normalizer (Yplus : Set G))
    (hSV₂ : S ≤ normalizer (V₂ : Set G))
    (hYV₂ : Yplus ≤ normalizer (V₂ : Set G))
    (hVS : V ≤ S) (hV₂ne : V₂ ≠ ⊥)
    (h37 : Yplus ≤ componentOrbit L S ∨ L = componentOrbit L S)
    (h12 : primeRank 3 L = 1 →
      ComponentIntersection.InducesInnerOnTwoCoreQuotient Yplus L →
      Yplus = ComponentIntersection.intersectionResidual Yplus L ⊔
        ComponentIntersection.centralizerResidual Yplus L ∧
      3 ^ (Nat.card (componentFactor Yplus L)).factorization 3 = 3 ∧
      Nat.card (Yplus ⧸ pCore 2 Yplus) = 9)
    (hcompare : L < componentOrbit L S → center L = ⊥ ∧ primeRank 3 L = 1)
    (actors : PlaneActorPair M Y Yplus S V V₁ V₂) :
    L = componentOrbit L S := by
  classical
  by_contra hne
  have hlt : L < componentOrbit L S := lt_of_le_of_ne (le_componentOrbit L S) hne
  obtain ⟨hZ, hrank⟩ := hcompare hlt
  obtain ⟨s, hs, hsup, hswap⟩ := exists_swapping_conjugate hlt
    (component_orbit_card_le_two hLI hSI hindex)
  obtain ⟨hd, hc⟩ := relative_component_conjugate_disjoint_commuting hLI hL hZ
    (⟨s, hSI s.property⟩ : I) hs
  have hY : Yplus ≤ L ⊔ L.map (MulAut.conj (s : G)).toMonoidHom :=
    (h37.resolve_right hlt.ne).trans hsup.le
  obtain ⟨hsplit, hthree, hquot⟩ :=
    h12 hrank (inner_on_twoCoreQuotient_of_component_product hd hc hY)
  let : IsQuasisimple L := relative_component_quasisimple hLI hL
  have hcent : ComponentIntersection.centralizerResidual Yplus L = centralizingFactor Yplus L := by
    unfold ComponentIntersection.centralizerResidual centralizingFactor Chapter4.sectionCentralizerIn
    rw [sectionCentralizer_eq_centralizer_of_perfect twoCore_le_center_of_quasisimple]
  change Yplus = componentFactor Yplus L ⊔ ComponentIntersection.centralizerResidual Yplus L at hsplit
  rw [hcent] at hsplit
  have hfactor := conjugate_residual_factorization (s : G) hd hc hZ hY
    (hSY s.property) hsplit
  have hYfix : Yplus.map (MulAut.conj (s : G)).toMonoidHom = Yplus :=
    mem_normalizer_iff_map_conj_eq.mp (hSY s.property)
  have hswapX : ((componentFactor Yplus L).map (MulAut.conj (s : G)).toMonoidHom).map
      (MulAut.conj (s : G)).toMonoidHom = componentFactor Yplus L := by
    simp only [componentFactor_map, hYfix, hswap]
  have hdX := hd.mono (componentFactor_le Yplus L) (map_mono (componentFactor_le Yplus L))
  have hcX : componentFactor Yplus L ≤
      centralizer ((componentFactor Yplus L).map (MulAut.conj (s : G)).toMonoidHom : Set G) :=
    (componentFactor_le Yplus L).trans (hc.trans (centralizer_le (map_mono (componentFactor_le Yplus L))))
  obtain ⟨Q, hQn, hQ, hQs⟩ := exists_componentFactor_simple_quotient Yplus L hthree hquot
  let := hQn
  let := hQs
  obtain ⟨hleftn, hleftS⟩ := plane_left_actor_normal_invariant hYV₂ hSY hSV₂
  have hleftfix := mem_normalizer_iff_map_conj_eq.mp (hleftS s.property)
  have hrightfix := mem_normalizer_iff_map_conj_eq.mp (actors.right_invariant s.property)
  have hVfix := mem_normalizer_iff_map_conj_eq.mp (hSV₂ s.property)
  have hleftle := centralizingFactor_le_left Yplus V₂
  have hrightle := actors.right_le.trans inf_le_left
  have hVle := actors.plane_le (hVS.trans hSY)
  have hrightn := actors.right_normal
  have transport (N : Subgroup G) (hn : (N.subgroupOf Yplus).Normal) :
      (N.subgroupOf (componentFactor Yplus L ⊔
        (componentFactor Yplus L).map (MulAut.conj (s : G)).toMonoidHom)).Normal := by
    rw [← hfactor]
    exact hn
  exact no_commutator_plane_in_swapped_product
    (componentFactor Yplus L) ((componentFactor Yplus L).map (MulAut.conj (s : G)).toMonoidHom)
    (centralizingFactor Yplus V₂) actors.right V₂ hdX hcX (MulAut.conj (s : G)) hswapX
    Q hQ (componentFactor_isPPerfect Yplus L) (hleftle.trans hfactor.le)
    (hrightle.trans hfactor.le) (transport _ hleftn) (transport _ hrightn)
    (centralizingFactor_isPPerfect Yplus V₂) actors.right_perfect
    actors.nontrivial.1 actors.nontrivial.2 hleftfix hrightfix hVfix (hVle.trans hfactor.le) hV₂ne
    (centralizingFactor_le Yplus V₂) actors.plane_self

end CFSG.Quasithin.Chapter15.Section03.RankTwo
