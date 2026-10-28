module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.MarkedOrdinarySource
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.SourceRanks
public import CFSG.Quasithin.Chapter1.SourceInputs.KnownSimple
public import Theory.GroupTheory.SimpleSectionSolvableReduction
public import Theory.SpecificGroups.Alternating.TwoThreeCycles

/-!
# Excluding the exchanged A₆ component orbit

Pass an ordinary component to the ambient two-core quotient. If it is
nonnormal, the proved A.3.6 source catalogue and commuting-component rank
argument make that image simple with three-rank at most one. Its original
odd-then-two-core quotient factors through this image. When that quotient
is A₆, the resulting surjection between simple groups is an isomorphism,
contradicting the two independent three-cycles in A₆.

Apply this normality result to the actual exchanged component in the original
marked pumpup. The original A₆ has trivial odd-then-two core, so the specified
quotient equivalence excludes the exchanged branch without a cover-lifting
premise or a new containing-model assumption.

Source: Aschbacher–Smith 2.5.19, pp.560–561, I.3.2, pp.414–415,
and A.3.8(3), pp.45–46, combined manuscript of 1 March 2004.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6
open ComponentRefinement ComponentSelection
open ChapterA.SQTKStructure ChapterA.SQTKStructure.NonnormalOuterSource

private theorem twoCore_le_oddTwoCore (D : Type*) [Group D] :
    pCore 2 D ≤ oddTwoCore D := by
  let q := QuotientGroup.mk' (pPrimeCore 2 D)
  change pCore 2 D ≤ (pCore 2 (D ⧸ pPrimeCore 2 D)).comap q
  apply map_le_iff_le_comap.mp
  exact le_sSup ⟨Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _),
    pCore_isPGroup.map q⟩

/-- An ordinary component whose original source quotient is A₆ is normal
in every actual known-simple SQTK overgroup. -/
theorem component_normal_of_a6_oddTwoCore_quotient
    {E : Type*} [Group E] [Finite E]
    (hE : IsSQTK KnownSimple.IsKnownSimple E) (J : Subgroup E)
    (hJ : IsComponent E J)
    (eJ : (J ⧸ oddTwoCore J) ≃* alternatingGroup (Fin 6)) : J.Normal := by
  by_contra hn
  let : Group.IsNilpotent (pCore 2 E) := pCore_isNilpotent
  let q := QuotientGroup.mk' (pCore 2 E)
  let C := J.map q
  have hc : C.IsCComponent := hJ.isCComponent.map_quotient (pCore 2 E)
  have hnc : ¬ C.Normal := fun h => hn (cComponent_normal_of_quotient_normal hJ.isCComponent _ h)
  have hC : IsComponent (E ⧸ pCore 2 E) C := by
    rcases hJ.map_surjective q (QuotientGroup.mk'_surjective _) with h | h
    · exact (hc.ne_bot h).elim
    · exact h
  let : IsQuasisimple C := hC.2
  have hQ := ChapterI.RankTwoSource.sqtk_twoCore_quotient hE
  have hf : fittingSubgroup C ≤ center C :=
    (le_solvableRadical _ inferInstance inferInstance).trans IsQuasisimple.solvableRadical_le_center
  have hm := (ordinary_model_of_central_fitting
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hQ C hc hf).2
  let : IsSimpleGroup C := FourModels.simple_of_model
    (hQ.stronglyQuasithin 3 (by decide) (by decide))
    (pCore_quotient_pCore_eq_bot 2) C hC hnc hm
  have hr : primeRank 3 C ≤ 1 := FourModels.odd_ranks_of_model hQ.stronglyQuasithin
    (pCore_quotient_pCore_eq_bot 2) C hC hnc hm 3 (by decide) (by decide)
  let f : (J ⧸ pCore 2 J) →* (J ⧸ oddTwoCore J) :=
    QuotientGroup.lift (pCore 2 J) (QuotientGroup.mk' (oddTwoCore J))
      (by intro x hx; exact (QuotientGroup.eq_one_iff x).mpr (twoCore_le_oddTwoCore J hx))
  have hsur : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (oddTwoCore J) y
    exact ⟨QuotientGroup.mk' (pCore 2 J) x, rfl⟩
  let e : (J ⧸ pCore 2 J) ≃* C := cComponentTwoCoreQuotientEquiv hJ.isCComponent
  let g : C →* alternatingGroup (Fin 6) := eJ.toMonoidHom.comp (f.comp e.symm.toMonoidHom)
  have hg : Function.Surjective g := eJ.surjective.comp (hsur.comp e.symm.surjective)
  let d : C ≃* alternatingGroup (Fin 6) := MulEquiv.ofBijective g
    ⟨g.injective_of_surjective_of_simple hg, hg⟩
  rw [primeRank_equiv 3 d] at hr
  have hl := alternatingGroup.TwoThreeCycles.two_le_primeRank (n := 6) (by decide)
  omega

private theorem simple_oddTwoCore_eq_bot {D : Type*} [Group D] [Finite D]
    [IsSimpleGroup D] [Group.IsPerfect D] : oddTwoCore D = ⊥ := by
  let : Group.IsSolvable (pPrimeCore 2 D) :=
    odd_order_theorem _ (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  let : Group.IsSolvable (oddTwoCore D) := oddTwoCore_isSolvable
  rcases (inferInstance : (oddTwoCore D).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · let : Group.IsSolvable (⊤ : Subgroup D) := h ▸ inferInstanceAs (Group.IsSolvable (oddTwoCore D))
    exact (Group.IsPerfect.not_isSolvable D
      (Group.isSolvable_of_surjective (f := (topEquiv : (⊤ : Subgroup D) ≃* D).toMonoidHom)
        topEquiv.surjective)).elim

/-- The actual marked A₆ source pumpup has an invariant ordinary component.
The exchanged orbit is excluded on its literal odd-then-two-core quotient. -/
theorem source_a6_marked_pumpup_invariant {G : Type*} [Group G] [Finite G]
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* alternatingGroup (Fin 6))
    (t i : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hi : orderOf i = 2) (hiS : i ∈ (S : Subgroup H).map H.subtype)
    (hiK : i ∈ centralizer (K : Set G))
    (hbad : ¬ IsComponentIn K (centralizer ({i} : Set G))) :
    ∃ _htI : t ∈ centralizer ({i} : Set G),
      let Gi := centralizer ({i} : Set G)
      let D := K.subgroupOf Gi
      let X := componentOrbit D (oddELayer Gi)
      IsComponent Gi X ∧ ∃ a : MulAut X, orderOf a = 2 ∧
        (∀ x : X, ((a x : Gi) : G) = t * ((x : Gi) : G) * t⁻¹) ∧
        IsComponentIn (D.subgroupOf X) a.fixedSubgroup ∧
        Nonempty (K ≃* ((D.subgroupOf X).subgroupOf a.fixedSubgroup)) := by
  obtain ⟨htI, hcases⟩ := source_marked_ordinary_pumpup
    c hG hempty hgen hb hstar t i ht htC htZ hi hiS hiK hbad
  refine ⟨htI, ?_⟩
  rcases hcases with h | ⟨J, hJ, hne, _, ⟨e⟩⟩
  · exact h
  · let : IsSimpleGroup K := (MathieuSourceSetup.small_source_structure c hG hempty hgen hb).2.1
    let : IsQuasisimple K := (show IsComponentIn K H from ⟨c.component_le, c.component⟩).quasisimple
    let f : (K ⧸ oddTwoCore K) ≃* alternatingGroup (Fin 6) :=
      (QuotientGroup.quotientMulEquivOfEq simple_oddTwoCore_eq_bot).trans
        (QuotientGroup.quotientBot.trans eK)
    have hn := component_normal_of_a6_oddTwoCore_quotient
      (hG.involution_centralizer_sqtk hi) J hJ (e.trans f)
    exact (hne ((normal_iff_map_conj_eq.mp hn ⟨t, htI⟩).symm)).elim

end CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6
