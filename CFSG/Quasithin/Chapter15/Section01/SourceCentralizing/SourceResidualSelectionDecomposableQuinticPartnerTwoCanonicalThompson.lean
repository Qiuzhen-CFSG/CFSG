module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoIrreducible
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoMaximalSection
public import Theory.GroupTheory.ElementaryThompsonNormalizerControl
public import Theory.Representation.BinaryConjugationSection.ActionKernel

/-!
# Thompson movement on the literal canonical quintic quotient

If J(T) acted trivially on F/D, its normal action kernel and Thompson
Frattini would make E join D invariant under Mc. The original invariant
subgroup criterion puts that join either in D or equal to F. In the first
case normality of D absorbs the whole E-span F; in the second case V
centralizes F since it centralizes both E and D. Both contradict the
actual noncore branch. This keeps the canonical denominator and yields
movement for every specified F/D coordinate action, without FF inheritance.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
universe u v
variable {G : Type u} [Group G] [Finite G]

/-- The original Thompson subgroup moves the canonical section, in its
literal group denominator and every chosen conjugation coordinate action. -/
theorem PreparedChosenModule.decomposable_five_canonical_thompson_movement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      ¬V≤Mc.pCoreIn 2 →
      let E := thompsonFixed T V
      let C := centralizer (localModule T Mc:Set G)
      let F := conjugateSpanBy E C
      let D := (((F⊓centralizer (V:Set G)).subgroupOf Mc).normalCore).map Mc.subtype
      let J := elementaryAbelianMaxJ (T:Subgroup G)
      (¬⁅J,F⁆≤D) ∧
        ∀ {W:Type v} [AddCommGroup W] [Module (ZMod 2) W]
          (ρ:Representation (ZMod 2) Mc W),
          BinaryConjugationSection Mc F D ρ → ¬J.subgroupOf Mc≤ρ.ker := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hVQ
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc:Set G)
  let F := conjugateSpanBy E C
  let D := (((F⊓centralizer (V:Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  let J := elementaryAbelianMaxJ (T:Subgroup G)
  rcases h.decomposable_five_core_or_maximal_reduced_section
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive with
    hcore | ⟨_,hDF,hDC,hnD,_,hHF,_,_,hHC,_⟩
  · exact (hVQ hcore).elim
  have hFC : ¬F≤centralizer (V:Set G) := fun hc=>hHC (hHF.trans hc)
  have hnF : Mc≤normalizer (F:Set G) :=
    (h.decomposable_five_partner_fixed_envelope hG T hempty hM hmany hJ hu
      hfull c d hd s π hp hs hdec hq hfive).2.2.2.2.2
  have hIE : M⊓Mc≤normalizer (E:Set G) :=
    (h.decomposable_five_partner_control hG T hempty hM hmany hJ hu
      hfull c d hd s π hp hs hdec hq hfive).2.1
  have hMc : Mc∈maximalTwoLocalOvergroups (centralizer (centralInvolutions T:Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T:Subgroup G)≤Mc := by
    intro t ht
    exact hMc.2 (fun z hz=>(centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hJMc : J≤Mc := (sSup_le fun _ hA=>hA.1).trans hTMc
  have hEF : E≤F := le_conjugateSpanBy E C
  have hmove : ¬⁅J,F⁆≤D := by
    intro htrivial
    let K := commutatorPreimage Mc F D
    have hnK : Mc≤normalizer (K:Set G) :=
      commutatorPreimage_normalized Mc F D Mc hnD Mc.le_normalizer hnF hnD
    have hKF : ⁅K,F⁆≤D := commutator_commutatorPreimage_le Mc F D hnD
    have hKN : K≤normalizer (E⊔D:Subgroup G) :=
      le_normalizer_iff_commutator_le_right.mpr
        (((commutator_mono le_rfl (sup_le hEF hDF.le)).trans hKF).trans le_sup_right)
    let S := T.subtype hTMc
    let K₀ := K.subgroupOf Mc
    let : K₀.Normal := normal_subgroupOf_of_le_normalizer hnK
    have hm : (elementaryAbelianMaxJ (S:Subgroup Mc)).map Mc.subtype=J := by
      rw [←elementaryAbelianMaxJ_map_injective Mc.subtype Mc.subtype_injective]
      exact congrArg elementaryAbelianMaxJ (map_subgroupOf_eq_of_le hTMc)
    have hJK : J≤K := le_commutatorPreimage hJMc htrivial
    have hJK₀ : elementaryAbelianMaxJ (S:Subgroup Mc)≤K₀ := by
      intro j hj
      exact hJK (hm ▸ mem_map_of_mem Mc.subtype hj)
    have hgen := elementaryAbelianMaxJ_frattini_of_le_normal S K₀ hJK₀
    have hbound : normalizer (elementaryAbelianMaxJ (S:Subgroup Mc):Set Mc)⊔K₀≤
        (normalizer (E⊔D:Subgroup G)).subgroupOf Mc := by
      apply sup_le
      · intro n hn
        have hnJ : (n:G)∈normalizer (J:Set G) := by
          rw [←hm]
          exact le_normalizer_map Mc.subtype (mem_map_of_mem Mc.subtype hn)
        have hnM : (n:G)∈M :=
          (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1 hnJ
        exact normalizer_inf_normalizer_le_normalizer_sup E D
          ⟨hIE ⟨hnM,n.property⟩,hnD n.property⟩
      · intro n hn
        exact hKN hn
    rw [hgen] at hbound
    have hnED : Mc≤normalizer (E⊔D:Subgroup G) := by
      intro n hn
      exact hbound (show (⟨n,hn⟩:Mc)∈⊤ from mem_top _)
    rcases (PreparedChosenModule.decomposable_five_canonical_section_irreducible.{u,v}
      hG T hempty hM hmany hJ hu h hfull c d hd s π hp hs hdec hq hfive).1
      (E⊔D) (sup_le hEF hDF.le) hnED with htop | hsmall
    · apply hFC
      change E⊔D=F at htop
      rw [←htop]
      exact sup_le (inf_le_left.trans V.le_centralizer) hDC
    · have hED : E≤D := le_sup_left.trans hsmall
      have hFD : F≤D := conjugateSpanBy_le hED
        ((localModule_centralizer_le_partner T Mc hu).trans hnD)
      exact hDF.not_ge hFD
  refine ⟨hmove,?_⟩
  intro W _ _ ρ dF hk
  apply hmove
  apply commutator_le.mpr
  intro j hj f hf
  exact (dF.action_mem_ker_iff (⟨j,hJMc hj⟩:Mc)).mp (hk hj) f hf

end CFSG.Quasithin.Chapter15.Section01
