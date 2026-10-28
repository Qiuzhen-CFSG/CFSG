module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoLineCosts
public import CFSG.Quasithin.ChapterG.Section06.IrreducibleCentral
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# The original rank-one line actor is a central G.6.4 actor

The original V-image is normal of order two in the image of the original
Sylow subgroup. Its unique involution is therefore Sylow-central. The
canonical irreducible faithful action supplies the actual orbit generation
and trivial two-core needed by the proved universal G.6.4. Its central clause
classifies this same action and makes the original V-image normally generate.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
universe u
variable {G : Type u} [Group G] [Finite G]

/-- G.6.4 classifies the same canonical action in the original rank-one
line branch, and its original V-image normally generates the whole actor. -/
theorem PreparedChosenModule.decomposable_five_partner_two_line_rank_one_central_model
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
      Nat.card (localModule T Mc) = 2 →
      let E := thompsonFixed T V
      let C := centralizer (localModule T Mc : Set G)
      let F := conjugateSpanBy E C
      let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
      let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
      V ≤ Mc.pCoreIn 2 ∨
        ∀ {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
          (ρ : Representation (ZMod 2) Mc W) (_dF : BinaryConjugationSection Mc F D ρ),
          Nat.card (D ⊓ Z₁ : Subgroup G) = 2 →
          let σ := Representation.BinaryOffender.imageRepresentation ρ
          let A := actionSubgroup ρ (V.subgroupOf Mc)
          rank A = 1 →
          normalClosure (A : Set (actionImage ρ)) = ⊤ ∧
            ChapterG.Section06.CentralModel σ := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc : Set G)
  let F := conjugateSpanBy E C
  let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  by_cases hVQ : V ≤ Mc.pCoreIn 2
  · exact Or.inl hVQ
  right
  intro W _ _ ρ dF hline
  let σ := Representation.BinaryOffender.imageRepresentation ρ
  let A := actionSubgroup ρ (V.subgroupOf Mc)
  change rank A = 1 → _
  intro hr
  let : Finite W := Finite.of_surjective (fun x : F => (dF.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp dF.onto)
  obtain ⟨hoff,_,_,_,_,_,_,_⟩ :=
    ((h.decomposable_five_partner_two_line_costs hG T hempty hM hmany hJ hu hfull
      c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ) ρ dF hline
  change IsOffender σ A at hoff
  have hfaith : Function.Injective σ := imageRepresentation_injective ρ
  have hcard : Nat.card A = 2 := by rw [hoff.1.card_eq_two_pow_rank,hr]; rfl
  have hcost : fixedCodim σ A = 1 := by
    have hpos := fixedCodim_pos_of_faithful σ hfaith hoff.1.1
    have hle := hoff.2
    omega
  let : IsElementaryAbelian 2 A := hoff.1.2
  let : IsCyclic A := isCyclic_of_prime_card hcard
  obtain ⟨t,ht⟩ := A.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have htA : t ∈ A := ht ▸ mem_zpowers t
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t htA
  have htne : t ≠ 1 := by
    intro he
    have hh := ht
    rw [he,zpowers_one_eq_bot] at hh
    exact hoff.1.1 hh.symm
  have htr : Module.finrank (ZMod 2) (LinearMap.range (σ t - LinearMap.id)) = 1 := by
    rw [←fixedCodim_zpowers_eq_displacement_rank,ht]
    exact hcost
  let : Nontrivial W := (Module.finrank_pos_iff (R := ZMod 2) (M := W)).mp
    (lt_of_lt_of_le (by rw [htr]; decide)
      (Submodule.finrank_le (LinearMap.range (σ t - LinearMap.id))))
  have hirr : IsIrreducible ρ := (h.decomposable_five_canonical_section_irreducible
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2 ρ dF
  let : IsIrreducible σ := imageRepresentation_isIrreducible ρ hirr
  have hcore : pCore 2 (actionImage ρ) = ⊥ := by
    apply le_bot_iff.mp
    exact (normal_p_subgroup_le_ker σ (pCore 2 (actionImage ρ))
      (pCore_isPGroup (p := 2))).trans (σ.ker_eq_bot_iff.mpr hfaith).le
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hVT : V ≤ (T : Subgroup G) := by
    let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer h.normalized
    let := IsElementaryAbelian.subgroupOf h.le_selected (p := 2)
    have hh := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal
      (T.subtype hM.1.2)
    simpa only [map_subgroupOf_eq_of_le h.le_selected,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hM.1.2] using map_mono (f := M.subtype) hh
  let q := Representation.BinaryOffender.actionHom ρ
  have hqonto : Function.Surjective q := ρ.asGroupHom.rangeRestrict_surjective
  let S : Sylow 2 (actionImage ρ) := (T.subtype hTMc).mapSurjective hqonto
  have hAS : A ≤ (S : Subgroup (actionImage ρ)) := by
    apply map_mono
    intro x hx
    exact hVT hx
  have hSN : (S : Subgroup (actionImage ρ)) ≤ normalizer (A : Set _) := by
    rintro a ⟨x,hx,rfl⟩
    apply le_normalizer_map q
    apply mem_map_of_mem
    apply mem_normalizer_iff.mpr
    intro y
    change (y : G) ∈ V ↔ (x : G) * (y : G) * (x : G)⁻¹ ∈ V
    exact h.normalized (hM.1.2 hx) y
  have htS : t ∈ (center S).map (S : Subgroup (actionImage ρ)).subtype := by
    refine ⟨⟨t,hAS htA⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact ((normalizer_le_centralizer_of_card_two A hcard) (hSN x.property) t htA).symm
  have hG64 := ChapterG.Section06.hypotheses_of_irreducible σ q
    (hG.twoLocal_sqtk hMc.1.1) hqonto hcore hfaith t ht2 htne (by
      change Module.finrank (ZMod 2) (LinearMap.range (σ t - LinearMap.id)) ≤ 2
      omega)
  obtain ⟨hgen,hmodel⟩ := (ChapterG.Section06.lemma_G_6_4 hG64 htr).2 S htS
  refine ⟨?_,hmodel⟩
  apply top_unique
  rw [←hgen]
  apply normalClosure_mono
  intro x hx
  have he : x = t := Set.mem_singleton_iff.mp hx
  subst x
  exact htA

end CFSG.Quasithin.Chapter15.Section01
