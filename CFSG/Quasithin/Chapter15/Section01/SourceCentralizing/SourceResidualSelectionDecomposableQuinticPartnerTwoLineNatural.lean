module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoLineCosts
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoSupportComponent
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoNaturalActor
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoPerfectLift

/-!
# Natural recognition in the original two-line strong branch

The rank-two, codimension-one original offender moves exactly the image
of E. That plane is Sylow invariant, so the component selected by the
original actor is normal and moves the whole irreducible section. Binary
natural recognition fills the faithful actor. Its inclusion in the original
actor normal closure makes the literal perfect lift surjective as well.
The two equal-cost alternatives retain their original section and indices.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual strong middle row of the original two-line alternatives
has a whole natural actor and a surjective original perfect lift. -/
theorem PreparedChosenModule.decomposable_five_partner_two_line_natural_or_equal_cost
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
      let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
      let K := commutatorPreimage Mc F D
      V ≤ Mc.pCoreIn 2 ∨
        ∀ {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
          (ρ : Representation (ZMod 2) Mc W) (dF : BinaryConjugationSection Mc F D ρ),
          Nat.card (D ⊓ Z₁ : Subgroup G) = 2 →
          let σ := Representation.BinaryOffender.imageRepresentation ρ
          let A := actionSubgroup ρ (V.subgroupOf Mc)
          let P := dF.imageSpace E
          IsOffender σ A ∧ IsQuadratic σ A ∧ P = subspaceCommutator σ ⊤ A ∧
            Module.finrank (ZMod 2) (dF.imageSpace Z₁) = 1 ∧
            Module.finrank (ZMod 2) (dF.imageSpace Z₂) = 1 ∧
            (Module.finrank (ZMod 2) P = 1 ∨ Module.finrank (ZMod 2) P = 2) ∧
            Nat.card A = K.relIndex V ∧
            ((rank A = 1 ∧ fixedCodim σ A = 1 ∧ Module.finrank (ZMod 2) P = 1 ∧
                K.relIndex V = 2 ∧ Nat.card (K ⊓ V : Subgroup G) = 128 ∧
                IsMinimalBestOffender σ A) ∨
              (rank A = 2 ∧ fixedCodim σ A = 1 ∧ Module.finrank (ZMod 2) P = 2 ∧
                K.relIndex V = 4 ∧ Nat.card (K ⊓ V : Subgroup G) = 64 ∧
                IsStrongOffender σ A ∧ IsMinimalBestOffender σ A ∧
                ∃ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 5) ∧
                  Nonempty (ActionEquiv σ (linearNatural BinaryField.two n)) ∧
                  normalClosure (A : Set (Representation.BinaryOffender.actionImage ρ)) = ⊤ ∧
                  let N := normalClosure (V.subgroupOf Mc : Set Mc)
                  let L := ((solvableResidual N).map N.subtype).map Mc.subtype
                  Group.IsPerfect L ∧ Mc ≤ normalizer (L : Set G) ∧
                  L ≤ conjugateSpanBy V Mc ∧ L ≤ centralizer (D : Set G) ∧
                  ⁅F,L⁆ = F ∧ F ≤ L ∧ actionSubgroup ρ (L.subgroupOf Mc) = ⊤) ∨
              (rank A = 2 ∧ fixedCodim σ A = 2 ∧ K.relIndex V = 4 ∧
                Nat.card (K ⊓ V : Subgroup G) = 64 ∧ ¬IsStrongOffender σ A)) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc : Set G)
  let F := conjugateSpanBy E C
  let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  let K := commutatorPreimage Mc F D
  by_cases hVQ : V ≤ Mc.pCoreIn 2
  · exact Or.inl hVQ
  right
  intro W _ _ ρ dF hline
  let : Finite W := Finite.of_surjective (fun x : F => (dF.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp dF.onto)
  let σ := Representation.BinaryOffender.imageRepresentation ρ
  let A := actionSubgroup ρ (V.subgroupOf Mc)
  let P := dF.imageSpace E
  obtain ⟨hoff,hquad,himage,hd₁,hd₂,hdP,hcard,hcases⟩ :=
    ((h.decomposable_five_partner_two_line_costs
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ)
        ρ dF hline
  refine ⟨hoff,hquad,himage,hd₁,hd₂,hdP,hcard,?_⟩
  rcases hcases with hequal | hstrong | hequal
  · exact Or.inl hequal
  · right
    left
    obtain ⟨hr,hcost,hdimP,hidx,hker,hstrong,hmin⟩ := hstrong
    refine ⟨hr,hcost,hdimP,hidx,hker,hstrong,hmin,?_⟩
    change P = subspaceCommutator σ ⊤ A at himage
    change Module.finrank (ZMod 2) P = 2 at hdimP
    have hdimA : Module.finrank (ZMod 2) (moved σ A) = 2 := by
      change Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ A) = 2
      rw [←himage]
      exact hdimP
    have hdimW : 0 < Module.finrank (ZMod 2) W := by
      have hh := Submodule.finrank_le P
      omega
    let : Nontrivial W := (Module.finrank_pos_iff (R := ZMod 2) (M := W)).mp hdimW
    have hirr : IsIrreducible ρ := (h.decomposable_five_canonical_section_irreducible
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2 ρ dF
    let : IsIrreducible σ := imageRepresentation_isIrreducible ρ hirr
    have hcore : pCore 2 (Representation.BinaryOffender.actionImage ρ) = ⊥ :=
      actionImage_twoCore_eq_bot ρ hirr
    have hEF : E ≤ F := le_conjugateSpanBy E C
    obtain ⟨_,hMN,_⟩ := h.decomposable_five_partner_control
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    have hTMc : (T : Subgroup G) ≤ Mc := by
      intro t ht
      exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
    have hTN : (T : Subgroup G) ≤ normalizer (E : Set G) :=
      (le_inf hM.1.2 hTMc).trans hMN
    let cover : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple
        (Representation.BinaryOffender.actionImage ρ) :=
      ⟨Mc,(Representation.BinaryOffender.actionHom ρ).ker,hG.twoLocal_sqtk hMc.1.1,
        QuotientGroup.quotientKerEquivOfSurjective
          (Representation.BinaryOffender.actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective⟩
    let S : Sylow 2 (Representation.BinaryOffender.actionImage ρ) :=
      (T.subtype hTMc).mapSurjective ρ.asGroupHom.rangeRestrict_surjective
    have hSP : (S : Subgroup (Representation.BinaryOffender.actionImage ρ)) ≤
        subspaceStabilizer σ P := by
      apply le_subspaceStabilizer
      rintro a ⟨t,ht,rfl⟩ v hv
      change ρ t v ∈ dF.imageSpace E
      have hc : E.conjBy (t : G) = E := mem_normalizer_iff_map_conj_eq.mp (hTN ht)
      have hm := dF.imageSpace_conjBy E hEF t
      rw [hc] at hm
      rw [hm]
      exact Submodule.mem_map_of_mem (f := ρ t) hv
    have hAP : moved σ A ≤ P := himage.ge
    obtain ⟨_,J,hJc,hJA,hJN,_,hm,_,_⟩ :=
      DecomposableQuinticControl.whole_component_of_small_sylow_moved_span
        σ (imageRepresentation_injective ρ) hcore cover hmin hstrong hdimA
        S P hAP (by omega) hSP
    obtain ⟨n,hn,⟨e⟩⟩ := DecomposableQuinticControl.whole_component_natural_of_half_cost
      σ (imageRepresentation_injective ρ) hcore cover hJc hmin hJA
      (Or.inl ⟨hr,hcost⟩) hdimA.le hm
    have hJtop : J = ⊤ := DecomposableQuinticControl.subgroup_eq_top_of_binary_natural
      σ (imageRepresentation_injective ρ) J n e
    have hnatural := DecomposableQuinticControl.whole_actor_natural_of_subgroup
      σ (imageRepresentation_injective ρ) J n e
    let R := normalClosure (A : Set (Representation.BinaryOffender.actionImage ρ))
    have hR : R = ⊤ := top_unique (hJtop ▸ hJN)
    let : IsQuasisimple J := hJc.2
    let : Group.IsPerfect (Representation.BinaryOffender.actionImage ρ) :=
      Group.IsPerfect.ofSurjective (f := J.subtype) (fun g => ⟨⟨g,hJtop ▸ mem_top g⟩,rfl⟩)
    let : Group.IsPerfect R := by rw [hR]; infer_instance
    let : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr (by
      intro hz
      exact hJc.isCComponent.ne_bot (bot_unique (hJN.trans_eq hz)))
    have hnot : ¬Group.IsSolvable R := Group.IsPerfect.not_isSolvable R
    obtain ⟨hperf,hnL,hspan,hcentral,hmove,hFL,himageL⟩ :=
      (h.decomposable_five_canonical_perfect_lift hG T hempty hM hmany hJ hu hfull
        c d hd s π hp hs hdec hq hfive hVQ ρ dF).resolve_left hnot
    refine ⟨n,hn,hnatural,hR,hperf,hnL,hspan,hcentral,hmove,hFL,?_⟩
    rw [himageL]
    change (solvableResidual R).map R.subtype = ⊤
    rw [solvableResidual_eq_top,←MonoidHom.range_eq_map,range_subtype,hR]
  · exact Or.inr (Or.inr hequal)

end CFSG.Quasithin.Chapter15.Section01
