module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoLineDual
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoSupportComponent
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoNaturalActor
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoPerfectLift

/-!
# The ordinary common-axis branch has a natural whole dual action

The original actor's strong dual plane is Sylow invariant because T
normalizes V. The checked small-plane component theorem therefore gives a
normal component fully moving the same dual section. Its native natural
marking fills the faithful actor. The literal canonical coordinates and
original actor are retained, and no quotient FF transfer is invoked.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The same canonical dual action in the rank-two, one-dimensional
marked-image branch is a whole natural binary linear action. -/
theorem PreparedChosenModule.decomposable_five_partner_two_line_dual_natural
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
          (ρ : Representation (ZMod 2) Mc W) (dF : BinaryConjugationSection Mc F D ρ),
          Nat.card (D ⊓ Z₁ : Subgroup G) = 2 →
          let σ := Representation.BinaryOffender.imageRepresentation ρ
          let A := actionSubgroup ρ (V.subgroupOf Mc)
          let P := dF.imageSpace E
          rank A = 2 → Module.finrank (ZMod 2) P = 1 →
          let N := normalClosure (V.subgroupOf Mc : Set Mc)
          let L := ((solvableResidual N).map N.subtype).map Mc.subtype
          normalClosure (A : Set (actionImage ρ)) = ⊤ ∧
            Group.IsPerfect L ∧ Mc ≤ normalizer (L : Set G) ∧
            L ≤ centralizer (D : Set G) ∧ ⁅F,L⁆ = F ∧ F ≤ L ∧
            actionSubgroup ρ (L.subgroupOf Mc) = ⊤ ∧
            ∃ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 5) ∧
              Nonempty (ChapterB.QuasisimpleSource.ActionEquiv σ.dual
                (ChapterB.QuasisimpleSource.linearNatural ChapterB.QuasisimpleSource.BinaryField.two n)) := by
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
  let P := dF.imageSpace E
  change rank A = 2 → Module.finrank (ZMod 2) P = 1 → _
  intro hr hdP
  let : Finite W := Finite.of_surjective (fun x : F => (dF.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp dF.onto)
  obtain ⟨_,hcost,hmoved,_,hstrong,hbest,hfaith,hcore,hnot⟩ :=
    ((h.decomposable_five_partner_two_line_dual_strong hG T hempty hM hmany hJ hu hfull
      c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ) ρ dF hline hr hdP
  have hdimW : 0 < Module.finrank (ZMod 2) W := by
    have hh := Submodule.finrank_le P
    rw [hdP] at hh
    omega
  let : Nontrivial W := (Module.finrank_pos_iff (R := ZMod 2) (M := W)).mp hdimW
  have hirr : IsIrreducible ρ := (h.decomposable_five_canonical_section_irreducible
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2 ρ dF
  let : IsIrreducible σ := imageRepresentation_isIrreducible ρ hirr
  let : IsIrreducible σ.dual := isIrreducible_dual
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  let cover : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple
      (Representation.BinaryOffender.actionImage ρ) :=
    ⟨Mc,(Representation.BinaryOffender.actionHom ρ).ker,hG.twoLocal_sqtk hMc.1.1,
      QuotientGroup.quotientKerEquivOfSurjective
        (Representation.BinaryOffender.actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective⟩
  let S : Sylow 2 (Representation.BinaryOffender.actionImage ρ) :=
    (T.subtype hTMc).mapSurjective ρ.asGroupHom.rangeRestrict_surjective
  have hSN : (S : Subgroup (Representation.BinaryOffender.actionImage ρ)) ≤ normalizer (A : Set _) := by
    rintro a ⟨t,ht,rfl⟩
    apply le_normalizer_map (Representation.BinaryOffender.actionHom ρ)
    apply mem_map_of_mem
    apply (mem_normalizer_iff).mpr
    intro x
    change (x : G) ∈ V ↔ (t : G) * (x : G) * (t : G)⁻¹ ∈ V
    exact h.normalized (hM.1.2 ht) x
  let X := ChapterB.QuasisimpleSource.moved σ.dual A
  have hdimX : Module.finrank (ZMod 2) X = 2 := hmoved
  have hSX : (S : Subgroup (Representation.BinaryOffender.actionImage ρ)) ≤
      subspaceStabilizer σ.dual X :=
    subspaceCommutator_invariant_normalizer σ.dual
      (le_subspaceStabilizer σ.dual ⊤ (by intros; trivial)) hSN
  obtain ⟨_,K,hK,hKA,hKN,_,hm,_,_⟩ :=
    DecomposableQuinticControl.whole_component_of_small_sylow_moved_span
      σ.dual hfaith hcore cover hbest hstrong hmoved S X le_rfl (by omega) hSX
  obtain ⟨n,hn,⟨e⟩⟩ := DecomposableQuinticControl.whole_component_natural_of_half_cost
    σ.dual hfaith hcore cover hK hbest hKA (Or.inl ⟨hr,hcost⟩) hmoved.le hm
  have hKtop := DecomposableQuinticControl.subgroup_eq_top_of_binary_natural σ.dual hfaith K n e
  let R := normalClosure (A : Set (actionImage ρ))
  have hR : R = ⊤ := top_unique (hKtop ▸ hKN)
  let : IsQuasisimple K := hK.2
  let : Group.IsPerfect (actionImage ρ) :=
    Group.IsPerfect.ofSurjective (f := K.subtype) (fun g => ⟨⟨g,hKtop ▸ mem_top g⟩,rfl⟩)
  let : Group.IsPerfect R := by rw [hR]; infer_instance
  obtain ⟨hperf,hnL,_,hLD,hFL,hFleL,himage⟩ :=
    (h.decomposable_five_canonical_perfect_lift hG T hempty hM hmany hJ hu hfull
      c d hd s π hp hs hdec hq hfive hVQ ρ dF).resolve_left hnot
  refine ⟨hR,hperf,hnL,hLD,hFL,hFleL,?_,n,hn,
    DecomposableQuinticControl.whole_actor_natural_of_subgroup σ.dual hfaith K n e⟩
  rw [himage]
  change (solvableResidual R).map R.subtype = ⊤
  rw [solvableResidual_eq_top,←MonoidHom.range_eq_map,range_subtype,hR]

end CFSG.Quasithin.Chapter15.Section01
