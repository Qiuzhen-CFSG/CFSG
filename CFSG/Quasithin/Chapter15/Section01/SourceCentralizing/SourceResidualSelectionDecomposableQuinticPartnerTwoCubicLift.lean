module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoPerfectActor
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoNaturalStabilizer
public import Theory.Representation.BinaryOffender.EquivariantStabilizer
public import Theory.Representation.BinaryOffender.IrreducibleOrbitAction

/-!
# A moving cubic seed-image stabilizer in the original perfect lift

The image of E on the actual canonical quotient has dimension two or three.
Its native natural stabilizer contains an element of exact order three that
moves this image. Surjectivity of the original perfect lift supplies a
literal ambient preimage centralizing D. No claim is made here that the
preimage normalizes E; correcting that lift requires the actual kernel rows.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original perfect lift contains a central-D lift of a moving cubic
stabilizer of the exact seed image in the supplied canonical coordinates. -/
theorem PreparedChosenModule.decomposable_five_partner_two_cubic_lift
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
          D ⊓ Z₁ = ⊥ →
          let N := normalClosure (V.subgroupOf Mc : Set Mc)
          let L := ((solvableResidual N).map N.subtype).map Mc.subtype
          ∃ g : Mc, (g : G) ∈ L ∧ (g : G) ∈ centralizer (D : Set G) ∧
            ρ (g^3) = 1 ∧ g ∈ subspaceStabilizer ρ (dF.imageSpace E) ∧
            ∃ w ∈ dF.imageSpace E, ρ g w ≠ w := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc : Set G)
  let F := conjugateSpanBy E C
  let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
  by_cases hVQ : V ≤ Mc.pCoreIn 2
  · exact Or.inl hVQ
  right
  intro W _ _ ρ dF hDZ
  let : Finite W := Finite.of_surjective (fun x : F => (dF.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp dF.onto)
  let σ := Representation.BinaryOffender.imageRepresentation ρ
  let P := dF.imageSpace E
  have hEF : E ≤ F := le_conjugateSpanBy E C
  have hZ₁F : Z₁ ≤ F := (show Z₁ ≤ E from inf_le_right).trans hEF
  have hdimP₁ : Module.finrank (ZMod 2) (dF.imageSpace Z₁) = 2 := by
    apply dF.imageSpace_finrank_of_index Z₁ hZ₁F 2
    have hh := relIndex_mul_card_of_le (show D ⊓ Z₁ ≤ Z₁ from inf_le_right)
    rw [inf_relIndex_right,hDZ,card_bot,s.thompson_card s.first,mul_one] at hh
    exact hh
  have hplanes := ((h.decomposable_five_partner_two_seed_intersections
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ).2.2.2 ρ dF
  have hdimP : Module.finrank (ZMod 2) P = 2 ∨ Module.finrank (ZMod 2) P = 3 := by
    rcases hplanes.2.2.2 with hh | hh | hh
    · exact Or.inr hh.2.1
    · exact Or.inl hh.2
    · have hbad := hh.2.2.1
      rw [hdimP₁] at hbad
      omega
  obtain ⟨_,_,_,_,_,n,_,⟨e⟩⟩ := ((h.decomposable_five_partner_two_canonical_natural
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ)
      ρ dF hDZ
  let P' := P.map e.linearEquiv.toLinearMap
  have hdimP' : Module.finrank (ZMod 2) P' = 2 ∨ Module.finrank (ZMod 2) P' = 3 := by
    simpa only [P',LinearEquiv.finrank_map_eq] using hdimP
  obtain ⟨a,ha,haP,w,hw,hwa⟩ :=
    DecomposableQuinticControl.exists_order_three_moving_subspace n P' hdimP'
  let a₀ := e.groupEquiv.symm a
  have ha₀ : a₀^3 = 1 := by
    apply e.groupEquiv.injective
    rw [map_pow,show e.groupEquiv a₀ = a from e.groupEquiv.apply_symm_apply a,map_one]
    exact ha ▸ pow_orderOf_eq_one a
  have ha₀P : a₀ ∈ subspaceStabilizer σ P := by
    apply (mem_subspaceStabilizer_equivariant σ (linearNatural BinaryField.two n)
      e.groupEquiv e.linearEquiv e.intertwines P a₀).mpr
    rw [show e.groupEquiv a₀ = a from e.groupEquiv.apply_symm_apply a]
    exact (subspace_map_eq_iff (linearNatural BinaryField.two n) P' a).mp haP
  obtain ⟨v,hv,hvw⟩ := hw
  have hva : σ a₀ v ≠ v := by
    intro he
    apply hwa
    have hh := e.intertwines a₀ v
    rw [he,show e.groupEquiv a₀ = a from e.groupEquiv.apply_symm_apply a] at hh
    rw [←hvw]
    exact hh.symm
  obtain ⟨_,_,_,_,hLC,_,_,himage⟩ :=
    ((h.decomposable_five_partner_two_perfect_actor hG T hempty hM hmany hJ hu hfull
      c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ) ρ dF hDZ
  have haImage : a₀ ∈ actionSubgroup ρ
      ((((solvableResidual (normalClosure (V.subgroupOf Mc : Set Mc))).map
        (normalClosure (V.subgroupOf Mc : Set Mc)).subtype).map Mc.subtype).subgroupOf Mc) :=
    himage.symm ▸ mem_top a₀
  obtain ⟨g,hg,hga⟩ := haImage
  refine ⟨g,hg,hLC hg,?_,?_,v,hv,?_⟩
  · change σ ((Representation.BinaryOffender.actionHom ρ) (g^3)) = 1
    rw [map_pow,hga,ha₀,map_one]
  · change (Representation.BinaryOffender.actionHom ρ) g ∈ subspaceStabilizer σ P
    rwa [hga]
  · change σ ((Representation.BinaryOffender.actionHom ρ) g) v ≠ v
    rwa [hga]

end CFSG.Quasithin.Chapter15.Section01
