module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoSupportComponent
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoNaturalActor

/-!
# Natural coordinates for the full actual canonical quintic actor

The original support component acts naturally on the whole canonical F/D.
Over the binary field this component fills the whole faithful linear actor.
Thus the marked natural coordinates describe the exact original Mc-image,
retaining the first original support offender and its literal moved plane.
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

/-- Disjointness from the marked planes identifies the entire original
canonical action as a natural binary linear action, on the supplied section. -/
theorem PreparedChosenModule.decomposable_five_partner_two_canonical_natural
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
          let A₁ := actionSubgroup ρ
            ((plane V (c.ambientFactor d s.first).space).subgroupOf Mc)
          let σ := Representation.BinaryOffender.imageRepresentation ρ
          rank A₁ = 2 ∧ fixedCodim σ A₁ = 1 ∧
            IsMinimalBestOffender σ A₁ ∧ IsStrongOffender σ A₁ ∧
            subspaceCommutator σ ⊤ A₁ = dF.imageSpace Z₁ ∧
            ∃ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 5) ∧
              Nonempty (ActionEquiv σ (linearNatural BinaryField.two n)) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  rcases h.decomposable_five_partner_two_support_component
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU with
    hcore | hcomponent
  · exact Or.inl hcore
  right
  intro W _ _ ρ dF hDZ
  obtain ⟨hr,hcost,hmin,hstrong,hm,_,K,_,_,_,_,_,_,_,n,hn,⟨e⟩⟩ := hcomponent ρ dF hDZ
  exact ⟨hr,hcost,hmin,hstrong,hm,n,hn,
    DecomposableQuinticControl.whole_actor_natural_of_subgroup
      (Representation.BinaryOffender.imageRepresentation ρ)
      (imageRepresentation_injective ρ) K n e⟩

end CFSG.Quasithin.Chapter15.Section01
