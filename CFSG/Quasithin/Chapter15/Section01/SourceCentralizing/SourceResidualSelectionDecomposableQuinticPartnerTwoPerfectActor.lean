module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoCanonicalNatural
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoPerfectLift

/-!
# Surjectivity of the original perfect lift on the canonical natural actor

The component selected by an original support fills the faithful binary
linear actor and lies in the normal closure of that support. Thus the
normal closure of the full original V-image is the entire perfect actor.
The literal solvable residual of the original normal closure in Mc maps
onto this whole actor, with its original central kernel unchanged.
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

/-- The original perfect lift surjects onto the full supplied canonical
natural action, retaining the exact denominator and the original residual. -/
theorem PreparedChosenModule.decomposable_five_partner_two_perfect_actor
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
          D ⊓ Z₁ = ⊥ →
          let A := actionSubgroup ρ (V.subgroupOf Mc)
          let N := normalClosure (V.subgroupOf Mc : Set Mc)
          let L := ((solvableResidual N).map N.subtype).map Mc.subtype
          normalClosure (A : Set (Representation.BinaryOffender.actionImage ρ)) = ⊤ ∧
          Group.IsPerfect L ∧ Mc ≤ normalizer (L : Set G) ∧
          L ≤ conjugateSpanBy V Mc ∧ L ≤ centralizer (D : Set G) ∧
          ⁅F,L⁆ = F ∧ F ≤ L ∧ actionSubgroup ρ (L.subgroupOf Mc) = ⊤ := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc : Set G)
  let F := conjugateSpanBy E C
  let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  by_cases hVQ : V ≤ Mc.pCoreIn 2
  · exact Or.inl hVQ
  right
  intro W _ _ ρ dF hDZ
  let A := actionSubgroup ρ (V.subgroupOf Mc)
  let A₁ := actionSubgroup ρ
    ((plane V (c.ambientFactor d s.first).space).subgroupOf Mc)
  let R := normalClosure (A : Set (Representation.BinaryOffender.actionImage ρ))
  obtain ⟨_,_,_,_,_,_,K,hK,_,hKN,_,_,_,_,n,_,⟨e⟩⟩ :=
    ((h.decomposable_five_partner_two_support_component
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ)
        ρ dF hDZ
  have hKtop : K = ⊤ := DecomposableQuinticControl.subgroup_eq_top_of_binary_natural
    (Representation.BinaryOffender.imageRepresentation ρ)
    (imageRepresentation_injective ρ) K n e
  have hA₁A : A₁ ≤ A := map_mono (subgroupOf_mono Mc (plane_le _))
  have hR : R = ⊤ := top_unique (hKtop ▸ hKN.trans (normalClosure_mono hA₁A))
  let : IsQuasisimple K := hK.2
  let : Group.IsPerfect (Representation.BinaryOffender.actionImage ρ) :=
    Group.IsPerfect.ofSurjective (f := K.subtype) (fun g => ⟨⟨g,hKtop ▸ mem_top g⟩,rfl⟩)
  let : Group.IsPerfect R := by rw [hR]; infer_instance
  have hnot := (((h.decomposable_five_partner_two_disjoint_strong
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ)
      ρ dF hDZ).2.2
  obtain ⟨hperf,hn,hspan,hcentral,hm,hFL,himage⟩ :=
    (h.decomposable_five_canonical_perfect_lift hG T hempty hM hmany hJ hu hfull
      c d hd s π hp hs hdec hq hfive hVQ ρ dF).resolve_left hnot
  refine ⟨hR,hperf,hn,hspan,hcentral,hm,hFL,?_⟩
  rw [himage]
  change (solvableResidual R).map R.subtype = ⊤
  rw [solvableResidual_eq_top,←MonoidHom.range_eq_map,range_subtype,hR]

end CFSG.Quasithin.Chapter15.Section01
