module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoMovingSpan
public import Theory.Representation.BinaryConjugationSection.Irreducible

/-!
# The canonical original quintic section is irreducible

Every proper partner-invariant subgroup of F centralizes the original V,
so it lies in the literal normal core D of F intersect C_G(V). Thus all
proper invariant subgroups lie in D. The exact conjugation-section
coordinates transfer this original subgroup statement to irreducibility
of any nonzero F/D action. No faithful-quotient offender transfer is used.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The literal maximal centralizing denominator contains every proper
partner-invariant subgroup. Its specified nonzero section is irreducible. -/
theorem PreparedChosenModule.decomposable_five_canonical_section_irreducible
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
      let E := thompsonFixed T V
      let C := centralizer (localModule T Mc:Set G)
      let F := conjugateSpanBy E C
      let D := (((F⊓centralizer (V:Set G)).subgroupOf Mc).normalCore).map Mc.subtype
      (∀ H:Subgroup G, H≤F → Mc≤normalizer (H:Set G) → H=F ∨ H≤D) ∧
        ∀ {W:Type*} [AddCommGroup W] [Module (ZMod 2) W] [Nontrivial W]
          (ρ:Representation (ZMod 2) Mc W),
          BinaryConjugationSection Mc F D ρ → IsIrreducible ρ := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive
  dsimp only
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc:Set G)
  let F := conjugateSpanBy E C
  let D := (((F⊓centralizer (V:Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  obtain ⟨hCMc,_,hQT,_,_,_,_,_⟩ := h.decomposable_five_partner_kernel_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  obtain ⟨_,_,hFA,_,_,_⟩ := h.decomposable_five_partner_fixed_envelope
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  have hJQ:elementaryAbelianMaxJ (C.pCoreIn 2)≤C.pCoreIn 2 := sSup_le fun _ hA=>hA.1
  have hFQ:F≤C.pCoreIn 2 := fun f hf=>
    hJQ (((mem_omegaOneCenterAmbient_iff _ _).mp (hFA hf)).1)
  have hFMc:F≤Mc := (hFQ.trans (pCoreIn_le 2 C)).trans hCMc
  have hminimal:∀H:Subgroup G,H≤F→Mc≤normalizer (H:Set G)→H=F∨H≤D := by
    intro H hHF hnH
    by_cases hHC:H≤centralizer (V:Set G)
    · right
      intro x hx
      refine ⟨⟨x,hFMc (hHF hx)⟩,?_,rfl⟩
      intro n
      have hnHx := le_normalizer_iff.mp hnH n n.property x hx
      exact ⟨hHF hnHx,hHC hnHx⟩
    · exact Or.inl (h.decomposable_five_moving_normal_span
        hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive H hHF hnH hHC).2
  refine ⟨hminimal,?_⟩
  intro W _ _ _ ρ dF
  exact dF.irreducible_of_subgroup_minimal hminimal

end CFSG.Quasithin.Chapter15.Section01
