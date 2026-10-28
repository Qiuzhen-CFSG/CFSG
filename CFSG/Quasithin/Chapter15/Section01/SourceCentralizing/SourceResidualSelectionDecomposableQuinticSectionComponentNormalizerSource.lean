module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionOriginalComponent
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionComponentNormalizer

/-!
# The original Sylow image preserves the selected quintic component

The whole original V-image is a minimal best offender and its moved space
lies in the marked quotient plane. Its normalizer therefore preserves the
selected Irr⁺ component. Original T-normality of V transports through the
literal section action, giving normalization by the actual T-image.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The whole original V-image moves a literal small component, retaining
its exact rank and fixed codimension on the same faithful F/Uc section. -/
theorem PreparedChosenModule.decomposable_five_core_or_sylow_normalized_section_component
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
      Nat.card (localModule T Mc) = 4 →
      let Uc := localModule T Mc
      let F := conjugateSpanBy (thompsonFixed T V) (centralizer (Uc : Set G))
      V ≤ Mc.pCoreIn 2 ∨
        ∃ he : IsElementaryAbelian 2 F,
          letI := he
          ∃ ρ : Representation (ZMod 2) Mc (Additive (F ⧸ Uc.subgroupOf F)),
            Nonempty (BinaryConjugationSection Mc F Uc ρ) ∧
            Function.Injective (Representation.BinaryOffender.imageRepresentation ρ) ∧
            (Representation.BinaryOffender.actionHom ρ).ker.map Mc.subtype =
              commutatorPreimage Mc F Uc ∧
            Nat.card (actionSubgroup ρ (V.subgroupOf Mc)) =
              (commutatorPreimage Mc F Uc).relIndex V ∧
            pCore 2 (Representation.BinaryOffender.actionImage ρ) = ⊥ ∧
            IsStrongOffender (Representation.BinaryOffender.imageRepresentation ρ)
              (actionSubgroup ρ (V.subgroupOf Mc)) ∧
            IsQuadratic (Representation.BinaryOffender.imageRepresentation ρ)
              (actionSubgroup ρ (V.subgroupOf Mc)) ∧
            Module.finrank (ZMod 2) (subspaceCommutator
              (Representation.BinaryOffender.imageRepresentation ρ) ⊤
              (actionSubgroup ρ (V.subgroupOf Mc))) ≤ 2 ∧
            IsMinimalBestOffender (Representation.BinaryOffender.imageRepresentation ρ)
              (actionSubgroup ρ (V.subgroupOf Mc)) ∧
            ((rank (actionSubgroup ρ (V.subgroupOf Mc)) = 2 ∧
              fixedCodim (Representation.BinaryOffender.imageRepresentation ρ)
                (actionSubgroup ρ (V.subgroupOf Mc)) = 1) ∨
             (rank (actionSubgroup ρ (V.subgroupOf Mc)) = 4 ∧
              fixedCodim (Representation.BinaryOffender.imageRepresentation ρ)
                (actionSubgroup ρ (V.subgroupOf Mc)) = 2)) ∧
            let A := actionSubgroup ρ (V.subgroupOf Mc)
            A ≤ centralizer (fittingSubgroup (Representation.BinaryOffender.actionImage ρ) :
              Set (Representation.BinaryOffender.actionImage ρ)) ∧
            ∃ K, IsComponent (Representation.BinaryOffender.actionImage ρ) K ∧ ⁅K,A⁆ = K ∧
              K ≤ normalClosure (A : Set (Representation.BinaryOffender.actionImage ρ)) ∧
              (K.subgroupOf (normalClosure (A : Set (Representation.BinaryOffender.actionImage ρ)))).Normal ∧
              IsIrrPlus (Representation.BinaryOffender.imageRepresentation ρ) K
                (ChapterB.QuasisimpleSource.moved (Representation.BinaryOffender.imageRepresentation ρ) K) ∧
              ChapterB.QuasisimpleSource.SmallMoved.ActorList K ∧
              normalizer (A : Set (Representation.BinaryOffender.actionImage ρ)) ≤
                normalizer (K : Set (Representation.BinaryOffender.actionImage ρ)) ∧
              actionSubgroup ρ ((T : Subgroup G).subgroupOf Mc) ≤
                normalizer (K : Set (Representation.BinaryOffender.actionImage ρ)) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  obtain hcore | ⟨heF,ρ,⟨dF⟩,hfaith,hker,hcard,hcore,hsA,hqA,hplane,hmin,hcost,
      hfit,K,hK,hKA,hKN,hnK,hirr,hlist⟩ :=
    h.decomposable_five_core_or_original_section_component
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  · exact Or.inl hcore
  right
  let Uc := localModule T Mc
  let F := conjugateSpanBy (thompsonFixed T V) (centralizer (Uc : Set G))
  let : IsElementaryAbelian 2 F := heF
  let σ := Representation.BinaryOffender.imageRepresentation ρ
  let A := actionSubgroup ρ (V.subgroupOf Mc)
  have hn : normalizer (A:Set (Representation.BinaryOffender.actionImage ρ))≤
      normalizer (K:Set (Representation.BinaryOffender.actionImage ρ)) :=
    DecomposableQuinticControl.component_normalized_by_actor_normalizer_of_minimal_plane
      σ hfaith hK hirr hmin hKA hplane
  have hTV : (T:Subgroup G)≤normalizer (V:Set G) := hM.1.2.trans h.normalized
  have hTN : (T:Subgroup G).subgroupOf Mc≤normalizer (V.subgroupOf Mc:Set Mc) := by
    intro t ht v
    exact hTV ht (v:G)
  have hTA : actionSubgroup ρ ((T:Subgroup G).subgroupOf Mc)≤
      normalizer (A:Set (Representation.BinaryOffender.actionImage ρ)) :=
    (map_mono hTN).trans ((V.subgroupOf Mc).le_normalizer_map
      (Representation.BinaryOffender.actionHom ρ))
  exact ⟨heF,ρ,⟨dF⟩,hfaith,hker,hcard,hcore,hsA,hqA,hplane,hmin,hcost,
    hfit,K,hK,hKA,hKN,hnK,hirr,hlist,hn,hTA.trans hn⟩

end CFSG.Quasithin.Chapter15.Section01
