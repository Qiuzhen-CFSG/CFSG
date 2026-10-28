module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionComponentNormalizerSource
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionComponentNormalizerFull

/-!
# A normal component in the original quintic section image

The actual whole V-image moves the selected component, and its original
Sylow image normalizes that component. Complete B.5 on the literal normal
closure of V's image permits at most two conjugates. The Sylow orbit parity
therefore forces normality in the full faithful section image, retaining
all original module, action, kernel and component markers.
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
theorem PreparedChosenModule.decomposable_five_core_or_normal_section_component
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
                normalizer (K : Set (Representation.BinaryOffender.actionImage ρ)) ∧ K.Normal := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  obtain hcore | ⟨heF,ρ,⟨dF⟩,hfaith,hker,hcard,hcore,hsA,hqA,hplane,hmin,hcost,
      hfit,K,hK,hKA,hKN,hnK,hirr,hlist,hNA,hTK⟩ :=
    h.decomposable_five_core_or_sylow_normalized_section_component
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  · exact Or.inl hcore
  right
  let Uc := localModule T Mc
  let F := conjugateSpanBy (thompsonFixed T V) (centralizer (Uc : Set G))
  let : IsElementaryAbelian 2 F := heF
  let σ := Representation.BinaryOffender.imageRepresentation ρ
  have hMc : Mc∈maximalTwoLocalOvergroups (centralizer (centralInvolutions T:Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T:Subgroup G)≤Mc := by
    intro t ht
    exact hMc.2 (fun z hz=>(centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  let cover : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple
      (Representation.BinaryOffender.actionImage ρ) :=
    ⟨Mc,(Representation.BinaryOffender.actionHom ρ).ker,
      hG.twoLocal_sqtk hMc.1.1,
      QuotientGroup.quotientKerEquivOfSurjective
        (Representation.BinaryOffender.actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective⟩
  let S : Sylow 2 (Representation.BinaryOffender.actionImage ρ) :=
    (T.subtype hTMc).mapSurjective ρ.asGroupHom.rangeRestrict_surjective
  have hSN : (S:Subgroup (Representation.BinaryOffender.actionImage ρ))≤
      normalizer (K:Set (Representation.BinaryOffender.actionImage ρ)) := hTK
  have hn : K.Normal :=
    DecomposableQuinticControl.component_normal_of_sylow_normalizes_of_normalClosure_best
      σ hfaith hcore cover hmin.1 hK hKA S hSN
  exact ⟨heF,ρ,⟨dF⟩,hfaith,hker,hcard,hcore,hsA,hqA,hplane,hmin,hcost,
    hfit,K,hK,hKA,hKN,hnK,hirr,hlist,hNA,hTK,hn⟩

end CFSG.Quasithin.Chapter15.Section01
