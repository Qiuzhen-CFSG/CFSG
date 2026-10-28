module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionBestSource
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionComponent

/-!
# The component moved by the whole original quintic section actor

The precise paired-support comparison makes the whole original V-image a
minimal best offender, of rank two or four. This same actor centralizes
Fitting and moves an actual small component; no contained replacement is
chosen. Its original section, action kernel, fixed codimension and whole
moved-space Irr⁺ statement are retained for the next normalizer argument.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.DecomposableQuinticControl
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

private theorem strong_minimal_centralizes_fitting
    (ρ : Representation (ZMod 2) G W) (hf : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥) {B : Subgroup G}
    (hB : IsMinimalBestOffender ρ B) (hstrong : IsStrongOffender ρ B) :
    B ≤ centralizer (fittingSubgroup G : Set G) := by
  by_contra hn
  have hmove : ⁅fittingSubgroup G,B⁆ ≠ ⊥ := by
    intro hz
    exact hn (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz))
  obtain ⟨b⟩ := ChapterB.FittingStructure.localPlaneLaw ρ hf hcore B hB hmove
  have hr : rank B = 1 := by
    rw [rank,b.actor_card]
    decide
  have hpos := fixedCodim_pos_of_faithful ρ hf hB.1.1.1
  have hlt := hstrong.2
  rw [hr] at hlt
  omega

private theorem component_of_minimal_strong_plane
    (ρ : Representation (ZMod 2) G W) (hf : Function.Injective ρ)
    (hcore : pCore 2 G = ⊥)
    (cover : SQTKQuotient KnownSimple.IsKnownSimple G)
    {A : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hstrong : IsStrongOffender ρ A)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) ≤ 2) :
    A ≤ centralizer (fittingSubgroup G : Set G) ∧
      ∃ K, IsComponent G K ∧ ⁅K,A⁆ = K ∧
        K ≤ normalClosure (A : Set G) ∧
        (K.subgroupOf (normalClosure (A : Set G))).Normal ∧
        IsIrrPlus ρ K (moved ρ K) ∧ SmallMoved.ActorList K := by
  have hfit := strong_minimal_centralizes_fitting ρ hf hcore hA hstrong
  obtain ⟨K,hK,hmove⟩ := ComponentReduction.exists_component_moved ρ hcore hA.1 hfit
  have hn : A ≤ normalizer (K : Set G) := ChapterB.source_lemma_B_1_5_4 ρ hf hA.1 hK
  have hKA : ⁅K,A⁆ = K := by
    rcases hK.commutator_dichotomy A with hz | he
    · exact (hmove hz).elim
    · exact le_antisymm (le_normalizer_iff_commutator_le_left.mp hn)
        (he ▸ le_iSup_conjugates K A)
  obtain ⟨hKN,hnK,_⟩ := moved_component_in_normalClosure ρ hf hK hA.1 hKA
  obtain ⟨hirr,hlist⟩ := component_irrPlus_and_actor_of_minimal_plane ρ hf hcore cover
    hK hA hKA hd
  exact ⟨hfit,K,hK,hKA,hKN,hnK,hirr,hlist⟩

end CFSG.Quasithin.Chapter15.DecomposableQuinticControl

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The whole original V-image moves a literal small component, retaining
its exact rank and fixed codimension on the same faithful F/Uc section. -/
theorem PreparedChosenModule.decomposable_five_core_or_original_section_component
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
              ChapterB.QuasisimpleSource.SmallMoved.ActorList K := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  obtain hcore | ⟨heF,ρ,⟨dF⟩,hfaith,hker,hcard,hcore,hsA,hqA,hplane,hmin,hcost⟩ :=
    h.decomposable_five_core_or_section_minimal_best_offender
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  · exact Or.inl hcore
  right
  let Uc := localModule T Mc
  let F := conjugateSpanBy (thompsonFixed T V) (centralizer (Uc : Set G))
  let : IsElementaryAbelian 2 F := heF
  let σ := Representation.BinaryOffender.imageRepresentation ρ
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  let cover : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple
      (Representation.BinaryOffender.actionImage ρ) :=
    ⟨Mc,(Representation.BinaryOffender.actionHom ρ).ker,
      hG.twoLocal_sqtk hMc.1.1,
      QuotientGroup.quotientKerEquivOfSurjective
        (Representation.BinaryOffender.actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective⟩
  exact ⟨heF,ρ,⟨dF⟩,hfaith,hker,hcard,hcore,hsA,hqA,hplane,hmin,hcost,
    DecomposableQuinticControl.component_of_minimal_strong_plane σ hfaith hcore cover
      hmin hsA hplane⟩

end CFSG.Quasithin.Chapter15.Section01
