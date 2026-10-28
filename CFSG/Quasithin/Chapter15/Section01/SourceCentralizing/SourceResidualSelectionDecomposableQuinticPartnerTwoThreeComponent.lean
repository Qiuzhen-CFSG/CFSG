module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoThreeNonsolvable
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionComponent

/-!
# A component moved inside the original canonical quintic action

Strongness selects a contained minimal best offender B in the literal
original V-image A. The Fitting action theorem forces B to centralize
Fitting, so it moves a genuine component. This component lies in the
normal closure of B, and hence in that of the unchanged original A.
No plane bound or small-component classification is used. The component
belongs to the faithful F/D actor; it is not asserted to lift to G.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter15.DecomposableQuinticControl
open ChapterB.QuasisimpleSource ChapterB.SourceInduction

/-- Every strong offender in a faithful core-free action contains an actual
minimal strong offender moving a component in its own normal closure. -/
theorem component_of_strong_offender
    {J W : Type*} [Group J] [Finite J] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) J W)
    (hfaith : Function.Injective σ) (hcore : pCore 2 J = ⊥)
    {A : Subgroup J} (hA : IsStrongOffender σ A) :
    ∃ B ≤ A, IsMinimalBestOffender σ B ∧ IsQuadratic σ B ∧
      IsStrongOffender σ B ∧ B ≤ centralizer (fittingSubgroup J : Set J) ∧
      ∃ K, IsComponent J K ∧ ⁅K,B⁆ = K ∧ K ≤ normalClosure (B : Set J) ∧
        (K.subgroupOf (normalClosure (B : Set J))).Normal ∧
        K ≤ normalClosure (A : Set J) := by
  obtain ⟨B,hBA,hB,hquad,hBs⟩ := hA.exists_quadratic_minimalBestOffender σ
  have hfit := strong_minimal_centralizes_fitting σ hfaith hcore hB hBs
  obtain ⟨K,hK,hmove⟩ := ComponentReduction.exists_component_moved σ hcore hB.1 hfit
  have hn : B ≤ normalizer (K : Set J) := ChapterB.source_lemma_B_1_5_4 σ hfaith hB.1 hK
  have hKB : ⁅K,B⁆ = K := by
    rcases hK.commutator_dichotomy B with hz | he
    · exact (hmove hz).elim
    · exact le_antisymm (le_normalizer_iff_commutator_le_left.mp hn)
        (he ▸ le_iSup_conjugates K B)
  obtain ⟨hKN,hnK,_⟩ := moved_component_in_normalClosure σ hfaith hK hB.1 hKB
  exact ⟨B,hBA,hB,hquad,hBs,hfit,K,hK,hKB,hKN,hnK,
    hKN.trans (normalClosure_mono hBA)⟩

end CFSG.Quasithin.Chapter15.DecomposableQuinticControl

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The actual dimension-three original seed selects a moved component on
the same supplied canonical section, retaining its contained actor mark. -/
theorem PreparedChosenModule.decomposable_five_partner_two_three_component
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
      V ≤ Mc.pCoreIn 2 ∨
        ∀ {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
          (ρ : Representation (ZMod 2) Mc W) (dF : BinaryConjugationSection Mc F D ρ),
          Module.finrank (ZMod 2) (dF.imageSpace E) = 3 →
          let A := actionSubgroup ρ (V.subgroupOf Mc)
          let σ := Representation.BinaryOffender.imageRepresentation ρ
          ∃ B ≤ A, IsMinimalBestOffender σ B ∧ IsQuadratic σ B ∧
            IsStrongOffender σ B ∧
            B ≤ centralizer (fittingSubgroup (Representation.BinaryOffender.actionImage ρ) :
              Set (Representation.BinaryOffender.actionImage ρ)) ∧
            ∃ K, IsComponent (Representation.BinaryOffender.actionImage ρ) K ∧ ⁅K,B⁆ = K ∧
              K ≤ normalClosure (B : Set (Representation.BinaryOffender.actionImage ρ)) ∧
              (K.subgroupOf (normalClosure (B : Set (Representation.BinaryOffender.actionImage ρ)))).Normal ∧
              K ≤ normalClosure (A : Set (Representation.BinaryOffender.actionImage ρ)) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc : Set G)
  let F := conjugateSpanBy E C
  let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  rcases h.decomposable_five_partner_two_three_strong
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU with
    hcore | hstrong
  · exact Or.inl hcore
  right
  intro W _ _ ρ dF hdim
  let : Finite W := Finite.of_surjective (fun x : F => (dF.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp dF.onto)
  have hdimW : 0 < Module.finrank (ZMod 2) W :=
    lt_of_lt_of_le (by decide : 0 < 3)
      (hdim ▸ Submodule.finrank_le (dF.imageSpace E))
  let : Nontrivial W := (Module.finrank_pos_iff (R := ZMod 2) (M := W)).mp hdimW
  have hirr : IsIrreducible ρ := (h.decomposable_five_canonical_section_irreducible
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2 ρ dF
  exact DecomposableQuinticControl.component_of_strong_offender
    (Representation.BinaryOffender.imageRepresentation ρ) (imageRepresentation_injective ρ)
    (actionImage_twoCore_eq_bot ρ hirr) (hstrong ρ dF hdim).2

end CFSG.Quasithin.Chapter15.Section01
