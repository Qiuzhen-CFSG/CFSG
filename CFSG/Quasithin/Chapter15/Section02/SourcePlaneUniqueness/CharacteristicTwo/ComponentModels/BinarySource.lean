module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.BinaryResidual
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.LinearFlags
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.RepeatedNatural.Source
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.OmegaAction.SourceAction
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.Orbit

/-!
# Original-source input to the binary small-action obstruction

The binary residual theorem discharges the component-residual identity,
relative normality and K-containment required by the terminal original-U
recognition. Its output is the literal L₄(2) quotient, S-reducibility and
two-perfect minimal-parabolic seed for corrected 15.2.21(3).

The source-action adapter also constructs the S₃ action on the original
NI = M ∩ I, with kernel C_NI(V). The actual wreath quotient supplies
T-irreducibility, and the earlier component-orbit alternative gives Kc's
centralization. The restricted actions, involution, S₃-square quotient and
component-orbit alternative remain explicit source premises.
The L₅(2) consumer constructs the marked binary branch on the same
selected X, R and NI from its original star-model equivalence.
Neither the marked catalogue nor corrected 15.2.21(3)
is assumed proved by this conditional consumer.

Source: Aschbacher--Smith, 15.2.18(3), 15.2.21 and 15.2.23,
printed pp.1113--1117; refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Section01 PlaneUniquenessPreceding TerminalLinear ChapterD ChapterD.UniqueFactor
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- Apply the terminal module argument after proving the actual component
residual, relative normality and K-placement from the marked binary row. -/
theorem binary_smallAction_obstruction
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hout : ¬ X ≤ Mc) {n : ℕ} (b : BinaryBranch M I X n)
    (hpair : Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hirr : IsSmallActionIrreducible (T : Subgroup G) (smallActionK H))
    (hc : smallActionKc H Mc ≤ centralizer (ZS : Set G))
    (hNI : ¬ M ⊓ I ≤ Mc ⊓ I)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hf : Function.Surjective f)
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I)) :
    Nonempty ((smallActionKc H Mc ⧸ pCore 2 (smallActionKc H Mc)) ≃* SL(4,ZMod 2)) ∧
      ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H) ∧
      ∃ P : Subgroup G, smallActionS T ZS ⊓ X ⋖ P ∧ P ≤ X ∧ P ≤ M ⊓ I ∧
        smallActionS T ZS ≤ normalizer (P : Set G) ∧
        SmallActionsSource.Seed M I (smallActionS T ZS) ((pResidual 2 P).map P.subtype) ∧
        ¬ (pResidual 2 P).map P.subtype ≤ Mc ⊓ I := by
  exact TerminalLinear.binaryBranch_smallAction_obstruction d hI hfit
    (binary_normalized (hsource := hsource) hI b) hout b
    (binary_eq_threeResidual (hsource := hsource) hI b)
    ((binary_residual_le_M1 d hI b).trans inf_le_left) hpair hirr hc hNI f hf hker

/-- The binary consumer on the original source action. The S₃ quotient,
its exact kernel, component-residual identity and K-placement are all
constructed; the genuine earlier action clauses remain explicit. -/
theorem binary_smallAction_obstruction_of_restricted_actions
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hout : ¬ X ≤ Mc) {n : ℕ} (b : BinaryBranch M I X n)
    (hpair : Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hNI : ¬ M ⊓ I ≤ Mc ⊓ I)
    (ha : letI := hsource.prepared.elementary;
      Nonempty (internalActionImage M V hsource.prepared.normalized ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (hi : OmegaAction.PlaneInverter hsource ZS) :
    Nonempty ((smallActionKc H Mc ⧸ pCore 2 (smallActionKc H Mc)) ≃* SL(4,ZMod 2)) ∧
      ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H) ∧
      ∃ P : Subgroup G, smallActionS T ZS ⊓ X ⋖ P ∧ P ≤ X ∧ P ≤ M ⊓ I ∧
        smallActionS T ZS ≤ normalizer (P : Set G) ∧
        SmallActionsSource.Seed M I (smallActionS T ZS) ((pResidual 2 P).map P.subtype) ∧
        ¬ (pResidual 2 P).map P.subtype ≤ Mc ⊓ I := by
  obtain ⟨_,f,hf,hker,_⟩ := OmegaAction.intersection_source_action d hI ha hi hNI
  have hc := SmallActionsSource.orbit_centralizes_of_reducible d horbit hI
    (TerminalLinear.reducible_of_symmetricThreePair d hpair)
  exact binary_smallAction_obstruction d hI hfit hout b hpair
    (SmallActionsSource.sylow_irreducible d) hc hNI f hf hker

/-- On the same selected L₅(2) component, the star-model equivalence
constructs the marked positive-rank flag before applying the terminal
argument. No marked-parabolic or Thompson-placement callback remains. -/
theorem normalized_linearFive_smallAction_obstruction
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (s : Normalized H M I X) (hout : ¬ X ≤ Mc)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* SL(5,ZMod 2))
    (hpair : Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hNI : ¬ M ⊓ I ≤ Mc ⊓ I)
    (ha : letI := hsource.prepared.elementary;
      Nonempty (internalActionImage M V hsource.prepared.normalized ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (hi : OmegaAction.PlaneInverter hsource ZS) :
    Nonempty ((smallActionKc H Mc ⧸ pCore 2 (smallActionKc H Mc)) ≃* SL(4,ZMod 2)) ∧
      ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H) ∧
      ∃ P : Subgroup G, smallActionS T ZS ⊓ X ⋖ P ∧ P ≤ X ∧ P ≤ M ⊓ I ∧
        smallActionS T ZS ≤ normalizer (P : Set G) ∧
        SmallActionsSource.Seed M I (smallActionS T ZS) ((pResidual 2 P).map P.subtype) ∧
        ¬ (pResidual 2 P).map P.subtype ≤ Mc ⊓ I := by
  obtain ⟨_,f,hf,hker,_⟩ := OmegaAction.intersection_source_action d hI ha hi hNI
  have hcore := d.intersection_core_eq_of_centralizes hI
    (intersection_core_centralizes_of_symmetricThree f hf hker)
  have hs := normalized_component_input (hsource := hsource) hI hcore s
  have hp := linearFive_marked_parabolic hs
    ((M ⊓ I).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (M ⊓ I) (pCore 2 (M ⊓ I : Subgroup G))))
    (s.toSelected.not_chi hno) e
  let b : BinaryBranch M I X 5 := ⟨hs,Or.inr rfl,hp⟩
  have hc := SmallActionsSource.orbit_centralizes_of_reducible d horbit hI
    (TerminalLinear.reducible_of_symmetricThreePair d hpair)
  exact binary_smallAction_obstruction d hI hfit hout b hpair
    (SmallActionsSource.sylow_irreducible d) hc hNI f hf hker

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
