module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.BinaryExclusion
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.NaturalPair

/-!
# The terminal binary-linear exclusion on the original source

The actual C.2.7 binary branch supplies its relative normality, cubic
residual identity and K-containment. Its intrinsic movement excludes
containment in Mc. The original-U module classification excludes the
natural-dual, exterior-five and orthogonal-six rows, leaving the marked
natural-five action. That action constructs the literal KS two-core
quotient, and hence S-reducibility. The minimal-parabolic residual inside
the original X is a two-perfect seed in NI = M ∩ I outside MI = Mc ∩ I.
Corrected 15.2.21(1),(3) supplies the contrary S-irreducibility.

The selected-component application also constructs the binary parabolic
marking and faithful NI action. No KS quotient, component escape, residual
placement, T-irreducibility or final small-action conclusion is assumed.
The preceding HStar quotients, Kc orbit, restricted action, plane involution
and no-chi statements retain their source producers in plane geometry,
small-parabolic and component models; final discharge belongs to
qt-e-152-plane-uniqueness.

Source: Aschbacher--Smith, 15.2.21 and 15.2.23, printed pp.1114,1116--1117;
refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 PlaneUniquenessPreceding ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

namespace TerminalLinear

/-- Exclude the literal L₄(2)/L₅(2) branch of C.2.7. The original component
and small-action theorems discharge every terminal module premise. -/
theorem binaryBranch_false
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* ChosenGeometry.Wreath))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {n : ℕ} (b : BinaryBranch M I X n)
    (hNI : ¬ M ⊓ I ≤ Mc ⊓ I)
    (eNI : OmegaAction.intersectionImage hsource I ≃* Equiv.Perm (Fin 3)) :
    letI := hsource.prepared.elementary
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) → False :=
  SmallActionsSource.binaryComponent_false_from_preceding d hquotient horbit hI hfit
    (ComponentCatalogue.binary_not_le_partner d horbit hI b) b hNI eNI

end TerminalLinear

namespace ComponentCatalogue
open TerminalLinear
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

/-- Apply the binary exclusion to the original selected component, using
its unmarked star equivalence. The actual KS pair quotient is proved from
the natural-five action, so it is not an additional source premise. -/
theorem normalized_binary_false_from_preceding
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* ChosenGeometry.Wreath))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (s : Normalized H M I X)
    (hno : ∀ Y : Subgroup I, ¬ ChapterC.IsChiBlockIn Y)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃* SL(n,ZMod 2))
    (hNI : ¬ M ⊓ I ≤ Mc ⊓ I)
    (ha : letI := hsource.prepared.elementary;
      Nonempty (internalActionImage M V hsource.prepared.normalized ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (hi : OmegaAction.PlaneInverter hsource ZS) : False := by
  let := hsource.prepared.elementary
  have ho := OmegaAction.omega_of_restricted_actions d hI ha hNI
  obtain ⟨eNI⟩ := OmegaAction.intersection_image_equiv_of_omega d hI hNI ho hi
  obtain ⟨f,hf,hker⟩ := OmegaAction.exists_symmetricThree_action_of_image_equiv eNI
  have hcore := d.intersection_core_eq_of_centralizes hI
    (intersection_core_centralizes_of_symmetricThree f hf hker)
  have hs := normalized_component_input (hsource := hsource) hI hcore s
  let b : BinaryBranch M I X n :=
    ⟨hs,hn,binary_model_marked_parabolic d hI hs (s.toSelected.not_chi hno) hn e⟩
  exact binaryBranch_false d hquotient horbit hI hfit b hNI eNI ho

end ComponentCatalogue
end CFSG.Quasithin.Chapter15.Section02
