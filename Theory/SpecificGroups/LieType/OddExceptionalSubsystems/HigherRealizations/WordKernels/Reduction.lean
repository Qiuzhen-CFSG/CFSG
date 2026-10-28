module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.SixNodes
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralLattice

/-!
# Reduction of the folded word comparison to the six-node representations

The two genuine representation obligations are kept separate. Restriction to
the integral E6 adjoint block gives the implication from a trivial larger
matrix word to a trivial source word. Conversely, a word trivial in the E6
adjoint representation must be represented by an E6 central character in each
larger realization, with its diagram transform represented by the transformed
character. These representation assertions are inputs here, not proved facts.

The integral lattice calculation shows that a diagram-fixed central-character
value is trivial. Every folded word is diagram-fixed on evaluation, so the two
inputs imply equality of the literal folded-word kernels and give marked
injective homomorphisms through the existing descent constructors. This avoids
postulating a homomorphism from the whole adjoint E6 group. No identification
of the folded subgroup with F4 is used.

Source: GLS3 §§2.5--2.6, especially 2.6.2--3, and the exceptional inclusions in
Aschbacher--Smith A.2.17, printed p.39 (`refs/quasithin.pdf`).
-/

@[expose] public section
noncomputable section

open Theory.AlgebraicGroup.StandardRootSystem
namespace TwistedE6.FoldedSubsystem.HigherRealizations

variable (F : Type*) [Field F]

/-- The precise central-version comparison on all six-node words. A producer
must construct these characters from the actual integral matrix representations.
The paired equality records the pinned diagram action on the same character. -/
def CentralCharacterComparison {G : Type*} [Group G] (v : SixNodeWord F →* G) : Prop :=
  ∀ w, sourceSix F w = 1 →
    ∃ c : typeE6WeightLatticeQuotient →+ Additive G,
      v w = CentralLattice.characterValue c CentralLattice.centralWeight ∧
      v (diagramWord F w) =
        CentralLattice.characterValue c
          (CentralLattice.quotientDiagram CentralLattice.centralWeight)

/-- Folded kernel equality follows from adjoint restriction and the genuine
central-character comparison, rather than an adjoint-to-universal group map. -/
theorem folded_ker_eq_of_sixNode_comparison {G : Type*} [Group G]
    (v : SixNodeWord F →* G)
    (hrestrict : v.ker ≤ (sourceSix F).ker)
    (hcentral : CentralCharacterComparison F v)
    (hfixed : ∀ w, v (diagramWord F (expandFolded F w)) = v (expandFolded F w)) :
    (sourceWord F).ker = (v.comp (expandFolded F)).ker := by
  ext w
  change sourceWord F w = 1 ↔ v (expandFolded F w) = 1
  constructor
  · intro hw
    have hs : sourceSix F (expandFolded F w) = 1 := by
      rw [sourceSix_expandFolded, hw]
      rfl
    obtain ⟨c, hc, hd⟩ := hcentral (expandFolded F w) hs
    have hf : CentralLattice.characterValue c
          (CentralLattice.quotientDiagram CentralLattice.centralWeight) =
        CentralLattice.characterValue c CentralLattice.centralWeight :=
      hd.symm.trans ((hfixed w).trans hc)
    exact hc.trans (CentralLattice.characterValue_eq_one_of_fixed c _ hf)
  · intro hw
    have hs : sourceSix F (expandFolded F w) = 1 := hrestrict hw
    apply Subtype.ext
    simpa only [sourceSix_expandFolded, OneMemClass.coe_one] using hs

theorem sourceWord_ker_eq_e7Word_of_sixNode_comparison
    (hrestrict : (e7Six F).ker ≤ (sourceSix F).ker)
    (hcentral : CentralCharacterComparison F (e7Six F)) :
    (sourceWord F).ker = (e7Word F).ker := by
  have h := folded_ker_eq_of_sixNode_comparison F (e7Six F) hrestrict hcentral
    (fun w => (e7Six_diagram_expandFolded F w).trans (e7Six_expandFolded F w).symm)
  ext w
  simpa only [MonoidHom.mem_ker, MonoidHom.comp_apply, e7Six_expandFolded] using
    SetLike.ext_iff.mp h w

theorem sourceWord_ker_eq_e8Word_of_sixNode_comparison
    (hrestrict : (e8Six F).ker ≤ (sourceSix F).ker)
    (hcentral : CentralCharacterComparison F (e8Six F)) :
    (sourceWord F).ker = (e8Word F).ker := by
  have h := folded_ker_eq_of_sixNode_comparison F (e8Six F) hrestrict hcentral
    (fun w => (e8Six_diagram_expandFolded F w).trans (e8Six_expandFolded F w).symm)
  ext w
  simpa only [MonoidHom.mem_ker, MonoidHom.comp_apply, e8Six_expandFolded] using
    SetLike.ext_iff.mp h w

/-- The marked E7 map, conditional on the two explicit representation inputs. -/
def e7CoverMapOfSixNodeComparison
    (hrestrict : (e7Six F).ker ≤ (sourceSix F).ker)
    (hcentral : CentralCharacterComparison F (e7Six F)) :
    splitSubgroup F →* ExceptionalSplit.e7Cover F :=
  e7CoverMapOfWordKernels F
    (sourceWord_ker_eq_e7Word_of_sixNode_comparison F hrestrict hcentral)

/-- The marked E8 map, conditional on the two explicit representation inputs. -/
def e8CoverMapOfSixNodeComparison
    (hrestrict : (e8Six F).ker ≤ (sourceSix F).ker)
    (hcentral : CentralCharacterComparison F (e8Six F)) :
    splitSubgroup F →* ExceptionalSplit.e8Cover F :=
  e8CoverMapOfWordKernels F
    (sourceWord_ker_eq_e8Word_of_sixNode_comparison F hrestrict hcentral)

theorem e7CoverMapOfSixNodeComparison_injective
    (hrestrict : (e7Six F).ker ≤ (sourceSix F).ker)
    (hcentral : CentralCharacterComparison F (e7Six F)) :
    Function.Injective (e7CoverMapOfSixNodeComparison F hrestrict hcentral) :=
  e7CoverMapOfWordKernels_injective F _

theorem e8CoverMapOfSixNodeComparison_injective
    (hrestrict : (e8Six F).ker ≤ (sourceSix F).ker)
    (hcentral : CentralCharacterComparison F (e8Six F)) :
    Function.Injective (e8CoverMapOfSixNodeComparison F hrestrict hcentral) :=
  e8CoverMapOfWordKernels_injective F _

@[simp] theorem e7CoverMapOfSixNodeComparison_f4Simple
    (hrestrict : (e7Six F).ker ≤ (sourceSix F).ker)
    (hcentral : CentralCharacterComparison F (e7Six F)) (s : Bool) (i : Fin 4) (t : F) :
    e7CoverMapOfSixNodeComparison F hrestrict hcentral (f4Simple F s i t) =
      e7FoldedSimple F s i t := e7CoverMapOfWordKernels_f4Simple F _ s i t

@[simp] theorem e8CoverMapOfSixNodeComparison_f4Simple
    (hrestrict : (e8Six F).ker ≤ (sourceSix F).ker)
    (hcentral : CentralCharacterComparison F (e8Six F)) (s : Bool) (i : Fin 4) (t : F) :
    e8CoverMapOfSixNodeComparison F hrestrict hcentral (f4Simple F s i t) =
      e8FoldedSimple F s i t := e8CoverMapOfWordKernels_f4Simple F _ s i t

end TwistedE6.FoldedSubsystem.HigherRealizations
