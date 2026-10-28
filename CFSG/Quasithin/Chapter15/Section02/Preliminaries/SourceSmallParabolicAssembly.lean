module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallMixedRecognition
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallKernelCentralizer
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.DistinguishedPlane

/-!
# The remaining marked-five action after the mixed recognition input

The completed maximal-overgroup theorem and the conditional cubic/Omega
wreath quotients feed the existing terminal chosen-action contradiction.
This removes those two action rows using exactly the independent mixed
Sylow bound and preceding 15.2.12 residual clauses. The remaining action
carries its actual dihedral marking; no plane, inverter, uniqueness or
common-plane callback is added.

The mixed size theorem is owned by qt-d-tensor-mixed-size-bound. The
15.2.12 source producer and the final chosen-action assembly retain their
existing owners. The marked-five S₃/S₅ and wreath exclusions remain with
qt-e-152-small-parabolic; this is conditional assembly, not a proof of all
of 15.2.1--8 or Section 15.2.

Source: Aschbacher--Smith 15.2.1--8 and 15.2.12, printed pp.1104--1112,
and the terminal chosen-action argument, printed pp.1110--1120.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
open ChapterF.Source ChosenGeometry ChosenGeometry.Cyclic
variable {G : Type*} [Group G] [Finite G]

/-- The cubic and Omega chosen actions reach the completed terminal consumer
from the mixed Sylow bound and the original 15.2.12 residual clauses. Hence
only the literal marked-five action remains under these independent inputs.
The mixed theorem's owner is qt-d-tensor-mixed-size-bound; this theorem does
not discharge its size bound or the original residual clauses. -/
theorem source_chosen_marked_five_of_mixed_size_and_preceding_residuals
    (hsize : ∀ (K A S : Subgroup G), HypothesisF11 ![K,A] S →
      IsQuasithin (generated ![K,A] S) → Chapter1.IsSylowIn 2 S (generated ![K,A] S) →
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) →
      Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) →
      borel A S ≤ normalizer (S : Set G) → Nat.card S ≤ 256)
    {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hprior : SmallSourcePrior T M V)
    (hresidual : ∀ J B, ResidualInput h J B →
      partnerSpan J Mc = threePrimeResidual Mc ∧ StructuralAlternatives T J Mc) :
    letI := h.prepared.elementary
    ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
      (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
      DihedralMarking l 5 2 := by
  exact (h.HStar_wreath_or_marked_five_of_mixed_size hsize hprior).resolve_left
    (fun hquotient => source_chosen_contradiction_of_preceding_residuals h
      (h.maximal_overgroups hprior) hquotient hresidual)

end CFSG.Quasithin.Chapter15.Section02
