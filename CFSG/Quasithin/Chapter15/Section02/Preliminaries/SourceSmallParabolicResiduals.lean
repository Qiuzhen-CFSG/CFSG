module

public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallMixedRecognition
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SourceSmallParabolicTerminal
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallKernelCentralizer
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.ResidualIdentityAssembly

/-!
# The marked-five source action with Held retained

Apply the chosen-action contradiction to the literal wreath alternative of
the small-parabolic recognition theorem. The Held residual row is now
discharged by its terminal consumer, so this application requires only the
residual identities, in addition to the existing mixed size and prior inputs.
The marked-five action is the remaining source alternative; its later
exclusions and the independent mixed size theorem remain separate obligations.

Source: Aschbacher--Smith, 15.2.1--12 and the terminal argument,
printed pp.1104--1112,1119--1120.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
open ChapterF.Source ChosenGeometry ChosenGeometry.Cyclic
variable {G : Type*} [Group G] [Finite G]

/-- The literal marked-five consumer after internally excluding the Held
residual row; no structural-list premise is required. -/
theorem source_chosen_marked_five_of_mixed_size_and_residual_identities
    (hsize : ∀ (K A S : Subgroup G), HypothesisF11 ![K,A] S →
      IsQuasithin (generated ![K,A] S) → Chapter1.IsSylowIn 2 S (generated ![K,A] S) →
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) →
      Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) →
      borel A S ≤ normalizer (S : Set G) → Nat.card S ≤ 256)
    {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hprior : SmallSourcePrior T M V)
    (hresidual : ∀ J B, ResidualInput h J B →
      partnerSpan J Mc = threePrimeResidual Mc) :
    letI := h.prepared.elementary
    ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
      (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
      DihedralMarking l 5 2 := by
  rcases source_chosen_marked_five_or_omega_of_mixed_size hsize h hprior with hf | ho
  · exact hf
  · have hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
        Nonempty ((P ⧸ pCore 2 P) ≃* Wreath) :=
      fun P hP => h.HStar_wreath_of_omega_of_mixed_size hsize hprior ho hP
    exact (source_chosen_contradiction_of_residual_identities h
      (h.maximal_overgroups_of_omega ho) hquotient hresidual).elim

end CFSG.Quasithin.Chapter15.Section02
