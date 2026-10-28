module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.MarkedFiveFinalQuotient
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallMixedRecognition
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.ResidualIdentityAssembly

/-!
# Small-source quotients and the original residual endgame

The marked-five row now supplies its H-star wreath quotients directly.
Combining this with the existing cubic and Omega rows proves all of
15.2.8 from the independent mixed A₅/S₃ Sylow bound and original prior.
The actual two-overgroup theorem and residual-identity endgame then give
the chosen-source contradiction. No marked-five recognition premise or
quintic enumeration remains in this Chapter 15 consumer.

The mixed bound, original prior and residual identities remain explicit
source inputs, with their existing independent owners; this module does
not assert the full quasithin classification.
Source: Aschbacher--Smith 15.2.1--12 and the terminal argument,
printed pp.1104--1112,1119--1120.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
open ChapterF.Source ChosenGeometry ChosenGeometry.Cyclic
variable {G : Type*} [Group G] [Finite G]

/-- Every original small-source H-star quotient is S₃ wreath C₂ once the
independent mixed A₅/S₃ bound and original source prior are supplied. -/
theorem ChosenSmallSource.HStar_wreath_of_mixed_size
    (hsize : ∀ (K A S : Subgroup G), HypothesisF11 ![K,A] S →
      IsQuasithin (generated ![K,A] S) → Chapter1.IsSylowIn 2 S (generated ![K,A] S) →
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) →
      Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) →
      borel A S ≤ normalizer (S : Set G) → Nat.card S ≤ 256)
    {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hprior : SmallSourcePrior T M V) :
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((H ⧸ pCore 2 H) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) := by
  rcases h.HStar_wreath_or_marked_five_of_mixed_size hsize hprior with hwr | hd
  · exact hwr
  · exact fun H hH => h.HStar_wreath_of_marked_five hd hH

/-- The complete small-source quotient theorem feeds the original terminal
argument. Only the independent mixed-size, prior and residual inputs remain. -/
theorem source_chosen_contradiction_of_mixed_size_and_residual_identities
    (hsize : ∀ (K A S : Subgroup G), HypothesisF11 ![K,A] S →
      IsQuasithin (generated ![K,A] S) → Chapter1.IsSylowIn 2 S (generated ![K,A] S) →
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) →
      Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) →
      borel A S ≤ normalizer (S : Set G) → Nat.card S ≤ 256)
    {T : Sylow 2 G} {M Mc V : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hprior : SmallSourcePrior T M V)
    (hresidual : ∀ H B, ResidualInput h H B →
      partnerSpan H Mc = threePrimeResidual Mc) : False :=
  source_chosen_contradiction_of_residual_identities h (h.maximal_overgroups hprior)
    (h.HStar_wreath_of_mixed_size hsize hprior) hresidual

end CFSG.Quasithin.Chapter15.Section02
