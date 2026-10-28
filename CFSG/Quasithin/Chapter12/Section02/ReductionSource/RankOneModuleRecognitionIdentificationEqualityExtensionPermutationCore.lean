module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationEqualityExtensionMarkedQuotient
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionPermutationCore

/-!
# The canonical outer four-image on the Chapter 12 setup

The actual quotient of N_G(L) by O₂(LT) marks L as A₅ and sends the
canonical extraspecial P to an outer elementary four-group with kernel
of order eight. The same homomorphism and literal whole reduced subgroup
are retained throughout. Source: 6.2.13 and 12.2.2(3d), pp.687,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ} {z : G}

/-- The canonical extraspecial image in the original maximal local quotient. -/
theorem reduced_equality_core_permutation_image
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (hbranch : sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓
      commutatorLayer T L = ZS (T : Subgroup G) L (wholeReduced T L)) :
    ∃ f : (normalizer (L : Set G)) →* Equiv.Perm (Fin 5), Function.Surjective f ∧
      f.ker = ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf (normalizer (L : Set G)) ∧
      (L.subgroupOf (normalizer (L : Set G))).map f = alternatingGroup (Fin 5) ∧
      let fP := f.comp (equalityCoreToMaximal hTH h611.sylow_le
        (L := L) (R := wholeReduced T L))
      IsElementaryAbelian 2 fP.range ∧ Nat.card fP.ker = 8 ∧ Nat.card fP.range = 4 ∧
        ¬ fP.range ≤ alternatingGroup (Fin 5) := by
  exact A.equality_core_permutation_image h611 hnatural hz horder hTH hbranch

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
