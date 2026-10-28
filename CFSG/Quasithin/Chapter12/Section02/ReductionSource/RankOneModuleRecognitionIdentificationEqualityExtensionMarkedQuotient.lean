module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationEqualityExtensionLayer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionMarkedQuotient
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionFixed
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionCoreImage

/-!
# Marked local quotient and core geometry for Chapter 12

The original whole reduced subgroup supplies M=LT and a marked M/Q≃S₅,
where Q=O₂(LT). The same source inputs give the fixed plane in Q and the
canonical extraspecial core's kernel and fixed line on the natural layer.
Natural-vector fusion supplies the layer part of the eventual transfer.
The centralizer order bound and remaining fusion clauses stay with the
equality-geometry owner; no recognition conclusion is asserted here.

Source: Aschbacher–Smith, 6.2.13 and 12.2.2(3d), pp.687–688,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ} {z : G}

/-- The same quotient equivalence identifies the literal image of L with A₅. -/
theorem reduced_equality_marked_core_quotient
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (hbranch : sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓
      commutatorLayer T L = ZS (T : Subgroup G) L (wholeReduced T L)) :
    letI := A.equality_local_core_normal h611 hnatural hz horder hTH hbranch
    ∃ e : ((normalizer (L : Set G)) ⧸
      ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf (normalizer (L : Set G))) ≃*
        Equiv.Perm (Fin 5),
      (L.subgroupOf (normalizer (L : Set G))).map (e.toMonoidHom.comp
        (QuotientGroup.mk' (((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf
          (normalizer (L : Set G))))) = alternatingGroup (Fin 5) := by
  exact A.equality_marked_local_core_quotient h611 hnatural hz horder hTH hbranch

/-- The fixed spaces and core intersection used by the source extension calculation. -/
theorem reduced_equality_core_fixed_geometry
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (hbranch : sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓
      commutatorLayer T L = ZS (T : Subgroup G) L (wholeReduced T L)) :
    normalizer (L : Set G) = L ⊔ (T : Subgroup G) ∧
      (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer ((T : Subgroup G) ⊓ L : Set G) =
        ZS (T : Subgroup G) L (wholeReduced T L) ∧
      (equalityCore L (wholeReduced T L) z).map (centralizer ({z} : Set G)).subtype ⊓
          (L ⊔ (T : Subgroup G)).pCoreIn 2 =
        commutatorLayer T L ⊓
          (equalityCore L (wholeReduced T L) z).map (centralizer ({z} : Set G)).subtype ∧
      commutatorLayer T L ⊓ centralizer
        ((equalityCore L (wholeReduced T L) z).map
          (centralizer ({z} : Set G)).subtype : Set G) = zpowers z ∧
      ∀ v ∈ commutatorLayer T L, orderOf v = 2 → IsConj z v := by
  exact ⟨A.equality_maximal_eq_local h611 hnatural hz horder hTH hbranch,
    A.equality_local_core_sylow_fixed h611 hnatural hz horder hTH hbranch,
    A.equality_core_inf_local_core h611 hnatural hz horder hTH hbranch,
    A.equality_layer_core_centralizer h611 hnatural hz horder hTH hbranch,
    fun _ hv hvorder => equality_layer_involution_fusion hnatural hz horder hv hvorder⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
