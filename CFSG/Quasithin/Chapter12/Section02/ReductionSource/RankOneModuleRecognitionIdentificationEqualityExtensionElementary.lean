module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationEqualityExtension
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionElementary
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionResidual

/-!
# Equality core and centralizer calculations on the whole reduced layer

Apply the canonical pair construction to the literal R₂(LT) used in Chapter12.
It supplies the quaternion-product data for the actual P = O₂(⟨V^H⟩).
The core-action kernel, Sylow centralizer product, elementary Q and D, and
Q = O₂(M) now follow without action-output or block-output premises.
The residual calculation also gives C_M(V) = Q and H ∩ M = T.

These applications discharge the corresponding inputs to the extension
argument. The equality-geometry owner still has to construct the action
quotient, marked S₅ quotient and order-four fusion before applying the
published recognition endpoint.
Source: Aschbacher–Smith, 6.2.13 and 12.2.2(3d), printed pp.687–688,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
open Chapter6.M22Recognition.CentralizerExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ} {z : G}

/-- The actual central-quotient action kernel, with the extraspecial premise
constructed from the equality branch on the whole reduced layer. -/
theorem reduced_equality_core_action_kernel
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (hbranch : sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓
      commutatorLayer T L = ZS (T : Subgroup G) L (wholeReduced T L)) :
    let H := centralizer ({z} : Set G)
    let K := equalityLayerClosure L (wholeReduced T L) z
    let P := equalityCore L (wholeReduced T L) z
    centralizer (P : Set H) = centralizer (K : Set H) ∧
      (equalityOuterAction L (wholeReduced T L) z).ker = P ⊔ centralizer (K : Set H) ∧
      (equalityOuterAction L (wholeReduced T L) z).ker ≤ pCore 2 H ∧
      (equalityOuterAction L (wholeReduced T L) z).ker ⊓
        centralizer ((commutatorLayer T L).subgroupOf H : Set H) =
          (P ⊓ (commutatorLayer T L).subgroupOf H) ⊔ centralizer (K : Set H) := by
  have hp := A.equality_action_pair_data h611 hnatural hz horder hTH hbranch
  exact ⟨A.equality_core_centralizer h611 hnatural hz,
    A.equalityOuterAction_ker h611 hnatural hz hp.plusType,
    A.equalityOuterAction_ker_le h611 hnatural hz hp.plusType,
    A.equality_outer_kernel_layer_centralizer h611 hnatural hz hp.plusType⟩

/-- Elementary Q and D and the normal quotient kernel, with all pair and
centralizer-production premises discharged on the original Chapter12 setup. -/
theorem reduced_equality_elementary_core
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (hbranch : sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓
      commutatorLayer T L = ZS (T : Subgroup G) L (wholeReduced T L)) :
    let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
    let D := equalityCentralizer L (wholeReduced T L) z
    (T : Subgroup G) ⊓ centralizer (commutatorLayer T L : Set G) = commutatorLayer T L ⊔ D ∧
      IsElementaryAbelian 2 Q ∧ IsElementaryAbelian 2 D ∧
      Q = (normalizer (L : Set G)).pCoreIn 2 ∧
      (Q.subgroupOf (normalizer (L : Set G))).Normal ∧
      normalizer (Q : Set G) = normalizer (L : Set G) ∧
      D ≤ Q ∧ D ⊓ commutatorLayer T L = zpowers z := by
  have hp := A.equality_action_pair_data h611 hnatural hz horder hTH hbranch
  have hnormal := A.equality_local_core_normal h611 hnatural hz horder hTH hbranch
  exact ⟨A.equality_sylow_layer_centralizer h611 hnatural hz hTH hp.plusType,
    A.equality_local_core_elementary h611 hnatural hz horder hTH hbranch,
    A.equality_centralizer_elementary h611 hnatural hz horder hTH hbranch,
    A.equality_local_core_eq_maximal_core h611 hnatural hz horder hTH hbranch,
    hnormal, equality_local_core_normalizer h611 hnormal,
    A.equality_centralizer_le_local_core h611 hnatural hz hTH,
    A.equality_centralizer_inf_layer h611 hz hp.core_center⟩

/-- The local action kernel and residual on the whole reduced layer, removing
the residual obstruction before the marked S₅ quotient calculation. -/
theorem reduced_equality_local_residual
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (hbranch : sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓
      commutatorLayer T L = ZS (T : Subgroup G) L (wholeReduced T L)) :
    normalizer (L : Set G) ⊓ centralizer (commutatorLayer T L : Set G) =
        (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      pResidual 2 (centralizer ({z} : Set G) ⊓ normalizer (L : Set G) : Subgroup G) = ⊥ ∧
      centralizer ({z} : Set G) ⊓ normalizer (L : Set G) = (T : Subgroup G) := by
  exact ⟨A.equality_maximal_layer_centralizer h611 hnatural hz horder hTH hbranch,
    A.equality_intersection_residual_eq_bot h611 hnatural hz horder hTH hbranch,
    A.equality_intersection_eq_sylow h611 hnatural hz horder hTH hbranch⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
