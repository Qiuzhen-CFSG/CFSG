module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationEquality
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionAssembly

/-!+# Equality extension assembly on the whole reduced layer

The conditional Chapter 6 extension argument applies to the literal whole
R₂(LT) layer. Its canonical closure and two-core remain inside C_G(z), and
its symmetric-five quotient marks the actual L by the same quotient map.
The order-four alternative is eliminated by the transfer theorem inside
the assembly, once the independent source fusion argument supplies its
three remaining premises.

The action, block and fusion calculations remain explicit source inputs.
This application does not assert their production or the final M₂₂ theorem.
Source: Aschbacher--Smith, 6.2.13 and 12.2.2(3d), printed pp.687--688,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
open Chapter6.M22Recognition.CentralizerExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ} {z : G}

/-- The actual reduced-module consumer, retaining the undischarged source
action, block and fusion inputs. -/
theorem reduced_equality_extension_of_action_block_fusion
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (hplus : Nonempty (QuaternionCentralProductData (equalityCore L (wholeReduced T L) z)))
    (hcenter : coreCenter (equalityCore L (wholeReduced T L) z) =
      (zpowers z).subgroupOf (centralizer ({z} : Set G)))
    (hact : EqualityExtensionAction (T : Subgroup G) L (wholeReduced T L) z)
    (hblock : EqualityExtensionBlock (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) z)
    (hfour : Nat.card (equalityCentralizer L (wholeReduced T L) z) = 4 →
      EqualityExtensionFourFusion (T : Subgroup G) L (wholeReduced T L) z) :
    ∃ hnormal : ((commutatorLayer T L).subgroupOf (normalizer (L : Set G))).Normal,
      @CompatibleSymmetricFiveQuotient (normalizer (L : Set G)) inferInstance
        ((commutatorLayer T L).subgroupOf (normalizer (L : Set G)))
        (L.subgroupOf (normalizer (L : Set G))) hnormal ∧
      CoreData (equalityCore L (wholeReduced T L) z) ∧
      equalityCentralizer L (wholeReduced T L) z = zpowers z ∧
      (L ⊔ (T : Subgroup G)).pCoreIn 2 = commutatorLayer T L := by
  exact A.equality_extension_of_action_block_fusion h611 hnatural hz horder hTH
    hplus hcenter hact hblock hfour

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
