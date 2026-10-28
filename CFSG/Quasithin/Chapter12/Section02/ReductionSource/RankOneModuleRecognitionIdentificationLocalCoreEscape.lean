module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalCoreEscape
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalAction

/-!
# The terminal graph pair on the original Chapter 12 layer

Transport the graph pair and its common fixed point using the actual natural
module. A pair which is not a two-group cannot have its first layer in the point
centralizer core and its second layer centralizing that point. The normal
core join argument and conjugation exclude the original core containment. The existing count leaves orders four and eight.

The two-branch conclusion is conditional on the actual pair witness whose
construction remains in the 6.2.8 graph proof. It does not assert either the
full graph exclusion or the order-eight conclusion of 6.2.11.

Source: Aschbacher--Smith, last paragraph of 6.2.8, printed p.685,
applied to [R₂(LT),L] in 12.2.2(3d), printed p.795.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ} {z w : G}

/-- The literal graph pair removes the order-sixteen alternative in the
core count on the original whole-reduced layer. -/
theorem source_local_core_card_dichotomy_of_non_two_pair
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (g c : G) (hw : w ∈ (commutatorLayer T L).map (MulAut.conj g).toMonoidHom)
    (hw1 : w ≠ 1)
    (hc : ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj c).toMonoidHom ≤ centralizer ({w} : Set G))
    (hpair : ¬ IsPGroup 2 ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom ⊔
      ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj c).toMonoidHom : Subgroup G)) :
    Nat.card (commutatorLayer T L ⊓ (centralizer ({z} : Set G)).pCoreIn 2 : Subgroup G) = 4 ∨
    Nat.card (commutatorLayer T L ⊓ (centralizer ({z} : Set G)).pCoreIn 2 : Subgroup G) = 8 :=
  local_core_card_dichotomy_of_non_two_pair h611 hnatural hz ho hT g c hw hw1 hc hpair

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
