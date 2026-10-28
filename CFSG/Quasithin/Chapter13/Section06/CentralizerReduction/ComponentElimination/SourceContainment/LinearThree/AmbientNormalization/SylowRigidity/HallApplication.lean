module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.AmbientNormalization.SylowRigidity
public import Theory.GroupTheory.Hall.SylowSupplementRigidity

/-!
# The Hall-conjugacy input to A.3.6 Sylow rigidity

The general coprime-supplement theorem discharges the Hall premise in the
normal-cover application. The actual quotient image of D, all containment
and radical-supplement hypotheses, and the cubic quotient of Lᵥ are retained.
Only the A.3.6 conclusion and its Fitting fixed-point bound remain as
independent source inputs; this module does not assert either input.

Source: Aschbacher–Smith, A.3.6, printed pp.43–45, and the normalization
reduction used for 13.6.20, printed p.931.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.AmbientNormalization.SylowRigidity
open ComponentSelection Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal normal-cover application with the Hall-conjugacy premise discharged. -/
theorem normalizes_of_A36_fixed_points
    (K L T : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (D : Subgroup (plusActor K L T v)) (hD : D.IsCComponent)
    (hKD : K.subgroupOf (plusActor K L T v) ≤ D)
    (hLD : Lv L v ≤ D.map (plusActor K L T v).subtype)
    (hgen : solvableRadical D ⊔
      (K.subgroupOf (plusActor K L T v)).subgroupOf D = ⊤)
    (hc : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (ha : A36Conclusion
      (D.map (QuotientGroup.mk' (pCore 2 (plusActor K L T v)))))
    (hfixed : let C := D.map (QuotientGroup.mk' (pCore 2 (plusActor K L T v)))
      ∀ S : Sylow 2 C, fittingSubgroup C ⊓ centralizer (S : Set C) ≤ center C)
    : Lv L v ≤ normalizer (K : Set G) := by
  exact normalizes_of_A36_fixed_points_and_hall K L T z v hK hSyl hn hL D hD hKD hLD
    hgen hc ha hfixed normalizes_of_nilpotent_supplement_of_sylow_fixed_points

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.AmbientNormalization.SylowRigidity
