module
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Normalizing a centralizer from displacement modulo a central layer

If P normalizes Q and Z, Q centralizes Z, and [A,P] lies in Z, then P
normalizes C_Q(A). Indeed P normalizes AZ and C_Q(A)=C_Q(AZ).
All normality is relative to the named actors; no ambient normality or
finiteness is needed.

Source application: the literal T0=C_Q(U_d intersect B) in MS93 (5.9),
printed p.920, through Sp4Four.DistanceReduction.StrictIndex.Kernel.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- A central error layer absorbs displacement of a seed under an actor. -/
theorem normalizes_sup_of_displacement (P A Z : Subgroup G)
    (hPZ : P ≤ normalizer Z) (hAP : ⁅A,P⁆ ≤ Z) :
    P ≤ normalizer ((A ⊔ Z : Subgroup G) : Set G) :=
  le_normalizer_iff_commutator_le_left.mpr
    (commutator_sup_le_of_relative_normal (A ⊔ Z) A Z P (A ⊔ Z)
      (A ⊔ Z).le_normalizer le_sup_left le_sup_right
      (hAP.trans le_sup_right)
      ((le_normalizer_iff_commutator_le_left.mp hPZ).trans le_sup_right))

/-- Changing the seed by a layer centralized by Q preserves its centralizer
in Q. The actor need not normalize the seed itself. -/
theorem normalizes_inf_centralizer_of_displacement
    (P Q A Z : Subgroup G)
    (hPQ : P ≤ normalizer Q) (hPZ : P ≤ normalizer Z)
    (hQZ : Q ≤ centralizer (Z : Set G)) (hAP : ⁅A,P⁆ ≤ Z) :
    P ≤ normalizer ((Q ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
  have hPN := normalizes_sup_of_displacement P A Z hPZ hAP
  have he : Q ⊓ centralizer (A : Set G) =
      Q ⊓ centralizer ((A ⊔ Z : Subgroup G) : Set G) := by
    apply le_antisymm (le_inf inf_le_left ?_)
      (inf_le_inf_left _ (centralizer_le
        (show (A : Set G) ⊆ (A ⊔ Z : Subgroup G) from
          fun _ hx => (show A ≤ A ⊔ Z from le_sup_left) hx)))
    apply le_centralizer_iff.mp
    exact sup_le (le_centralizer_iff.mp inf_le_right)
      (le_centralizer_iff.mp (inf_le_left.trans hQZ))
  rw [he]
  exact (le_inf hPQ (hPN.trans (normalizer_le_normalizer_centralizer _))).trans
    inf_normalizer_le_normalizer_inf
end Subgroup
