module
public import Theory.GroupTheory.Commutator.NormalSpan
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# Displacement of a conjugate span by an actor normal modulo a kernel

If H centralizes D modulo Q and Q is H-invariant, then H normalizes QD.
Bounds on the commutators of a seed A with Q and D therefore propagate
to its full H-conjugate span, provided the bound Z is preserved by the
actors. All normality is relative to the displayed subgroups.

This supplies the neighborhood displacement step of DGS,
*Groups and Graphs* (1985), 9.10(3), printed p.148.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

theorem commutator_conjugateSpanBy_le_of_normal_modulo
    (A H Q D Z : Subgroup G)
    (hAH : A ≤ H) (hQH : Q ≤ H)
    (hHQ : H ≤ normalizer (Q : Set G))
    (hHZ : H ≤ normalizer (Z : Set G))
    (hDZ : D ≤ normalizer (Z : Set G))
    (hHD : ⁅H,D⁆ ≤ Q) (hAQ : ⁅A,Q⁆ ≤ Z) (hAD : ⁅A,D⁆ ≤ Z) :
    ⁅conjugateSpanBy A H,D⁆ ≤ Z := by
  let K := Q ⊔ D
  have hHK : H ≤ normalizer (K : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact commutator_sup_le_of_relative_normal K Q D H K K.le_normalizer
      le_sup_left le_sup_right
      ((le_normalizer_iff_commutator_le_left.mp hHQ).trans le_sup_left)
      ((commutator_comm D H).trans_le (hHD.trans le_sup_left))
  have hKZ : K ≤ normalizer (Z : Set G) := sup_le (hQH.trans hHZ) hDZ
  have hAK : ⁅A,K⁆ ≤ Z := by
    rw [commutator_comm]
    exact commutator_sup_le_of_relative_normal K Q D A Z hKZ le_sup_left le_sup_right
      ((commutator_comm Q A).trans_le hAQ) ((commutator_comm D A).trans_le hAD)
  apply (commutator_mono le_rfl (show D ≤ K from le_sup_right)).trans
  rw [commutator_conjugateSpanBy_of_normalized_right A H K hAH hHK]
  exact conjugateSpanBy_le hAK hHZ
end Subgroup
