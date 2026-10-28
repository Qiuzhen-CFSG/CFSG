module
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.ThreeSubgroups

/-!
# Reciprocal movement identifies the fixed subgroup of a supplement

Suppose E Q = A, Q/(Q ∩ N) is abelian and fully moved by A, and
Q ∩ N centralizes V. If [V,Q] is fixed by A, three-subgroups rotation
shows that C_V(E) centralizes [Q,E]. Generation modulo Q ∩ N then
makes it centralize Q and hence A. Thus C_V(E) = C_V(A).

All normality is relative to A. In particular N need not lie in Q.
The source application is the actual pair of critical centers and the
second-kernel section in DGS85 (12.6), printed p.183, supplied in
CommutingThreeProfile.SuzukiCenterFixed.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- Rotation identifies fixed points of a generating supplement under full reciprocal movement. -/
theorem centralizer_seed_eq_of_reciprocal_movement (A E Q V N Z : Subgroup G)
    (hgen : E ⊔ Q = A) (hAQ : A ≤ normalizer (Q : Set G))
    (hAN : A ≤ normalizer (N : Set G))
    (hQQ : ⁅Q,Q⁆ ≤ N) (hNV : Q ⊓ N ≤ centralizer (V : Set G))
    (hVQ : ⁅V,Q⁆ ≤ Z) (hZA : Z ≤ centralizer (A : Set G))
    (hmove : Q ≤ ⁅Q,A⁆ ⊔ (Q ⊓ N)) :
    V ⊓ centralizer (E : Set G) = V ⊓ centralizer (A : Set G) := by
  let C := V ⊓ centralizer (E : Set G)
  have hEA : E ≤ A := hgen ▸ le_sup_left
  have hQA : Q ≤ A := hgen ▸ le_sup_right
  have h1 : ⁅⁅C,Q⁆,E⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (((commutator_mono inf_le_left le_rfl).trans hVQ).trans
      (hZA.trans (centralizer_le hEA)))
  have h2 : ⁅⁅E,C⁆,Q⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp
      (show C ≤ centralizer (E : Set G) from inf_le_right)),commutator_bot_left]
  have h3 : ⁅⁅Q,E⁆,C⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h2 h1
  have hN : A ≤ normalizer (↑(Q ⊓ N) : Set G) :=
    (le_inf hAQ hAN).trans inf_normalizer_le_normalizer_inf
  let D := ⁅Q,E⁆ ⊔ (Q ⊓ N)
  have hAD : A ≤ normalizer (D : Set G) := by
    have hAC : A ≤ normalizer (↑(⁅Q,E⁆) : Set G) := by
      rw [←hgen]
      exact sup_le (normalizer_commutator_ge_right Q E) (normalizer_commutator_ge_left Q E)
    exact (le_inf hAC hN).trans (normalizer_inf_normalizer_le_normalizer_sup ⁅Q,E⁆ (Q ⊓ N))
  have hQD : ⁅Q,A⁆ ≤ D := by
    rw [commutator_comm,←hgen]
    apply commutator_sup_le_of_relative_normal A E Q Q D hAD hEA hQA
    · rw [commutator_comm]; exact le_sup_left
    · exact (le_inf (commutator_le_self Q) hQQ).trans le_sup_right
  have hQC : Q ≤ centralizer (C : Set G) := by
    have hbound : Q ≤ D := hmove.trans (sup_le hQD le_sup_right)
    exact hbound.trans (sup_le (commutator_eq_bot_iff_le_centralizer.mp h3)
      (hNV.trans (centralizer_le inf_le_left)))
  apply le_antisymm ?_ (inf_le_inf_left V (centralizer_le hEA))
  exact le_inf inf_le_left (le_centralizer_iff.mp (by
    rw [←hgen]
    exact sup_le (le_centralizer_iff.mp inf_le_right) hQC))
end Subgroup
