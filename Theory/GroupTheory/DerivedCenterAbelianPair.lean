module
public import Theory.GroupTheory.AbelianQuotientFixedSubgroup
/-!
# The center of a normal abelian pair

When two normal abelian subgroups generate R, their intersection is
central and R′ lies in their intersection. If Z(R)≤R′, the intersection
is precisely Z(R). This preserves all central covering layers.

Source: the pair intersection in Aschbacher–Smith, Lemma 2.4.8(3),
printed pp.529–530.
-/
public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

theorem center_eq_intersection_of_derived_center_abelian_pair
    (R A B : Subgroup G) [IsMulCommutative A] [IsMulCommutative B]
    (hgen : A ⊔ B = R) (hnA : R ≤ normalizer (A : Set G))
    (hnB : R ≤ normalizer (B : Set G))
    (hcent : R ⊓ centralizer (R : Set G) ≤ ⁅R,R⁆) :
    A ⊓ B = R ⊓ centralizer (R : Set G) := by
  have hAR : A ≤ R := le_sup_left.trans_eq hgen
  have hBR : B ≤ R := le_sup_right.trans_eq hgen
  have hcomA : ⁅R,R⁆ ≤ A := by
    rw [←hgen]
    exact commutator_sup_le_of_normalized_derived A B (hBR.trans hnA)
      (by rw [commutator_self_eq_bot_iff.mpr inferInstance];exact bot_le)
  have hcomB : ⁅R,R⁆ ≤ B := by
    rw [←hgen,sup_comm A B]
    exact commutator_sup_le_of_normalized_derived B A (hAR.trans hnB)
      (by rw [commutator_self_eq_bot_iff.mpr inferInstance];exact bot_le)
  have hc : A ⊓ B ≤ centralizer (R : Set G) := by
    apply le_centralizer_iff.mp
    rw [←hgen]
    exact sup_le
      (le_centralizer_iff.mp (inf_le_left.trans (le_centralizer A)))
      (le_centralizer_iff.mp (inf_le_right.trans (le_centralizer B)))
  exact le_antisymm (le_inf (inf_le_left.trans hAR) hc)
    (hcent.trans (le_inf hcomA hcomB))
end Subgroup
