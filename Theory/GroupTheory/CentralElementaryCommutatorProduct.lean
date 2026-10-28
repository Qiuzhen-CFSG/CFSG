module
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Theory.GroupTheory.Commutator.RelativeGeneration
/-!
# Central elementary commutators in commuting products

A commuting product inherits central elementary commutators from its two
factors. Each factor's central omega subgroup remains central in the join,
and relative normal generation bounds the commutator of the whole join.
Source application: Aschbacher--Smith 10.2.3(4), printed p.747.
-/
public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]
theorem omegaCenterIn_le_join_of_commuting (P Q : Subgroup G)
    (hc : P ≤ centralizer (Q : Set G)) : omegaCenterIn P ≤ omegaCenterIn (P ⊔ Q) := by
  intro x hx
  obtain ⟨hp,hpc,hx2⟩ := (mem_omegaCenterIn_iff P x).mp hx
  refine (mem_omegaCenterIn_iff _ _).mpr ⟨(le_sup_left : P ≤ P ⊔ Q) hp,?_,hx2⟩
  have hpx : P ≤ centralizer ({x} : Set G) := by
    intro p hp
    apply mem_centralizer_iff.mpr
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact (hpc p hp).symm
  have hqx : Q ≤ centralizer ({x} : Set G) := by
    intro q hq
    apply mem_centralizer_iff.mpr
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact (hc hp q hq).symm
  intro s hs
  exact ((sup_le hpx hqx) hs x (Set.mem_singleton x)).symm

theorem commutator_le_omegaCenterIn_join_of_commuting (P Q : Subgroup G)
    (hc : P ≤ centralizer (Q : Set G))
    (hP : ⁅P,P⁆ ≤ omegaCenterIn P) (hQ : ⁅Q,Q⁆ ≤ omegaCenterIn Q) :
    ⁅P ⊔ Q,P ⊔ Q⁆ ≤ omegaCenterIn (P ⊔ Q) := by
  let S := P ⊔ Q
  let Z := omegaCenterIn S
  have hn : S ≤ normalizer (Z : Set G) :=
    S.le_normalizer.trans (normalizer_le_normalizer_omegaCenterIn S)
  have hp : ⁅P,P⁆ ≤ Z := hP.trans (omegaCenterIn_le_join_of_commuting P Q hc)
  have hq : ⁅Q,Q⁆ ≤ Z := by
    simpa only [sup_comm] using hQ.trans
      (omegaCenterIn_le_join_of_commuting Q P (le_centralizer_iff.mp hc))
  have hpq : ⁅P,Q⁆ ≤ Z := (commutator_eq_bot_iff_le_centralizer.mpr hc).le.trans bot_le
  have hqp : ⁅Q,P⁆ ≤ Z := by rwa [commutator_comm]
  apply commutator_sup_le_of_relative_normal S P Q S Z hn le_sup_left le_sup_right
  · rw [commutator_comm]
    exact commutator_sup_le_of_relative_normal S P Q P Z hn le_sup_left le_sup_right hp hqp
  · rw [commutator_comm]
    exact commutator_sup_le_of_relative_normal S P Q Q Z hn le_sup_left le_sup_right hpq hq

end Subgroup
