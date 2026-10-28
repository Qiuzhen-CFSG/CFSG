module
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.CComponent.ProperQuotient

/-!
# Detecting nontrivial actions on component quotients

Let K be a normal C-component, B a nontrivial perfect proper subgroup of K,
and R a subgroup containing the embedded characteristic kernel N of K. If R
acts trivially on K/N, then [R,K] lies in N, so K normalizes R. When N_G(R)
normalizes B, this makes B subnormal in G, contradicting minimality of K.

The result retains the actual ambient conjugation map K → K/N and requires
no classification of K/N or lifting of automorphism normalizers.
Source application: Aschbacher--Smith, original 4.3.13--15, printed pp.617--618.
-/

public section
open Subgroup
open scoped commutatorElement

namespace Subgroup
variable {G : Type*} [Group G]

/-- A component cannot normalize a nontrivial proper perfect subgroup. -/
theorem IsCComponent.not_le_normalizer_of_perfect_lt {B K : Subgroup G}
    (hK : K.IsCComponent) (hBK : B < K) (hne : B ≠ ⊥) [Group.IsPerfect B] :
    ¬ K ≤ normalizer (B : Set G) := by
  intro hn
  have hnB : (B.subgroupOf K).Normal :=
    (normal_subgroupOf_iff_le_normalizer hBK.le).mpr hn
  have hs : B.IsSubnormal := by
    have hh := hnB.isSubnormal.trans' hK.subnormal
    simpa only [map_subgroupOf_eq_of_le hBK.le] using hh
  exact hBK.not_ge (hK.minimal B hBK.le hne inferInstance hs)

/-- Kernel containment makes the component normalize every subgroup with
trivial action on the quotient. -/
theorem le_normalizer_of_trivial_quotient_action
    (K R : Subgroup G) [K.Normal] (N : Subgroup K) [N.Characteristic]
    (hNR : N.map K.subtype ≤ R)
    (ha : R.map (normalQuotientAction K N) = ⊥) :
    K ≤ normalizer (R : Set G) := by
  apply le_normalizer_iff_commutator_le_right.mpr
  rw [commutator_comm]
  apply commutator_le.mpr
  intro r hr k hk
  have har : normalQuotientAction K N r = 1 :=
    mem_bot.mp (ha ▸ mem_map_of_mem _ hr)
  have he := DFunLike.congr_fun har (QuotientGroup.mk' N ⟨k,hk⟩)
  rw [normalQuotientAction_apply_mk] at he
  have hn : MulAut.conjNormal r (⟨k,hk⟩ : K) / ⟨k,hk⟩ ∈ N :=
    QuotientGroup.eq_iff_div_mem.mp he
  apply hNR
  exact ⟨_, hn, by simp [div_eq_mul_inv, commutatorElement_def]⟩

/-- The radical normalizer cannot preserve a smaller perfect subgroup of a
component if the radical acts trivially on the component quotient. -/
theorem IsCComponent.quotient_action_ne_bot
    {K B R : Subgroup G} [K.Normal] (hK : K.IsCComponent)
    (hBK : B < K) (hne : B ≠ ⊥) [Group.IsPerfect B]
    (N : Subgroup K) [N.Characteristic] (hNR : N.map K.subtype ≤ R)
    (hn : normalizer (R : Set G) ≤ normalizer (B : Set G)) :
    R.map (normalQuotientAction K N) ≠ ⊥ := by
  intro ha
  exact hK.not_le_normalizer_of_perfect_lt hBK hne
    ((le_normalizer_of_trivial_quotient_action K R N hNR ha).trans hn)
end Subgroup
