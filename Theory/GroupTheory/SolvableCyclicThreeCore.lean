module

public import Theory.GroupTheory.Fitting.Centralizer
public import Theory.GroupTheory.CyclicNormalCentralizer

/-!
# A nontrivial two-core from a cyclic three-core

A finite solvable {2,3}-group with cyclic three-core and a nonabelian
two-subgroup has nontrivial two-core. Otherwise its Fitting subgroup is
its cyclic three-core. The derived group centralizes that core and hence
lies in it by Fitting self-centralization. A two-subgroup must then be
abelian, since its derived group is also a three-group.

This is the elementary group-theoretic step preceding the PSL₃ fixed-space
argument in Aschbacher--Smith, 15.3.37, printed p.1135.
-/

public section
open Subgroup
namespace Theory.GroupTheory

/-- Cyclicity of the three-core forces a nontrivial two-core whenever a
solvable {2,3}-group contains a nonabelian two-subgroup. -/
theorem twoCore_ne_bot_of_solvable_cyclic_threeCore {G : Type*} [Group G] [Finite G]
    (hs : Group.IsSolvable G)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card G → p = 2 ∨ p = 3)
    [IsCyclic (pCore 3 G)] (P : Subgroup G) (hP : IsPGroup 2 P)
    (hPna : ¬ IsMulCommutative P) : pCore 2 G ≠ ⊥ := by
  intro htwo
  have hfit : fittingSubgroup G = pCore 3 G := by
    apply le_antisymm _ (pCore_le_fitting G 3)
    rw [fitting_eq_sup_pCore]
    refine iSup_le fun p => ?_
    rcases hprime p.val.val (Nat.prime_of_mem_primeFactors p.val.property)
      (Nat.dvd_of_mem_primeFactors p.val.property) with he | he
    · rw [he, htwo]
      exact bot_le
    · rw [he]
  have hc : centralizer (pCore 3 G : Set G) ≤ pCore 3 G := by
    rw [← hfit]
    exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hs
  have hd : _root_.commutator G ≤ pCore 3 G :=
    (commutator_le_centralizer_of_isCyclic_normal (pCore 3 G)).trans hc
  have hp3 : ⁅P, P⁆ ≤ pCore 3 G :=
    (commutator_mono (show P ≤ ⊤ from le_top) le_top).trans hd
  have hdis : Disjoint P (pCore 3 G) :=
    hP.disjoint_of_coprime pCore_isPGroup (by decide)
  apply hPna
  apply commutator_self_eq_bot_iff.mp
  exact le_bot_iff.mp ((le_inf (commutator_le_self P) hp3).trans hdis.le_bot)

end Theory.GroupTheory
