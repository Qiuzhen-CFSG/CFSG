module

public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# A generalized Fitting subgroup of order three

Self-centralization identifies the centralizer of the cyclic generalized
Fitting subgroup with that subgroup. Conjugation into its automorphism group
of order two makes the ambient order divide six. Its two-core is trivial
because it lies in both the cyclic three-group and a two-group.

Source application: the PSL₂(2)' case of Aschbacher–Smith C.1.17, p.126.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem card_dvd_six_and_twoCore_eq_bot_of_generalizedFitting_card_three (hc : Nat.card (generalizedFitting G) = 3) :
    Nat.card G ∣ 6 ∧ pCore 2 G = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let L := generalizedFitting G
  let : IsCyclic L := isCyclic_of_prime_card hc
  let : IsMulCommutative L := IsCyclic.isMulCommutative
  have hCL : centralizer (L : Set G) = L := le_antisymm
    (centralizer_generalizedFitting_le G) (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  let a : G →* MulAut L := MulAut.conjNormal
  have ha : a.ker = L := by rw [MulAut.conjNormal_ker_eq_centralizer,hCL]
  have hAut : Nat.card (MulAut L) = 2 := by rw [IsCyclic.card_mulAut,hc]; decide
  have hd : a.ker.index ∣ 2 := by rw [index_ker,← hAut]; exact a.range.card_subgroup_dvd_card
  have hcard : Nat.card G ∣ 6 := by
    have hm := a.ker.card_mul_index
    rw [ha,hc] at hm
    rw [← hm]
    simpa only [ha] using Nat.mul_dvd_mul_left 3 hd
  refine ⟨hcard,?_⟩
  have hO : pCore 2 G ≤ L := (pCore_le_fitting G 2).trans (fitting_le_generalizedFitting G)
  have hL3 : IsPGroup 3 L := IsPGroup.of_card (n := 1) (by simpa using hc)
  have hd := pCore_isPGroup.disjoint_of_coprime hL3 (by decide : Nat.Coprime 2 3)
  exact le_bot_iff.mp ((le_inf le_rfl hO).trans hd.le_bot)
end Theory.GroupTheory
