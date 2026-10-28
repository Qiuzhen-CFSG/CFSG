module

public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms
public import Theory.SpecificGroups.PSL2.RankOneRoots
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.GroupTheory.CComponent.TwoComponent.Involution

/-!
# Involution fixed groups in odd-degree binary PSL₂

Every outer involution forces even field degree by the proved semilinear
classification and fixed-field descent. Thus an involutory automorphism over
GF(2ⁿ), for odd n ≥ 3, is inner. The canonical SL₂–PSL₂ equivalence proves
centerlessness, so its conjugating element is an involution. The explicit
root-centralizer calculation makes its whole fixed group a two-group.
Consequently every involution fixed group is solvable and has no two-components.

The case n = 3 is used for the actual small Ree derived carrier after its
exceptional isomorphism is constructed. Sources: GLS II Definition 2.4;
GLS III §§2.2 and 2.5; Aschbacher–Smith 16.1.4 and 16.1.6, printed
pp.1171–1172, for the imported root-centralizer calculation.
-/

public section

open Subgroup
namespace Theory.PSL2

theorem odd_binary_fixed_solvable {n : ℕ} (hn : 2 ≤ n) (ho : Odd n)
    (a : MulAut (BinaryGroup n)) (ha : orderOf a = 2) :
    _root_.Group.IsSolvable a.fixedSubgroup := by
  have hi : a ∈ inner (BinaryField n) := by
    by_contra h
    exact (Nat.not_even_iff_odd.mpr ho)
      (outer_involution_halfFrobenius hn a
        (by simpa only [ha] using pow_orderOf_eq_one a) h).1
  obtain ⟨x, rfl⟩ := (mem_inner_iff _ _).mp hi
  have hc : center (BinaryGroup n) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have h := (centerCongr (sl2QuotientEquiv (BinaryField n)).symm ⟨x, hx⟩).property
    have h1 := mem_bot.mp ((le_of_eq (sl2_center_eq_bot (BinaryField n))) h)
    change (sl2QuotientEquiv (BinaryField n)).symm x = 1 at h1
    exact (sl2QuotientEquiv (BinaryField n)).symm.injective (h1.trans (map_one _).symm)
  have hx : orderOf x = 2 :=
    (MulAut.conj_orderOf_of_center_eq_bot hc x).symm.trans ha
  rw [MulAut.fixedSubgroup_conj]
  obtain ⟨_, _, _, _, _, hp⟩ := involution_root_geometry x hx
  let : _root_.Group.IsNilpotent (centralizer ({x} : Set (BinaryGroup n))) := hp.isNilpotent
  infer_instance

theorem odd_binary_hasInvolutoryB2 {n : ℕ} (hn : 2 ≤ n) (ho : Odd n) :
    Theory.GroupTheory.HasInvolutoryB2 (BinaryGroup n) :=
  Theory.GroupTheory.HasInvolutoryB2.of_fixed_solvable (odd_binary_fixed_solvable hn ho)

end Theory.PSL2
