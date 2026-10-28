module

public import Theory.GroupTheory.OddIndexTwoCore
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# Orders of the fifteen-point subgroups in PSL₄(2) and A₇

Odd index and the actual quotient H/O₂(H) ≅ PSL₃(2) force index fifteen.
For PSL₄(2), the subgroup and two-core orders are 1344 and eight. For A₇,
the two-core is trivial, yielding an actual isomorphism H ≅ PSL₃(2).
The argument uses the proved orders 20160, 2520 and 168 and the power-of-two
order of the intrinsic core. It does not assert two-transitivity.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.4.12(2), printed p.97 of `refs/quasithin.pdf`. The imported ATLAS
exceptional comparison retains its attribution and license.
-/

public section
open scoped MatrixGroups

namespace FifteenPointSubgroups
variable {G : Type*} [Group G] [Finite G]

theorem psl4_orders (e : G ≃* PSL(4, ZMod 2)) (H : Subgroup G)
    (hodd : Odd H.index)
    (hquot : Nonempty ((H ⧸ pCore 2 H) ≃* PSL(3, ZMod 2))) :
    H.index = 15 ∧ Nat.card (pCore 2 H) = 8 ∧ Nat.card H = 1344 := by
  obtain ⟨f⟩ := hquot
  have hq : Nat.card (H ⧸ pCore 2 H) = 168 :=
    (Nat.card_congr f.toEquiv).trans Matrix.PSL3Two.card_PSL
  have hG : Nat.card G = 168 * 2 ^ 3 * 15 := by
    rw [Nat.card_congr e.toEquiv, Atlas.Order20160A8.psl4Two_card]
    decide
  obtain ⟨hi, hc⟩ := H.index_and_card_twoCore_of_odd hG (by decide) (by decide) hodd hq
  refine ⟨hi, hc, ?_⟩
  have ht := H.card_mul_index
  rw [hG, hi] at ht
  omega

theorem alternating7_orders (e : G ≃* alternatingGroup (Fin 7)) (H : Subgroup G)
    (hodd : Odd H.index)
    (hquot : Nonempty ((H ⧸ pCore 2 H) ≃* PSL(3, ZMod 2))) :
    H.index = 15 ∧ pCore 2 H = ⊥ ∧ Nat.card H = 168 := by
  obtain ⟨f⟩ := hquot
  have hq : Nat.card (H ⧸ pCore 2 H) = 168 :=
    (Nat.card_congr f.toEquiv).trans Matrix.PSL3Two.card_PSL
  have hG : Nat.card G = 168 * 2 ^ 0 * 15 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card,
      card_alternatingGroup, Fintype.card_fin]
    decide
  obtain ⟨hi, hc⟩ := H.index_and_card_twoCore_of_odd hG (by decide) (by decide) hodd hq
  refine ⟨hi, Subgroup.card_eq_one.mp hc, ?_⟩
  have ht := H.card_mul_index
  rw [hG, hi] at ht
  omega
/-- In the alternating case the quotient marking lifts through the trivial core. -/
theorem alternating7_equiv (e : G ≃* alternatingGroup (Fin 7))
    (H : Subgroup G) (hodd : Odd H.index)
    (hquot : Nonempty ((H ⧸ pCore 2 H) ≃* PSL(3, ZMod 2))) :
    Nonempty (H ≃* PSL(3, ZMod 2)) := by
  have hc := (alternating7_orders e H hodd hquot).2.1
  obtain ⟨f⟩ := hquot
  exact ⟨QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hc.symm).trans f)⟩


end FifteenPointSubgroups
