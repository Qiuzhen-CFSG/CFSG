module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.RankComparison
public import Theory.SpecificGroups.SL2.SylowConsequences

/-!
# The elementary Sylow subgroups in the binary rank-one actor

The upper-unipotent Sylow subgroup is the additive field, so every Sylow
has order 2ⁿ and exponent two. Consequently an actual binary SL₂ actor
cannot contain an element of order four. If its Sylow has order four,
the field has four elements and the established exceptional isomorphism
gives the actual A₅ identification.

Source: the PSL₂(2ⁿ) branch of the B.5.1/F.6.18 comparison in
Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.68,
printed pp.1154–1155.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

/-- Every actual Sylow two-subgroup of the binary SL₂ model is elementary. -/
theorem linearTwo_sylow_elementary (F : BinaryField) (S : Sylow 2 SL(2,F.Carrier)) :
    IsElementaryAbelian 2 S := by
  let e := Matrix.SpecialLinearGroup.sylowEquivAdditive F.Carrier 2 S
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
  · intro x y
    apply e.symm.injective
    simp only [map_mul, mul_comm]
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply e.symm.injective
    rw [map_pow, map_one]
    change Multiplicative.ofAdd (2 • (e.symm x).toAdd) = Multiplicative.ofAdd 0
    congr 1
    simpa only [two_nsmul] using CharTwo.add_self_eq_zero (e.symm x).toAdd

/-- The actual field equivalence gives the exact Sylow order. -/
theorem linearTwo_sylow_card (F : BinaryField) (S : Sylow 2 SL(2,F.Carrier)) :
    Nat.card S = 2 ^ F.degree := by
  rw [← Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F.Carrier 2 S).toEquiv]
  exact F.card_eq

/-- The order-four test excludes every binary rank-one actor. -/
theorem linearTwo_no_order_four (F : BinaryField) (x : SL(2,F.Carrier)) :
    orderOf x ≠ 4 := by
  intro hx
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_zpowers, hx]
    decide)
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  let : IsElementaryAbelian 2 S := linearTwo_sylow_elementary F S
  have hs := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := (S : Subgroup SL(2,F.Carrier))) x (hS (mem_zpowers x))
  have hd := orderOf_dvd_of_pow_eq_one hs
  rw [hx] at hd
  norm_num at hd

/-- A four-element Sylow in the given rank-one actor forces the actual
A₅ model through a field equivalence, not by order recognition. -/
theorem linearTwo_alternatingFive_of_sylow_four
    {D : Type*} [Group D] [Finite D] (F : BinaryField)
    (e : D ≃* SL(2,F.Carrier)) (S : Sylow 2 D) (hS : Nat.card S = 4) :
    F.degree = 2 ∧ Nonempty (D ≃* alternatingGroup (Fin 5)) := by
  let P : Sylow 2 SL(2,F.Carrier) := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hp : Nat.card P = 4 := by
    change Nat.card ((S : Subgroup D).map e.toMonoidHom) = 4
    rw [card_map_of_injective e.injective, hS]
  have hn : F.degree = 2 := by
    have hh := (linearTwo_sylow_card F P).symm.trans hp
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hh
  let : Fintype F.Carrier := Fintype.ofFinite _
  let : Fintype BinaryField.four.Carrier := Fintype.ofFinite _
  let f : F.Carrier ≃+* BinaryField.four.Carrier := FiniteField.ringEquivOfCardEq (by
    simp only [← Nat.card_eq_fintype_card, F.card_eq, BinaryField.card_eq, hn]
    rfl)
  exact ⟨hn, ⟨e.trans ((Atlas.fieldEquivSL 2 f).trans alternatingFiveLinearEquiv.symm)⟩⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
