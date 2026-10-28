module

public import Theory.GroupTheory.PPrimeCoreReduction
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.SpecificGroups.PSL3Two.Cardinality
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# Three-prime cores of the even linear FF factors

An explicit cubic matrix shows that three divides the order of SL₂. Away
from the binary field its central quotient is simple and its scalar center
is trivial; at the binary field the order and trivial two-core suffice.
For SL₃, its scalar center has order dividing three, its central quotient
is simple, and the binary subgroup supplies three-divisibility. This proves
the core conclusion for all even fields, including the fields of odd degree
in the direct-product alternatives.

Source application: Aschbacher–Smith, combined 1 March 2004 manuscript,
B.5.6(1),(3),(5), printed p.105. The imported simplicity and order results
retain their ATLAS attribution; no classification premise is used here.
-/

public section
open Subgroup Matrix Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.SpecificGroups
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
omit [Finite F] [CharP F 2] in
theorem three_dvd_card_sl_two : 3 ∣ Nat.card SL(2,F) := by
  let g : SL(2,F) := ⟨!![0, -1; 1, -1], by simp [Matrix.det_fin_two]⟩
  have ho : orderOf g = 3 := by
    apply orderOf_eq_prime_iff.mpr
    constructor
    · apply Subtype.ext
      change (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
    · intro h
      have he := congrArg (fun a : SL(2,F) => a.val 0 0) h
      simp [g] at he
  exact ho ▸ orderOf_dvd_natCard g
theorem sl_two_threePrimeCore : pPrimeCore 3 SL(2,F) = ⊥ := by
  by_cases hc : Nat.card F = 2
  · apply pPrimeCore_eq_bot_of_card_dvd (p := 3) (q := 2) 1 1
      (by rw [Atlas.card_sl_two, hc]; norm_num)
      Atlas.RankOneFieldAutomorphisms.sl_twoCore_eq_bot
  · have hfour : 4 ≤ Nat.card F := by
      have ht := Finite.one_lt_card (α := F)
      let := Fintype.ofFinite F
      have hd : 2 ∣ Nat.card F := by
        rw [Nat.card_eq_fintype_card]
        exact (CharP.cast_eq_zero_iff F 2 _).mp (Nat.cast_card_eq_zero F)
      omega
    let := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := F) hfour
    let e : SL(2,F) ≃* PSL(2,F) :=
      ((QuotientGroup.quotientMulEquivOfEq
        Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot).trans QuotientGroup.quotientBot).symm
    let := e.isSimpleGroup_congr.mpr inferInstance
    exact pPrimeCore_eq_bot_of_simple (three_dvd_card_sl_two F)
omit [CharP F 2] in
theorem sl_three_center_isThreeGroup : IsPGroup 3 (center SL(3,F)) := by
  apply IsPGroup.of_card_dvd_pow (n := 1)
  rw [Atlas.ExceptionalSupport.card_sl_center]
  simpa using Nat.gcd_dvd_left 3 (Nat.card F - 1)
omit [Finite F] in
theorem three_dvd_card_sl_three : 3 ∣ Nat.card SL(3,F) := by
  let f := Matrix.SpecialLinearGroup.map (n := Fin 3) (ZMod.castHom (dvd_refl 2) F)
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    ext i j
    apply (ZMod.castHom (dvd_refl 2) F).injective
    exact congrArg (fun c : SL(3,F) => c.val i j) h
  have he := Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
  have hd := f.range.card_subgroup_dvd_card
  rw [← he, Matrix.PSL3Two.card_SL] at hd
  exact (by decide : 3 ∣ 168).trans hd
theorem sl_three_threePrimeCore : pPrimeCore 3 SL(3,F) = ⊥ := by
  let : IsQuasisimple SL(3,F) :=
    { toIsPerfect := Atlas.sl_perfect 3 (by decide)
      simple := Atlas.psl_simple_high_rank 3 (by decide) }
  exact IsQuasisimple.pPrimeCore_eq_bot (sl_three_center_isThreeGroup F) (three_dvd_card_sl_three F)
end Theory.SpecificGroups
