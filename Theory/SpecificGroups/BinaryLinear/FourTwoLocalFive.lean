module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Binary four-space two-locals have no factor five

An element of order five fixes only zero on binary four-space: orbit counting
makes the fixed-space cardinality congruent to sixteen modulo five. The same
count on an invariant subspace rules out every nonzero proper subspace.
A nontrivial two-subgroup has such a fixed space, which its normalizer preserves.
Consequently that normalizer has order prime to five.

This supplies the PSL₄(2) and A₈ exclusions in Aschbacher–Smith 13.5.15,
printed p.921, without a subgroup catalogue or any module-identification premise.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace BinaryLinear.FourTwoLocalFive
open OuterCyclic

private instance : Finite (LinearGroup 4) :=
  Finite.of_equiv (Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) (matrixEquivLinear 4).toEquiv

private theorem fixedSpace_card_one (Q : Subgroup (LinearGroup 4))
    (hQ : IsPGroup 5 Q) (hQ0 : Q ≠ ⊥) : Nat.card (fixedSpace Q) = 1 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have he : MulAction.fixedPoints Q (Space 4) = (fixedSpace Q : Set (Space 4)) := by
    ext v
    rw [MulAction.mem_fixedPoints]
    change (∀ q : Q, q.val v = v) ↔ ∀ q ∈ Q, q v = v
    exact ⟨fun h q hq => h ⟨q, hq⟩, fun h q => h q.val q.property⟩
  have hc := hQ.card_modEq_card_fixedPoints (Space 4)
  rw [he] at hc
  change Nat.card (Space 4) ≡ Nat.card (fixedSpace Q) [MOD 5] at hc
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Space 4),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace Q)] at hc
  norm_num [Space] at hc
  have hd := Submodule.finrank_lt (fixedSpace_ne_top hQ0)
  norm_num [Space] at hd
  have hd0 : Module.finrank (ZMod 2) (fixedSpace Q) = 0 := by
    interval_cases hh : Module.finrank (ZMod 2) (fixedSpace Q) <;>
      first | rfl | norm_num [Nat.ModEq, hh] at hc
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hd0, pow_zero]

private abbrev invariantAction (Q : Subgroup (LinearGroup 4))
    (W : Submodule (ZMod 2) (Space 4)) (hW : Q ≤ parabolic W) : MulAction Q W where
  smul q w := ⟨q.val w.val, (hW q.property w.val).mpr w.property⟩
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl

/-- Every proper nonzero geometric parabolic in binary four-space has order
prime to five. -/
theorem five_not_dvd_parabolic (W : Submodule (ZMod 2) (Space 4))
    (hW : W ≠ ⊥) (hWt : W ≠ ⊤) : ¬ 5 ∣ Nat.card (parabolic W) := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro hfive
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 5 hfive
  let Q : Subgroup (LinearGroup 4) := zpowers g.val
  have hQc : Nat.card Q = 5 := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective (parabolic W).subtype Subtype.val_injective g).trans hg
  have hQ : IsPGroup 5 Q := IsPGroup.of_card (n := 1) (by simpa using hQc)
  have hQ0 : Q ≠ ⊥ := by
    intro he
    rw [he, Subgroup.card_bot] at hQc
    omega
  have hQP : Q ≤ parabolic W := zpowers_le.mpr g.property
  let : MulAction Q W := invariantAction Q W hQP
  let toFixed : MulAction.fixedPoints Q W → fixedSpace Q := fun x =>
    ⟨x.val.val, fun q hq => congrArg Subtype.val
      ((MulAction.mem_fixedPoints.mp x.property) ⟨q, hq⟩)⟩
  have hinj : Function.Injective toFixed := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : fixedSpace Q => x.val) he
  have hle := Nat.card_le_card_of_injective toFixed hinj
  rw [fixedSpace_card_one Q hQ hQ0] at hle
  have hz : (0 : W) ∈ MulAction.fixedPoints Q W := by
    rw [MulAction.mem_fixedPoints]
    intro q
    apply Subtype.ext
    exact q.val.map_zero
  let : Nonempty (MulAction.fixedPoints Q W) := ⟨⟨0, hz⟩⟩
  have hcard : Nat.card (MulAction.fixedPoints Q W) = 1 := by
    have := Nat.card_pos (α := MulAction.fixedPoints Q W)
    omega
  have hc := hQ.card_modEq_card_fixedPoints W
  rw [hcard, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  have hpos : 0 < Module.finrank (ZMod 2) W :=
    Nat.pos_of_ne_zero (fun hz => hW (Submodule.finrank_eq_zero.mp hz))
  have hlt := Submodule.finrank_lt hWt
  rw [Module.finrank_fin_fun] at hlt
  interval_cases hd : Module.finrank (ZMod 2) W <;> norm_num [Nat.ModEq] at hc

/-- The normalizer of a nonidentity two-subgroup of GL₄(2) has order prime
to five. -/
theorem five_not_dvd_normalizer (Q : Subgroup (LinearGroup 4))
    (hQ : IsPGroup 2 Q) (hQ0 : Q ≠ ⊥) :
    ¬ 5 ∣ Nat.card (normalizer (Q : Set (LinearGroup 4))) := by
  intro hd
  apply five_not_dvd_parabolic (fixedSpace Q)
    (fixedSpace_ne_bot (by norm_num [Space, Nat.card_fun]) hQ) (fixedSpace_ne_top hQ0)
  exact hd.trans (card_dvd_of_le (normalizer_le_parabolic_fixedSpace Q))

end BinaryLinear.FourTwoLocalFive
end
