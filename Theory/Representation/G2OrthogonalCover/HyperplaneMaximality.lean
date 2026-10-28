module

public import Theory.Representation.G2OrthogonalCover.HyperplaneActions
public import Theory.GroupAction.PrimitivePrimeFixedPoint

/-!
# Maximal stabilizers in the norm-zero cover hyperplane orbit

The derived word BAA induces an order-seven permutation fixing exactly one
of the 36 hyperplanes. A block containing that point has size one modulo
seven and size dividing 36, so it is a singleton or the whole orbit.

Source: Aschbacher--Smith, Lemma 12.4.8, printed p.815. This proves the
required maximality directly in the intended orbit action, without an
additional identification of its order-168 stabilizer with PSL₂(7).
-/

@[expose] public noncomputable section
namespace Atlas.G2.Natural.OrthogonalCover.Hyperplanes

local notation "F" => ZMod 2
local notation "D" => commutator (Model F)

private def seven : D := binaryB F * binaryA F * binaryA F
private def stepSeven (a : Parameters) : Parameters := stepB (stepA (stepA a))

private theorem act_seven (a : Parameters) : act seven.val a = stepSeven a := by
  simp only [seven, Subgroup.coe_mul, act_mul, act_binaryA, act_binaryB, stepSeven]

private theorem act_seven_pow (n : ℕ) (a : Parameters) :
    act (seven.val ^ n) a = (stepSeven^[n]) a := by
  induction n with
  | zero => exact act_one a
  | succ n ih =>
    rw [pow_succ', act_mul, act_seven, ih, Function.iterate_succ_apply']

set_option maxRecDepth 16384 in
private theorem seven_period : ∀ a : Parameters, (stepSeven^[7]) a = a := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem seven_fixed : ∀ a : Parameters, normClass a = 0 →
    (stepSeven a = a ↔ a = 0) := by
  decide +kernel

private def baseZero : Fibre 0 := ⟨0, by decide +kernel⟩

instance derived_primitive_zero : MulAction.IsPreprimitive D (Fibre 0) := by
  apply MulAction.isPreprimitive_of_unique_fixed_prime 7 (by decide) seven baseZero
  · change (MulAction.toPermHom D (Fibre 0) seven) ^ 7 = 1
    rw [← map_pow]
    apply Equiv.ext
    intro a
    apply Subtype.ext
    change act (seven ^ 7).val a.val = a.val
    rw [Subgroup.coe_pow, act_seven_pow, seven_period]
  · intro a
    constructor
    · intro he
      apply Subtype.ext
      apply (seven_fixed a.val a.property).mp
      exact (act_seven a.val).symm.trans (congrArg Subtype.val he)
    · rintro rfl
      apply Subtype.ext
      change act seven.val 0 = 0
      rw [act_seven]
      exact (seven_fixed 0 (by decide +kernel)).mpr rfl
  · intro n hn hm
    rw [card_fibre_zero] at hn ⊢
    have hnle : n ≤ 36 := Nat.le_of_dvd (by decide) hn
    exact (by decide +kernel : ∀ k : Fin 37,
      k.val ∣ 36 → k.val % 7 = 1 % 7 → k.val = 1 ∨ k.val = 36)
        ⟨n, by omega⟩ hn hm

instance : Nontrivial (Fibre 0) :=
  ⟨⟨⟨0, by decide +kernel⟩, ⟨![1,0,0,0,0,0], by decide +kernel⟩,
    by decide +kernel⟩⟩

/-- Actual derived-group stabilizers in the orbit of length 36 are maximal. -/
theorem isCoatom_derived_stabilizer_zero (a : Fibre 0) :
    IsCoatom (MulAction.stabilizer D a) :=
  MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive D a

end Atlas.G2.Natural.OrthogonalCover.Hyperplanes
