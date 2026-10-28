module

public import Theory.SpecificGroups.SU3.SylowOmega
public import Theory.GroupTheory.PGroup.HomocyclicFourRecognition
public import Mathlib.Tactic

/-!
# Homocyclic subgroups in binary Hermitian root coordinates

The subgroup where the first coordinate belongs to the fixed field is
abelian. Its square is the central element with second coordinate a².
The first-coordinate map has kernel the additive fixed field and is
surjective by the quadratic trace, so the subgroup has order q².
Frobenius squaring supplies square roots for every square-one element.
The finite abelian decomposition therefore constructs an isomorphism with
(C₄)ⁿ when q = 2ⁿ. Transport through any actual root-coordinate isomorphism
retains the entire involution layer.

Source: GLS4, Chapter 4, Lemma 3.4(d5), and Chapter 2 after Lemma 13.4;
Hermitian coordinate conventions from Huppert II.10.12.
-/

noncomputable section
open Subgroup BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.HomocyclicSlice
open BorelTorus.EvenCenterAction
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- The full inverse image of the fixed field under the first coordinate. -/
@[expose] public def slice : Subgroup (hermitianUnipotentCoord J) where
  carrier := {z | J.conj z.val.1 = z.val.1}
  one_mem' := map_zero _
  mul_mem' := by
    intro z w hz hw
    change J.conj (z.val.1 + w.val.1) = z.val.1 + w.val.1
    rw [map_add, hz, hw]
  inv_mem' := by
    intro z hz
    change J.conj (-z.val.1) = -z.val.1
    rw [map_neg, hz]

public instance : IsMulCommutative (slice J) := ⟨⟨fun z w => by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact add_comm _ _
  · change z.val.val.2 + w.val.val.2 - z.val.val.1 * J.conj w.val.val.1 =
      w.val.val.2 + z.val.val.2 - w.val.val.1 * J.conj z.val.val.1
    rw [z.property, w.property]
    ring⟩⟩

/-- The first coordinate, with its actual fixed-field codomain. -/
@[expose] public def first : slice J →* Multiplicative (fixedField J) where
  toFun z := .ofAdd ⟨z.val.val.1, z.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable [CharP E 2]

public theorem square_coordinates (z : slice J) :
    (z.val ^ 2).val = (0, z.val.val.1 ^ 2) := by
  rw [EvenInner.square_coordinates, z.property, pow_two]

public theorem pow_four (z : slice J) : z ^ 4 = 1 := by
  apply Subtype.ext
  have hz : (z.val ^ 2).val.1 = 0 := by rw [square_coordinates]
  simpa only [Subgroup.coe_pow, Subgroup.coe_one, ← pow_mul] using
    (EvenSemilinear.square_eq_one_iff_first_zero J (z.val ^ 2)).mpr hz

omit [CharP E 2] in
/-- All zero-first-coordinate elements lie in the slice. -/
public theorem zero_first_mem (z : hermitianUnipotentCoord J) (hz : z.val.1 = 0) : z ∈ slice J := by
  change J.conj z.val.1 = z.val.1
  rw [hz, map_zero]

/-- The entire coordinate center lies in the slice. -/
public theorem center_le [Finite E] {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n) :
    center (hermitianUnipotentCoord J) ≤ slice J := by
  rw [NormalizedRootCentralizers.coord_center J hn hcard hfixed]
  rintro _ ⟨b, rfl⟩
  exact zero_first_mem J _ rfl

/-- The first-coordinate kernel is the additive fixed field. -/
public def kernelEquiv : (first J).ker ≃* Multiplicative (fixedField J) where
  toFun x := .ofAdd ⟨x.val.val.val.2, by
    have hz : x.val.val.val.1 = 0 := congrArg (fun y => (y.toAdd : E)) x.property
    have hp := x.val.val.property
    rw [hz, zero_mul, add_zero] at hp
    exact (eq_neg_of_add_eq_zero_right hp).trans (CharTwo.neg_eq _)⟩
  invFun b := ⟨⟨centralCoord J b, zero_first_mem J _ rfl⟩, rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (congrArg (fun y => (y.toAdd : E)) x.property).symm
    · rfl
  right_inv _ := rfl
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    have hz : x.val.val.val.1 = 0 := congrArg (fun y => (y.toAdd : E)) x.property
    change x.val.val.val.2 + y.val.val.val.2 - x.val.val.val.1 * J.conj y.val.val.val.1 =
      x.val.val.val.2 + y.val.val.val.2
    rw [hz, zero_mul, sub_zero]

variable [Finite E] {q : ℕ}
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)

include hcard hfixed in
omit [CharP E 2] in
public theorem first_surjective : Function.Surjective (first J) := by
  intro a
  obtain ⟨z, hz⟩ := EvenSemilinear.coord_first_surjective J hcard hfixed (a.toAdd : E)
  change z.val.1 = (a.toAdd : E) at hz
  refine ⟨⟨z, ?_⟩, ?_⟩
  · change J.conj z.val.1 = z.val.1
    rw [hz]
    exact a.toAdd.property
  · apply Multiplicative.toAdd.injective
    exact Subtype.ext hz

include hcard hfixed in
public theorem card : Nat.card (slice J) = q ^ 2 := by
  have hker : Nat.card (first J).ker = q := by
    rw [Nat.card_congr (kernelEquiv J).toEquiv, Nat.card_congr Multiplicative.toAdd]
    exact hfixed
  have hi : (first J).ker.index = q := by
    rw [index_ker, MonoidHom.range_eq_top.mpr (first_surjective J hcard hfixed),
      Nat.card_congr Subgroup.topEquiv.toEquiv, Nat.card_congr Multiplicative.toAdd]
    exact hfixed
  rw [← (first J).ker.card_mul_index, hker, hi, pow_two]

include hcard hfixed in
/-- Frobenius squaring on the fixed field supplies every central square root. -/
public theorem square_root (x : slice J) (hx : x ^ 2 = 1) : ∃ y : slice J, y ^ 2 = x := by
  have hzero : x.val.val.1 = 0 := (EvenSemilinear.square_eq_one_iff_first_zero J x.val).mp
    (congrArg Subtype.val hx)
  have hfix : J.conj x.val.val.2 = x.val.val.2 := by
    have hp := x.val.property
    rw [hzero, zero_mul, add_zero] at hp
    exact (eq_neg_of_add_eq_zero_right hp).trans (CharTwo.neg_eq _)
  obtain ⟨a, ha⟩ := (Finite.surjective_of_injective
    (CharTwo.sq_injective (R := fixedField J))) ⟨x.val.val.2, hfix⟩
  obtain ⟨y, hy⟩ := first_surjective J hcard hfixed (.ofAdd a)
  refine ⟨y, ?_⟩
  have hay : y.val.val.1 = (a : E) := congrArg (fun z => (z.toAdd : E)) hy
  apply Subtype.ext
  apply Subtype.ext
  change (y.val ^ 2).val = x.val.val
  rw [square_coordinates, hay]
  exact Prod.ext hzero.symm (congrArg (fun z : fixedField J => (z : E)) ha)

include hcard hfixed in
/-- The fixed-first-coordinate slice is a genuine product of n cyclic fours. -/
public theorem homocyclic {n : ℕ} (hq : q = 2 ^ n) :
    Nonempty (slice J ≃* StandardHomocyclicCover (Fin n) 4) := by
  apply Theory.GroupTheory.homocyclicFour_of_square_roots (pow_four J)
    (square_root J hcard hfixed)
  rw [card J hcard hfixed, hq]
  calc
    (2 ^ n) ^ 2 = (2 ^ 2) ^ n := pow_right_comm 2 n 2
    _ = 4 ^ n := rfl

include hcard hfixed in
/-- Transport the slice into a specified group with actual root coordinates;
it contains every element of square one in that group. -/
public theorem exists_subgroup_of_equiv {H : Type*} [Group H]
    (e : H ≃* hermitianUnipotentCoord J) {n : ℕ} (hq : q = 2 ^ n) :
    ∃ R : Subgroup H, Nonempty (R ≃* StandardHomocyclicCover (Fin n) 4) ∧
      ∀ x : H, x ^ 2 = 1 → x ∈ R := by
  let R := (slice J).map e.symm.toMonoidHom
  refine ⟨R, ?_, ?_⟩
  · obtain ⟨f⟩ := homocyclic J hcard hfixed hq
    exact ⟨((slice J).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm.trans f⟩
  · intro x hx
    refine ⟨e x, zero_first_mem J (e x) ?_, e.symm_apply_apply x⟩
    apply (EvenSemilinear.square_eq_one_iff_first_zero J _).mp
    rw [← map_pow, hx, map_one]

end BenderSuzuki.MatrixGroups.HermitianForm.HomocyclicSlice
