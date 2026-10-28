module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

/-!
# Counting conjugation differences over a subgroup

Every nonempty fiber of `x ↦ x⁻¹ * t * x * t⁻¹` on a subgroup `R` is a
translate of the centralizer of `t` in `R`. Consequently, if every element of
a subgroup `W` occurs as a difference, the preimage of `W` has cardinality
`|W| |C_R(t)|`. Neither normality nor commutativity of `W` is needed.

Choose a witness `a` for a fiber. The explicit bijection to the centralizer
is `x ↦ x * a⁻¹`, with inverse `c ↦ c * a`. Partitioning the preimage of `W`
into its fibers gives the cardinality formula.

This supplies the final counting step for the quaternion–cyclic core in
Janko–Thompson (1970), §4, Case 2, printed p.393.
-/

namespace Subgroup

private def differenceFiberEquiv {P : Type*} [Group P]
    (R : Subgroup P) (t w : P) (a : R)
    (ha : (a : P)⁻¹ * t * a * t⁻¹ = w) :
    {x : R // (x : P)⁻¹ * t * x * t⁻¹ = w} ≃
      ↥(R ⊓ centralizer ({t} : Set P)) where
  toFun x := ⟨(x.1 : P) * (a : P)⁻¹,
    R.mul_mem x.1.property (R.inv_mem a.property), by
      apply mem_centralizer_singleton_iff.mpr
      have he : (x.1 : P)⁻¹ * t * x.1 = (a : P)⁻¹ * t * a :=
        mul_right_cancel (x.property.trans ha.symm)
      calc
        ((x.1 : P) * (a : P)⁻¹) * t =
            (x.1 : P) * ((a : P)⁻¹ * t * a) * (a : P)⁻¹ := by group
        _ = (x.1 : P) * ((x.1 : P)⁻¹ * t * x.1) * (a : P)⁻¹ := by rw [he]
        _ = t * ((x.1 : P) * (a : P)⁻¹) := by group⟩
  invFun c := ⟨⟨(c : P) * a, R.mul_mem c.property.1 a.property⟩, by
    change ((c : P) * a)⁻¹ * t * ((c : P) * a) * t⁻¹ = w
    have hc : (c : P)⁻¹ * t * c = t := by
      rw [mul_assoc, ← mem_centralizer_singleton_iff.mp c.property.2,
        inv_mul_cancel_left]
    calc
      ((c : P) * a)⁻¹ * t * ((c : P) * a) * t⁻¹ =
          (a : P)⁻¹ * ((c : P)⁻¹ * t * c) * a * t⁻¹ := by group
      _ = w := by rw [hc, ha]⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; simp
  right_inv c := by apply Subtype.ext; simp

/-- If every element of `W` is a conjugation difference from `R`, the
preimage of `W` has cardinality `|W|` times the centralizer of `t` in `R`. -/
public theorem card_conjugation_difference_preimage_of_surjective {P : Type*} [Group P] [Finite P]
    (R W : Subgroup P) (t : P)
    (hhit : ∀ w : W, ∃ x : R, (x : P)⁻¹ * t * x * t⁻¹ = w) :
    Nat.card {x : R // (x : P)⁻¹ * t * x * t⁻¹ ∈ W} =
      Nat.card W * Nat.card (R ⊓ centralizer ({t} : Set P) : Subgroup P) := by
  classical
  let f : R → P := fun x => (x : P)⁻¹ * t * x * t⁻¹
  have he : (Σ w : W, {x : R // f x = w}) ≃ {x : R // f x ∈ W} :=
    Equiv.sigmaSubtypeFiberEquivSubtype f (fun _ => Iff.rfl)
  let : Fintype W := Fintype.ofFinite W
  rw [← Nat.card_congr he, Nat.card_sigma]
  have hf (w : W) : Nat.card {x : R // f x = w} =
      Nat.card (R ⊓ centralizer ({t} : Set P) : Subgroup P) := by
    obtain ⟨a, ha⟩ := hhit w
    exact Nat.card_congr (differenceFiberEquiv R t w a ha)
  simp only [hf, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

end Subgroup
