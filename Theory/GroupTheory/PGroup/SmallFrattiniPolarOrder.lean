module
public import Theory.GroupTheory.PGroup.SmallFrattiniLinearForms
public import Theory.Representation.UniformBinaryPolarQuotient
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Group orders from the actual Frattini polar

The radical of the commutator form on Q/Φ(Q) is exactly Z(Q)/Φ(Q).
Its binary dimension therefore records the center order, while the whole
space records the group order. No central summand is discarded.
-/

public section
open Subgroup Module
open scoped IsMulCommutative
namespace SmallFrattini
variable {Q : Type*} [Group Q] [Finite Q]

theorem card_eq_two_pow_frattini_finrank (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) :
    letI := quotientElementary htwo
    Nat.card Q = 2 ^ (finrank (ZMod 2) (Additive (Q ⧸ frattini Q)) + 1) := by
  let := quotientElementary htwo
  have hc : Nat.card (Q ⧸ frattini Q) =
      2 ^ finrank (ZMod 2) (Additive (Q ⧸ frattini Q)) :=
    (Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := Additive (Q ⧸ frattini Q))).trans (by rw [Nat.card_zmod])
  have hh := (frattini Q).card_mul_index
  rw [hphi,index_eq_card,hc] at hh
  rw [pow_succ]
  exact hh.symm.trans (Nat.mul_comm _ _)

theorem center_card_eq_two_pow_polar_radical (htwo : IsPGroup 2 Q)
    (hphi : Nat.card (frattini Q) = 2) :
    letI := quotientElementary htwo
    Nat.card (center Q) =
      2 ^ (finrank (ZMod 2) (quotientBilinearForm htwo hphi).ker + 1) := by
  classical
  let := quotientElementary htwo
  let B := quotientBilinearForm htwo hphi
  have hmem (x : Additive (Q ⧸ frattini Q)) :
      x ∈ B.ker ↔ x.toMul ∈ centerImage Q := by
    rw [LinearMap.mem_ker]
    rw [←quotientBilinearForm_radical htwo hphi x.toMul]
    constructor
    · intro hx y
      exact congrArg (fun l => l y) hx
    · intro hx
      ext y
      exact hx y
  let e : B.ker ≃ centerImage Q :=
    { toFun := fun x => ⟨x.val.toMul,(hmem x.val).mp x.property⟩
      invFun := fun x => ⟨Additive.ofMul x.val,(hmem _).mpr x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hBc : Nat.card (centerImage Q) = 2 ^ finrank (ZMod 2) B.ker :=
    (Nat.card_congr e.symm).trans
      ((Module.natCard_eq_pow_finrank (K := ZMod 2) (V := B.ker)).trans
        (by rw [Nat.card_zmod]))
  have hcentral : frattini Q ≤ center Q := central_of_normal_card_two _ hphi
  let f : center Q →* (Q ⧸ frattini Q) :=
    (QuotientGroup.mk' (frattini Q)).comp (center Q).subtype
  have hk : f.ker = (frattini Q).subgroupOf (center Q) := by
    ext z
    exact QuotientGroup.eq_one_iff z.val
  have hkc : Nat.card f.ker = 2 := by
    rw [hk]
    exact (Nat.card_congr (subgroupOfEquivOfLe hcentral).toEquiv).trans hphi
  have hr : f.range = centerImage Q := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨z.val,z.property,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨⟨z,hz⟩,rfl⟩
  have hh := f.ker.card_mul_index
  rw [hkc,index_ker,hr,hBc] at hh
  rw [pow_succ]
  exact hh.symm.trans (Nat.mul_comm _ _)
/-- The two exact group orders retained by an odd uniform polar orbit.
The second case keeps its central radical rather than quotienting it away. -/
theorem order_and_center_of_odd_polar_quotient
    (htwo : IsPGroup 2 Q) (hphi : Nat.card (frattini Q) = 2)
    (n : ℕ) (hn : Odd n) :
    letI := quotientElementary htwo
    ∀ (f : UniformBinaryPolar.V n →ₗ[ZMod 2] Additive (Q ⧸ frattini Q)),
      Function.Surjective f →
      (∀ x y, UniformBinaryPolar.form n x y =
        quotientBilinearForm htwo hphi (f x) (f y)) →
      (Nat.card Q = 2^n ∧ Nat.card (center Q) = 2) ∨
        (Nat.card Q = 2^(n+1) ∧ Nat.card (center Q) = 4) := by
  let := quotientElementary htwo
  intro f hf hp
  have hQc := card_eq_two_pow_frattini_finrank htwo hphi
  have hZc := center_card_eq_two_pow_polar_radical htwo hphi
  rcases UniformBinaryPolar.odd_quotient_dimension_and_radical
    (quotientBilinearForm htwo hphi) f hf hp hn with ⟨hd,hz⟩ | ⟨hd,hz⟩
  · left
    refine ⟨hQc.trans (congrArg (fun a => 2^a) hd),?_⟩
    rw [hz,finrank_bot] at hZc
    exact hZc
  · right
    exact ⟨hQc.trans (congrArg (fun a => 2^(a+1)) hd),by simpa [hz] using hZc⟩
end SmallFrattini
