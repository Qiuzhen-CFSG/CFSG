module

public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Tactic.FinCases

/-!
# Elementary abelian Sylow two-subgroups of the actual J₁ model

Seven conjugates of the standard involution, together with the identity,
form an eight-element subgroup of exponent two. The certified order of J₁
makes it Sylow, and Sylow conjugacy transports both its order and its
exponent to every Sylow two-subgroup.

The word, prefix matrices and eight-element table are reused from
`Model.Certification.InvolutionFusion`. The finite matrix identities are
checked again here to expose the elementary abelian structure without
accessing private declarations in that certificate. No new group-order
or simplicity computation is involved.

Source: GLS3, Table 5.3f, and the local J₁ argument in Aschbacher–Smith,
*The Classification of Quasithin Groups*, printed p.510. The underlying
ATLAS representation is `J1G1-f11r7B0`; its explicit matrices and attribution
are recorded in `Model.Basic`.
-/

namespace Janko1.SylowTwo

private abbrev Mat := Matrix (Fin 7) (Fin 7) (ZMod 11)
private def rho : Model →* Mat where
  toFun x := (inclusion x).val
  map_one' := rfl
  map_mul' _ _ := rfl
private theorem rho_injective : Function.Injective rho :=
  Units.val_injective.comp inclusion_injective
private def c : Model := (a*b)*(a*b^2)*(a*b^2)*(a*b)*(a*b)*(a*b^2)*(a*b)*(a*b^2)*(a*b^2)*(a*b)
-- Matrices of the two syllables and the successive word prefixes.
private def T₁ : Mat := !![9, 9, 2, 1, 3, 8, 6;
      2, 5, 5, 9, 2, 2, 1;
      5, 9, 9, 9, 8, 10, 3;
      5, 5, 7, 10, 9, 2, 5;
      7, 1, 5, 3, 5, 8, 2;
      6, 9, 10, 1, 10, 2, 3;
      1, 9, 6, 5, 9, 5, 4]
private def T₂ : Mat := !![1, 10, 3, 9, 10, 9, 6;
      5, 9, 4, 9, 6, 6, 1;
      9, 3, 6, 9, 10, 3, 9;
      5, 9, 10, 6, 9, 2, 9;
      9, 3, 8, 2, 9, 10, 6;
      4, 9, 5, 5, 1, 9, 5;
      5, 6, 9, 10, 3, 8, 4]
private def P0 : Mat := !![9, 9, 2, 1, 3, 8, 6;
      2, 5, 5, 9, 2, 2, 1;
      5, 9, 9, 9, 8, 10, 3;
      5, 5, 7, 10, 9, 2, 5;
      7, 1, 5, 3, 5, 8, 2;
      6, 9, 10, 1, 10, 2, 3;
      1, 9, 6, 5, 9, 5, 4]
private def P1 : Mat := !![1, 6, 5, 6, 6, 7, 7;
      5, 4, 5, 10, 6, 6, 4;
      6, 8, 6, 5, 3, 8, 3;
      4, 6, 7, 5, 8, 0, 8;
      5, 0, 7, 7, 3, 8, 6;
      6, 4, 10, 5, 5, 7, 6;
      4, 8, 5, 4, 3, 5, 0]
private def P2 : Mat := !![3, 3, 10, 8, 1, 9, 1;
      9, 1, 0, 4, 0, 8, 9;
      1, 8, 7, 0, 4, 3, 4;
      3, 1, 0, 4, 1, 5, 9;
      5, 9, 3, 3, 5, 10, 7;
      2, 10, 9, 7, 2, 4, 0;
      2, 8, 9, 10, 8, 6, 2]
private def P3 : Mat := !![9, 10, 4, 8, 7, 1, 3;
      6, 6, 9, 1, 6, 0, 3;
      0, 3, 3, 6, 7, 9, 2;
      7, 3, 5, 6, 7, 9, 4;
      8, 4, 6, 5, 8, 2, 10;
      2, 2, 3, 0, 2, 10, 1;
      3, 5, 10, 9, 5, 8, 7]
private def P4 : Mat := !![10, 8, 3, 10, 3, 1, 2;
      7, 5, 2, 8, 3, 6, 10;
      2, 2, 1, 0, 7, 0, 3;
      0, 2, 1, 2, 7, 9, 4;
      4, 1, 3, 4, 0, 7, 3;
      2, 2, 3, 2, 10, 3, 6;
      2, 8, 1, 0, 7, 1, 6]
private def P5 : Mat := !![3, 4, 7, 5, 5, 2, 7;
      4, 8, 2, 2, 2, 4, 5;
      0, 3, 4, 1, 4, 6, 0;
      5, 0, 6, 6, 3, 4, 0;
      0, 10, 4, 7, 7, 3, 3;
      5, 4, 3, 5, 4, 9, 4;
      5, 7, 5, 2, 6, 9, 1]
private def P6 : Mat := !![6, 1, 2, 6, 6, 4, 2;
      5, 0, 6, 6, 3, 0, 7;
      7, 4, 6, 3, 6, 4, 2;
      7, 3, 7, 0, 7, 1, 8;
      2, 6, 9, 4, 9, 8, 4;
      3, 7, 6, 5, 7, 4, 9;
      4, 0, 10, 0, 7, 3, 6]
private def P7 : Mat := !![7, 8, 4, 4, 6, 3, 8;
      8, 8, 0, 2, 3, 7, 8;
      0, 8, 2, 3, 3, 3, 4;
      5, 9, 10, 10, 4, 3, 0;
      2, 7, 8, 0, 8, 8, 3;
      10, 3, 5, 1, 7, 0, 2;
      1, 0, 10, 6, 4, 2, 8]
private def P8 : Mat := !![0, 8, 10, 5, 0, 7, 7;
      10, 4, 9, 2, 6, 6, 5;
      0, 0, 6, 4, 5, 6, 3;
      7, 4, 5, 2, 3, 7, 5;
      8, 1, 4, 8, 0, 7, 4;
      5, 8, 2, 4, 4, 2, 2;
      7, 7, 6, 2, 6, 8, 7]
private def P9 : Mat := !![8, 6, 2, 1, 10, 10, 2;
      5, 9, 2, 9, 10, 3, 8;
      3, 6, 9, 9, 9, 3, 1;
      9, 7, 10, 6, 8, 5, 8;
      4, 10, 9, 6, 5, 2, 6;
      1, 9, 5, 5, 9, 9, 9;
      5, 6, 5, 7, 10, 2, 9]
private abbrev C := P9
private def D : Mat := !![8, 5, 3, 9, 4, 1, 5;
      6, 9, 6, 7, 10, 9, 6;
      2, 2, 9, 10, 9, 5, 5;
      1, 9, 9, 6, 6, 5, 7;
      10, 10, 9, 8, 5, 9, 10;
      10, 3, 3, 5, 2, 9, 2;
      2, 8, 1, 8, 6, 9, 9]
private theorem rho_ab : rho (a*b) = T₁ := by
  change matrixA * matrixB = T₁
  decide +kernel
private theorem rho_ab2 : rho (a*b^2) = T₂ := by
  change matrixA * matrixB ^ 2 = T₂
  decide +kernel
private theorem step1 : P0 * T₂ = P1 := by decide +kernel
private theorem step2 : P1 * T₂ = P2 := by decide +kernel
private theorem step3 : P2 * T₁ = P3 := by decide +kernel
private theorem step4 : P3 * T₁ = P4 := by decide +kernel
private theorem step5 : P4 * T₂ = P5 := by decide +kernel
private theorem step6 : P5 * T₁ = P6 := by decide +kernel
private theorem step7 : P6 * T₂ = P7 := by decide +kernel
private theorem step8 : P7 * T₂ = P8 := by decide +kernel
private theorem step9 : P8 * T₁ = P9 := by decide +kernel
private theorem rho_c : rho c = C := by
  have h₁ : rho a * rho b = T₁ := rho_ab
  have h₂ : rho a * rho b ^ 2 = T₂ := rho_ab2
  simp only [c, map_mul, map_pow, h₁, h₂]
  rw [show T₁ * T₂ = P1 from step1, step2, step3, step4,
    step5, step6, step7, step8, step9]
private theorem rho_cinv : rho c⁻¹ = D := by
  let u : Ambient := ⟨C, D, by decide +kernel, by decide +kernel⟩
  have hc : inclusion c = u := Units.ext rho_c
  change (inclusion c⁻¹).val = D
  rw [map_inv, hc]
  rfl
-- The seven conjugates, with the identity adjoined to form the subgroup.
private def orbit : ℕ → Model
  | 0 => a
  | n+1 => c * orbit n * c⁻¹
private def e (i : Fin 8) : Model :=
  if i = 0 then 1 else orbit (i.val - 1)
private def E : Fin 8 → Mat := ![1,
!![0, 7, 9, 9, 10, 7, 9;
      7, 0, 1, 4, 3, 3, 4;
      9, 1, 2, 8, 3, 6, 2;
      9, 4, 8, 10, 1, 6, 0;
      10, 3, 3, 1, 8, 9, 1;
      7, 3, 6, 6, 9, 1, 3;
      9, 4, 2, 0, 1, 3, 0],
!![0, 4, 0, 3, 2, 9, 10;
      4, 0, 7, 3, 4, 10, 8;
      0, 7, 10, 5, 9, 8, 1;
      3, 3, 5, 1, 4, 5, 2;
      2, 4, 9, 4, 0, 9, 10;
      9, 10, 8, 5, 9, 2, 3;
      10, 8, 1, 2, 10, 3, 8],
!![3, 8, 9, 10, 10, 8, 1;
      8, 9, 10, 1, 3, 1, 8;
      9, 10, 1, 8, 10, 8, 3;
      10, 1, 8, 1, 3, 3, 2;
      10, 3, 10, 3, 3, 9, 10;
      8, 1, 8, 3, 9, 1, 10;
      1, 8, 3, 2, 10, 10, 3],
!![7, 7, 4, 3, 2, 7, 1;
      7, 4, 8, 9, 3, 3, 2;
      4, 8, 10, 3, 0, 1, 3;
      3, 9, 3, 2, 5, 9, 1;
      2, 3, 0, 5, 4, 3, 9;
      7, 3, 1, 9, 3, 6, 5;
      1, 2, 3, 1, 9, 5, 10],
!![4, 8, 3, 0, 9, 6, 9;
      8, 4, 8, 3, 9, 9, 7;
      3, 8, 6, 1, 5, 2, 4;
      0, 3, 1, 10, 3, 8, 7;
      9, 9, 5, 3, 10, 10, 10;
      6, 9, 2, 8, 10, 2, 3;
      9, 7, 4, 7, 10, 3, 7],
!![8, 8, 9, 3, 1, 10, 1;
      8, 0, 8, 10, 7, 4, 7;
      9, 8, 1, 6, 3, 5, 4;
      3, 10, 6, 2, 2, 3, 2;
      1, 7, 3, 2, 0, 0, 2;
      10, 4, 5, 3, 0, 10, 9;
      1, 7, 4, 2, 2, 9, 0],
!![10, 2, 10, 5, 10, 8, 2;
      2, 4, 2, 3, 4, 3, 8;
      10, 2, 2, 2, 3, 3, 5;
      5, 3, 2, 6, 4, 10, 8;
      10, 4, 3, 4, 7, 4, 2;
      8, 3, 3, 10, 4, 10, 0;
      2, 8, 5, 8, 2, 0, 4]]

private theorem orbit_step : ∀ i : Fin 6,
    C * E ⟨i.val + 1, by omega⟩ * D = E ⟨i.val + 2, by omega⟩ := by decide +kernel
private theorem rho_orbit (n : ℕ) (hn : n < 7) :
    rho (orbit n) = E ⟨n + 1, by omega⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [orbit, map_mul, map_mul, rho_c, rho_cinv, ih (by omega)]
    exact orbit_step ⟨n, by omega⟩
private theorem rho_e (i : Fin 8) : rho (e i) = E i := by
  fin_cases i
  · rfl
  all_goals exact rho_orbit _ (by decide)
-- These finite checks certify eight distinct elements closed under multiplication.
private theorem E_injective : Function.Injective E := by decide +kernel
private theorem E_mul : ∀ i j : Fin 8, ∃ k : Fin 8, E i * E j = E k := by decide +kernel
private theorem E_square : ∀ i : Fin 8, E i * E i = 1 := by decide +kernel

private theorem e_injective : Function.Injective e := by
  intro i j hij
  apply E_injective
  simpa only [rho_e] using congrArg rho hij

private theorem e_zero : e 0 = 1 := rfl

private theorem e_mul (i j : Fin 8) : ∃ k : Fin 8, e i * e j = e k := by
  obtain ⟨k, hk⟩ := E_mul i j
  refine ⟨k, rho_injective ?_⟩
  simpa only [map_mul, rho_e] using hk

private theorem e_inv (i : Fin 8) : (e i)⁻¹ = e i := by
  apply inv_eq_of_mul_eq_one_right
  apply rho_injective
  simpa only [map_mul, rho_e, map_one] using E_square i

private def eight : Subgroup Model where
  carrier := Set.range e
  one_mem' := ⟨0, e_zero⟩
  mul_mem' := by
    rintro x y ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := e_mul i j
    exact ⟨k, hk.symm⟩
  inv_mem' := by
    rintro x ⟨i, rfl⟩
    exact ⟨i, (e_inv i).symm⟩

private theorem card_eight : Nat.card eight = 8 := by
  change Nat.card (Set.range e) = 8
  rw [Nat.card_range_of_injective e_injective, Nat.card_fin]


private theorem eight_inv (x : eight) : x⁻¹ = x := by
  apply Subtype.ext
  obtain ⟨i, hi⟩ := x.property
  change (x : Model)⁻¹ = x
  rw [← hi, e_inv]

private instance eight_commutative : IsMulCommutative eight := .of_comm fun x y => by
  rw [← eight_inv (x * y), mul_inv_rev, eight_inv x, eight_inv y]

private theorem eight_pow_two (x : eight) : x ^ 2 = 1 := by
  simpa only [pow_two, eight_inv] using inv_mul_cancel x

private noncomputable def sylow : Sylow 2 Model :=
  (IsPGroup.of_card (p := 2) (n := 3) card_eight).toSylow (by
    have h := eight.card_mul_index
    rw [card_eight, card_model] at h
    have hi : eight.index = 21945 := by omega
    rw [hi]
    decide)

/-- Every Sylow two-subgroup of the actual matrix model has order eight. -/
public theorem card (S : Sylow 2 Model) : Nat.card S = 8 := by
  exact (Nat.card_congr (S.equiv sylow).toEquiv).trans card_eight

/-- Every Sylow two-subgroup of the actual matrix model is elementary abelian. -/
public theorem elementary (S : Sylow 2 Model) : IsElementaryAbelian 2 S := by
  let f := S.equiv sylow
  have hc : IsMulCommutative S := .of_comm fun x y => f.injective (by
    rw [map_mul, map_mul]
    exact isMulCommutative_iff.mp eight_commutative (f x) (f y))
  refine {
    toIsMulCommutative := hc
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => ?_
  }
  apply f.injective
  rw [map_pow, map_one]
  exact eight_pow_two (f x)

end Janko1.SylowTwo
