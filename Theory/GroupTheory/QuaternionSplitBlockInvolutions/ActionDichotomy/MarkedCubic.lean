module

public import Theory.GroupTheory.QuaternionSplitBlockInvolutions.ActionDichotomy.FixedPlane
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# A marked cubic forces the quaternion involution types

Use the actual conjugation action of an ambient group H on the square quotient
of its normal quaternion central product U. The image of the marked subgroup R
has order three and [U/Z(U),R] is all of U/Z(U). Its cubic norm therefore
vanishes. An involution inverting this image has four fixed quotient vectors,
so the fixed-plane dichotomy gives c₂ with two outer factor restrictions, or
factor interchange with type a₂.

No inversion of the entire elementary nine is assumed or asserted here.
Nor does this module identify the normalizer image of the elementary sixteen;
these are the remaining group-theoretic steps in the full source assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 12.8.5(1),
printed p.850, and the quaternion-action step of 14.4.4, printed p.1007.
-/

open Subgroup
namespace Subgroup.QuaternionCentralProductData
open Representation.BinaryOffender
variable {H : Type*} [Group H] [Finite H] (U : Subgroup H) [U.Normal]
    (d : QuaternionCentralProductData U)

/-- The literal conjugation action on the additive square quotient. -/
@[expose] public noncomputable def normalSquareLinearAction :
    H →* (d.SquareSpace ≃ₗ[ZMod 2] d.SquareSpace) :=
  d.quotientLinearAction.comp (MulAut.conjNormal : H →* MulAut U)

/-- The same action as a representation, for the source commutator subspace. -/
@[expose] public noncomputable def normalSquareRepresentation :
    Representation (ZMod 2) H d.SquareSpace :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (d.normalSquareLinearAction U)

/-- The norm of the marked cubic image vanishes on the full commutator space. -/
private theorem marked_cubic_polynomial
    (R : Subgroup H)
    (hR : Nat.card (R.map (d.normalSquareLinearAction U)) = 3)
    (hmove : subspaceCommutator (d.normalSquareRepresentation U) ⊤ R = ⊤) :
    ∃ r ∈ R, (d.normalSquareLinearAction U r)^3=1 ∧
      (d.normalSquareRepresentation U r)^2 + d.normalSquareRepresentation U r + 1 = 0 := by
  classical
  let σ := d.normalSquareLinearAction U
  let ρ := d.normalSquareRepresentation U
  let F := R.map σ
  have hFc : Nat.card F = 3 := hR
  let _ : Finite F := Nat.finite_of_card_ne_zero (by omega)
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨f, hf⟩ := exists_ne (1 : F)
  obtain ⟨r, hr, he⟩ := f.property
  have hf3 : f^3=1 := hR ▸ pow_card_eq_one' (x := f)
  have hr3 : (σ r)^3=1 := by rw [he]; exact congrArg Subtype.val hf3
  let t := ρ r
  let N := t^2+t+1
  have ht3 : t^3=1 := congrArg LinearEquiv.toLinearMap hr3
  have hNt : N*t=N := by
    dsimp [N]
    rw [add_mul, add_mul, one_mul, ← pow_succ, ← pow_two, ht3]
    abel
  have hNtn (n : ℕ) : N*t^n=N := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mul_assoc, ih, hNt]
  have hkill : subspaceCommutator ρ ⊤ R ≤ LinearMap.ker N := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, v, _, rfl⟩
    let fx : F := ⟨σ x, mem_map_of_mem σ hx⟩
    have hm := mem_zpowers_of_prime_card hR hf (g' := fx)
    rw [mem_zpowers_iff_mem_range_orderOf] at hm
    obtain ⟨n, _, hn⟩ := Finset.mem_image.mp hm
    have hn' : (σ r)^n=σ x := by rw [he]; exact congrArg Subtype.val hn
    have hnρ : t^n=ρ x := by
      have hh := congrArg LinearEquiv.automorphismGroup.toLinearMapMonoidHom hn'
      rw [map_pow] at hh
      exact hh
    change N (ρ x v-v)=0
    rw [map_sub, ← hnρ]
    exact sub_eq_zero.mpr (LinearMap.congr_fun (hNtn n) v)
  refine ⟨r, hr, hr3, ?_⟩
  apply LinearMap.ext
  intro v
  exact hkill (by rw [hmove]; exact Submodule.mem_top)

/-- The marked cubic action forces the c₂/factor-interchange dichotomy.
Both factor restrictions in the c₂ branch are proved outer. -/
public theorem marked_action_type_dichotomy
    (R : Subgroup H)
    (hR : Nat.card (R.map (d.normalSquareLinearAction U)) = 3)
    (hmove : subspaceCommutator (d.normalSquareRepresentation U) ⊤ R = ⊤)
    (a : H) (ha : a^2=1)
    (hinv : ∀ r ∈ R, d.normalSquareLinearAction U (a*r*a⁻¹) =
      (d.normalSquareLinearAction U r)⁻¹) :
    (d.IsC2Action (MulAut.conjNormal a) ∧ d.BothOuter (MulAut.conjNormal a)) ∨
      (d.left.map (MulAut.conjNormal a).toMonoidHom = d.right ∧
        d.IsA2Action (MulAut.conjNormal a)) := by
  obtain ⟨r, hr, hr3, hpoly⟩ := marked_cubic_polynomial U d R hR hmove
  have ha' : (MulAut.conjNormal a : MulAut U)^2=1 := by rw [← map_pow, ha, map_one]
  apply d.action_dichotomy_of_fixed_four _ ha'
  apply d.fixed_card_of_inverted_cubic _ ha' _ hpoly
  have he : d.normalSquareLinearAction U a * d.normalSquareLinearAction U r =
      (d.normalSquareLinearAction U r)^2 * d.normalSquareLinearAction U a := by
    have hh := hinv r hr
    rw [map_mul, map_mul, map_inv] at hh
    have hs : (d.normalSquareLinearAction U r)^2 =
        (d.normalSquareLinearAction U r)⁻¹ := by
      apply mul_eq_one_iff_eq_inv.mp
      rw [← pow_succ, hr3]
    rw [hs]
    exact mul_inv_eq_iff_eq_mul.mp hh
  exact congrArg LinearEquiv.toLinearMap he
end Subgroup.QuaternionCentralProductData
