module

public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.QuaternionPlacement.GraphField.MarkedAction

/-!
# Cyclic quaternion character kernels acting on the concrete E₉

Let B be the displayed quaternion subgroup of PSL₃(4), and let D be the
projective diagonal-and-cycle subgroup of order nine. Any surjective character
from B to a group of order two has cyclic kernel of order four. Its image in
PSL₃(4) normalizes D and has no proper nontrivial invariant subgroup in D.

Normalization uses the identification of D with the actual graph-field
fixed group's two-residual. For irreducibility, direct matrix multiplication
shows that the common quaternion involution v inverts D. The character kernel
contains an element whose square is v. On an invariant subgroup of order three,
that element's square would act trivially, contradicting inversion.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the covered
graph-field case of 16.4.9(2), printed p.1191. This is the intrinsic character
kernel calculation; identifying the covered centralizer quotient with this
kernel and transporting its action belong to the covering construction.
-/

public section

open Subgroup
namespace Matrix.PSL3Four.InnerFamilyNormalizer.DoubleCover.CyclicKernelAction
open ExtendedCentralizer.ProjectiveFixer Centerless
noncomputable section

variable {Z : Type*} [Group Z]

/-- Every surjective two-element character of the concrete Q₈ has kernel of order four. -/
theorem kernel_card (χ : quaternion →* Z) (hZ : Nat.card Z = 2)
    (hχ : Function.Surjective χ) : Nat.card χ.ker = 4 := by
  have h := χ.ker.card_mul_index
  rw [index_ker, χ.range_eq_top_of_surjective hχ,
    Nat.card_congr Subgroup.topEquiv.toEquiv, hZ, quaternion_card] at h
  omega

/-- The common quaternion involution lies in every two-element character kernel. -/
theorem v_mem_kernel (χ : quaternion →* Z) (hZ : Nat.card Z = 2) :
    (⟨v, v_mem_quaternion⟩ : quaternion) ∈ χ.ker := by
  have h : χ (⟨i, i_mem_quaternion⟩ : quaternion) ^ 2 = 1 := by
    simpa only [hZ] using (pow_card_eq_one' : χ (⟨i, i_mem_quaternion⟩ : quaternion) ^ Nat.card Z = 1)
  rw [← map_pow] at h
  exact (show (⟨i, i_mem_quaternion⟩ : quaternion) ^ 2 = ⟨v, v_mem_quaternion⟩
    from Subtype.ext i_sq_projective) ▸ h

private theorem exists_kernel_square_eq_v (χ : quaternion →* Z) (hZ : Nat.card Z = 2)
    (hχ : Function.Surjective χ) : ∃ x : χ.ker, (x.val.val : PSL) ^ 2 = v := by
  let vv : χ.ker := ⟨⟨v, v_mem_quaternion⟩, v_mem_kernel χ hZ⟩
  obtain ⟨x, hx1, hxv⟩ := ENat.exists_ne_ne_of_three_le
    (α := χ.ker) (by rw [ENat.card_eq_coe_natCard, kernel_card χ hZ hχ]; decide) 1 vv
  have hn : (x.val.val : PSL) ≠ 1 := by
    intro h
    exact hx1 (Subtype.ext (Subtype.ext h))
  rcases quaternion_nonidentity x.val.val x.val.property hn with hv | hs
  · exact (hxv (Subtype.ext (Subtype.ext hv))).elim
  · exact ⟨x, hs⟩

/-- The kernel is actually isomorphic to the cyclic group of order four. -/
theorem kernel_equiv (χ : quaternion →* Z) (hZ : Nat.card Z = 2)
    (hχ : Function.Surjective χ) : Nonempty (χ.ker ≃* Multiplicative (ZMod 4)) := by
  obtain ⟨x, hx⟩ := exists_kernel_square_eq_v χ hZ hχ
  have hx4 : (x.val.val : PSL) ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, hx, v_sq_projective]
  have horder : orderOf (x.val.val : PSL) = 4 :=
    orderOf_eq_prime_pow (p := 2) (n := 1)
      (by simpa only [pow_one, hx] using v_ne_one) (by simpa using hx4)
  have hxorder : orderOf x = 4 := by
    simpa only [Subgroup.orderOf_coe] using horder
  let : IsCyclic χ.ker := isCyclic_of_orderOf_eq_card x
    (hxorder.trans (kernel_card χ hZ hχ).symm)
  exact ⟨mulEquivOfCyclicCardEq (by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] using
      kernel_card χ hZ hχ)⟩

/-- The concrete quaternion matrices normalize the displayed E₉. -/
theorem quaternion_le_normalizer_model : quaternion ≤ normalizer (model : Set PSL) := by
  intro q hq
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact QuaternionPlacement.GraphField.model_map
    (QuaternionPlacement.GraphField.quaternionConj ⟨q, hq⟩)

/-- The character kernel acts on E₉ by the ambient matrix conjugation. -/
theorem kernel_le_normalizer_model (χ : quaternion →* Z) :
    χ.ker.map quaternion.subtype ≤ normalizer (model : Set PSL) := by
  rintro q ⟨x, _, rfl⟩
  exact quaternion_le_normalizer_model x.property

private theorem v_conj_diagonal (u : Fˣ) :
    (MulAut.conj v) (ExtendedCentralizer.ProjectiveFixer.diagonal u) = (ExtendedCentralizer.ProjectiveFixer.diagonal u)⁻¹ := by
  change v * ExtendedCentralizer.ProjectiveFixer.diagonal u * v⁻¹ = (ExtendedCentralizer.ProjectiveFixer.diagonal u)⁻¹
  apply (mul_inv_eq_iff_eq_mul).mpr
  rw [← map_inv]
  change project vSL * project (diagonalSL u) = project (diagonalSL u⁻¹) * project vSL
  rw [← map_mul, ← map_mul, project_eq_iff]
  refine ⟨(u : F), congrArg Units.val (unit_cube u), ?_⟩
  have hi := congrArg Units.val (unit_inv u)
  change (!![0,1,0;1,0,0;0,0,1] : Matrix (Fin 3) (Fin 3) F) *
      !![1,0,0;0,(u : F),0;0,0,(↑u⁻¹ : F)] =
    Matrix.scalar (Fin 3) (u : F) *
      (!![1,0,0;0,(↑u⁻¹ : F),0;0,0,(u : F)] * !![0,1,0;1,0,0;0,0,1])
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]
  simpa [pow_two] using hi

private theorem v_conj_cycle : (MulAut.conj v) cycle = cycle⁻¹ := by
  have hi : cycleSL⁻¹ = cycleSL ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [← pow_succ'] using cycleSL_cube
  have he : vSL * cycleSL = cycleSL ^ 2 * vSL := by
    apply Subtype.ext
    change vSL.val * cycleSL.val = cycleSL.val ^ 2 * vSL.val
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [vSL, cycleSL, pow_two, Matrix.mul_apply, Fin.sum_univ_three]
  change v * cycle * v⁻¹ = cycle⁻¹
  apply (mul_inv_eq_iff_eq_mul).mpr
  change project vSL * project cycleSL = (project cycleSL)⁻¹ * project vSL
  rw [← map_inv, hi, ← map_mul, ← map_mul, he]

/-- The common quaternion involution inverts each element of the concrete E₉. -/
theorem v_inverts_model (y : PSL) (hy : y ∈ model) :
    v * y * v⁻¹ = y⁻¹ := by
  obtain ⟨⟨u,t⟩, rfl⟩ := hy
  have ht : (MulAut.conj v) (t : PSL) = (t : PSL)⁻¹ := by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp t.property
    rw [← hk, map_zpow, v_conj_cycle, inv_zpow]
  change (MulAut.conj v) (ExtendedCentralizer.ProjectiveFixer.diagonal u * (t : PSL)) = (ExtendedCentralizer.ProjectiveFixer.diagonal u * (t : PSL))⁻¹
  rw [map_mul, v_conj_diagonal, ht]
  have hc : Commute (ExtendedCentralizer.ProjectiveFixer.diagonal u) (t : PSL) := by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp t.property
    rw [← hk]
    exact (diagonal_commute_cycle u).zpow_right k
  rw [_root_.mul_inv_rev]
  exact hc.inv_inv.eq

/-- A subgroup of the concrete E₉ invariant under the character kernel is trivial or all of E₉. -/
theorem kernel_irreducible (χ : quaternion →* Z) (hZ : Nat.card Z = 2)
    (hχ : Function.Surjective χ) (A : Subgroup PSL) (hA : A ≤ model)
    (hN : χ.ker.map quaternion.subtype ≤ normalizer (A : Set PSL)) :
    A = ⊥ ∨ A = model := by
  have hd := card_dvd_of_le hA
  rw [model_card] at hd
  have hm : Nat.card A ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  have hds : Nat.divisors 9 = {1, 3, 9} := by decide
  rw [hds] at hm
  have hc : Nat.card A = 1 ∨ Nat.card A = 3 ∨ Nat.card A = 9 := by simpa using hm
  rcases hc with hc | hc | hc
  · exact Or.inl ((eq_bot_iff_card A).mpr hc)
  · left
    let : IsCyclic A := isCyclic_of_prime_card hc
    have hAut : Nat.card (MulAut A) = 2 := by
      rw [IsCyclic.card_mulAut, hc]
      decide
    obtain ⟨x, hx⟩ := exists_kernel_square_eq_v χ hZ hχ
    let a : MulAut A := A.normalizerMonoidHom
      ⟨x.val.val, hN ⟨x.val, x.property, rfl⟩⟩
    have ha2 : a ^ 2 = 1 := by
      simpa only [hAut] using (pow_card_eq_one' : a ^ Nat.card (MulAut A) = 1)
    apply bot_unique
    intro y hy
    let yy : A := ⟨y, hy⟩
    have hfix : v * y * v⁻¹ = y := by
      have hh := congrArg (fun f : MulAut A => ((f yy : A) : PSL)) ha2
      change x.val.val * (x.val.val * y * x.val.val⁻¹) * x.val.val⁻¹ = y at hh
      calc
        v * y * v⁻¹ = x.val.val ^ 2 * y * (x.val.val ^ 2)⁻¹ := by rw [hx]
        _ = x.val.val * (x.val.val * y * x.val.val⁻¹) * x.val.val⁻¹ := by
          simp only [pow_two, _root_.mul_inv_rev, mul_assoc]
        _ = y := hh
    have hinv : y⁻¹ = y := (v_inverts_model y (hA hy)).symm.trans hfix
    have hy2 : yy ^ 2 = 1 := by
      apply Subtype.ext
      change y ^ 2 = 1
      rw [pow_two]
      calc
        y * y = y⁻¹ * y := congrArg (· * y) hinv.symm
        _ = 1 := inv_mul_cancel y
    have hy3 : yy ^ 3 = 1 := by
      simpa only [hc] using (pow_card_eq_one' : yy ^ Nat.card A = 1)
    change yy ^ (2 + 1) = 1 at hy3
    rw [pow_succ, hy2, one_mul] at hy3
    exact congrArg Subtype.val hy3
  · exact Or.inr (eq_of_le_of_card_ge hA (by rw [hc, model_card]))

end
end Matrix.PSL3Four.InnerFamilyNormalizer.DoubleCover.CyclicKernelAction
