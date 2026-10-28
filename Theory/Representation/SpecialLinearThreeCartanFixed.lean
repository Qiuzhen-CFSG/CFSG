module

public import Theory.SpecificGroups.PSL3.LinearThreeLocalCores
public import Theory.Representation.SpecialLinearThreeTransitivity
public import Theory.Representation.SpecialLinearThreeFrameGeometry
public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Fixed spaces of an odd subgroup of order (q − 1)² in SL₃(q)

A nonzero fixed vector puts the subgroup in a vector stabilizer. Its odd order
then embeds it in the stabilizer's SL₂ quotient, contradicting divisibility
of orders for even q > 2. Inverse transpose and the dot-product equivalence
give the same assertion on the contragredient module.

The natural argument is extracted from the Chapter 11 Cartan calculation in
`LocalGeometry.Normalizers.PointCohomology.PointGeometry.CartanFixed`.
Source: Aschbacher–Smith, 11.5.7, printed pp.781–782; G.2.5, pp.335–336.
-/

open Subgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
@[expose] public noncomputable section
namespace Representation.SpecialLinearThreeCartanFixed

theorem injective_of_odd_two_kernel {A B : Type*} [Group A] [Finite A] [Group B]
    (f : A →* B) (ho : Odd (Nat.card A)) (hk : IsPGroup 2 f.ker) :
    Function.Injective f := by
  apply f.ker_eq_bot_iff.mp
  have hc : Odd (Nat.card f.ker) := Odd.of_dvd_nat ho f.ker.card_subgroup_dvd_card
  obtain ⟨n, hn⟩ := hk.exists_card_eq
  have hn0 : n = 0 := by
    by_contra h
    exact hc.not_two_dvd_nat (hn ▸ dvd_pow_self 2 h)
  apply Subgroup.eq_bot_of_card_eq
  exact hn.trans (by rw [hn0]; rfl)

private theorem torus_order_not_dvd_sl2 {q : ℕ} (hq : 2 < q) (ho : Odd (q-1)) :
    ¬ (q-1)^2 ∣ q * (q^2-1) := by
  intro hd
  have hpos : 0 < q - 1 := by omega
  have he : q * (q^2-1) = (q-1) * (q*(q+1)) := by
    have h : q - 1 + 1 = q := by omega
    have h2 : q ^ 2 - 1 + 1 = q ^ 2 := Nat.sub_add_cancel (by nlinarith)
    nlinarith
  rw [he, pow_two] at hd
  have hd' : q-1 ∣ q*(q+1) := (Nat.mul_dvd_mul_iff_left hpos).mp hd
  have hcop : Nat.Coprime (q-1) q := by
    exact (Nat.coprime_self_sub_left (show 1 ≤ q by omega)).mpr (Nat.coprime_one_left _)
  have hh : q-1 ∣ q+1 := hcop.dvd_of_dvd_mul_left hd'
  have htwo : q-1 ∣ 2 := by
    have he : q+1 = (q-1)+2 := by omega
    rw [he] at hh
    exact (Nat.dvd_add_right (dvd_refl (q-1))).mp hh
  have hle := Nat.le_of_dvd (by decide : 0 < 2) htwo
  obtain ⟨k, hk⟩ := ho
  omega

private theorem not_injective_sl2 {F A : Type*} [Field F] [Finite F] [Group A] [Finite A]
    (hF : 2 < Nat.card F) (ho : Odd (Nat.card F - 1))
    (hc : Nat.card A = (Nat.card F - 1)^2) (f : A →* SL(2,F)) :
    ¬ Function.Injective f := by
  intro hi
  have hd := Subgroup.card_dvd_of_injective f hi
  rw [hc, BenderSuzuki.External.huppert614_card_specialLinearGroup] at hd
  exact torus_order_not_dvd_sl2 hF ho hd

private theorem odd_embedding_core_quotient {A B : Type*} [Group A] [Finite A] [Group B]
    (f : A →* B) (hi : Function.Injective f) (ho : Odd (Nat.card A)) :
    Function.Injective ((QuotientGroup.mk' (pCore 2 B)).comp f) := by
  apply injective_of_odd_two_kernel _ ho
  change IsPGroup 2 ((QuotientGroup.mk' (pCore 2 B)).ker.comap f)
  rw [QuotientGroup.ker_mk']
  exact pCore_isPGroup.comap_of_injective f hi

open Matrix.PSL3.LinearThree
theorem natural_fixed_eq_zero {F A : Type*} [Field F] [Finite F] [CharP F 2]
    [Group A] [Finite A] (hF : 2 < Nat.card F) (ho : Odd (Nat.card F - 1))
    (hc : Nat.card A = (Nat.card F - 1)^2) (f : A →* SL(3,F))
    (hi : Function.Injective f) (v : Fin 3 → F)
    (hv : ∀ a, (f a).val *ᵥ v = v) : v = 0 := by
  by_contra hn
  have he0 : (![1,0,0] : Fin 3 → F) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  obtain ⟨g,hg⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three v ![1,0,0] hn he0
  let j := (MulAut.conj g).toMonoidHom.comp f
  have hj (a : A) : j a ∈ pointLocalSL F := by
    have hh : (j a) • (![1,0,0] : Fin 3 → F) = ![1,0,0] := by
      change (g * f a * g⁻¹) • (![1,0,0] : Fin 3 → F) = _
      change g • v = ![1,0,0] at hg
      rw [← hg, mul_smul, mul_smul, inv_smul_smul]
      change g • ((f a).val *ᵥ v) = g • v
      rw [hv]
    apply (mem_pointLocalSL_iff F _).mpr
    change (j a).val *ᵥ ![1,0,0] = ![1,0,0] at hh
    have h0 := congrFun hh 0
    have h1 := congrFun hh 1
    have h2 := congrFun hh 2
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using And.intro h0 (And.intro h1 h2)
  let k := j.codRestrict (pointLocalSL F) hj
  have hk : Function.Injective k := by
    intro a b h
    exact hi ((MulAut.conj g).injective (congrArg Subtype.val h))
  have hodd : Odd (Nat.card A) := hc ▸ ho.pow
  let r := (pointLocalSLCoreQuotientEquiv F).toMonoidHom.comp
    ((QuotientGroup.mk' (pCore 2 (pointLocalSL F))).comp k)
  exact not_injective_sl2 hF ho hc r
    ((pointLocalSLCoreQuotientEquiv F).injective.comp (odd_embedding_core_quotient k hk hodd))

private theorem transpose_mul {F : Type*} [Field F] (g h : SL(3,F)) :
    SpecialLinearGroup.transpose (g * h) =
      SpecialLinearGroup.transpose h * SpecialLinearGroup.transpose g := by
  apply Subtype.ext
  exact Matrix.transpose_mul _ _

private theorem transpose_transpose {F : Type*} [Field F] (g : SL(3,F)) :
    SpecialLinearGroup.transpose (SpecialLinearGroup.transpose g) = g := by
  apply Subtype.ext
  exact Matrix.transpose_transpose _

private theorem transpose_inv {F : Type*} [Field F] (g : SL(3,F)) :
    SpecialLinearGroup.transpose g⁻¹ = (SpecialLinearGroup.transpose g)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← transpose_mul, mul_inv_cancel]
  apply Subtype.ext
  exact Matrix.transpose_one

private def graph {F : Type*} [Field F] : MulAut SL(3,F) where
  toFun g := (SpecialLinearGroup.transpose g)⁻¹
  invFun g := (SpecialLinearGroup.transpose g)⁻¹
  left_inv g := by dsimp only; rw [transpose_inv, transpose_transpose, inv_inv]
  right_inv g := by dsimp only; rw [transpose_inv, transpose_transpose, inv_inv]
  map_mul' g h := by rw [transpose_mul, _root_.mul_inv_rev]

/-- The contragredient module has zero common fixed space as well. -/
theorem dual_fixed_eq_zero {F A : Type*} [Field F] [Finite F] [CharP F 2]
    [Group A] [Finite A] (hF : 2 < Nat.card F) (ho : Odd (Nat.card F - 1))
    (hc : Nat.card A = (Nat.card F - 1)^2) (f : A →* SL(3,F))
    (hi : Function.Injective f) (v : Module.Dual F (Fin 3 → F))
    (hv : ∀ a, FrameGeometry.natural.dual (f a) v = v) : v = 0 := by
  let e := dotProductEquiv F (Fin 3)
  have he (a : A) : e ((graph (f a)).val *ᵥ e.symm v) =
      FrameGeometry.natural.dual (f a) v := by
    apply LinearMap.ext
    intro w
    change dotProduct (((SpecialLinearGroup.transpose (f a))⁻¹).val *ᵥ e.symm v) w =
      v (((f a)⁻¹).val *ᵥ w)
    rw [← transpose_inv]
    change dotProduct (((f a)⁻¹).val.transpose *ᵥ e.symm v) w = _
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
    exact congrArg (fun z : Module.Dual F (Fin 3 → F) => z (((f a)⁻¹).val *ᵥ w))
      (e.apply_symm_apply v)
  have hz := natural_fixed_eq_zero hF ho hc (graph.toMonoidHom.comp f)
    (graph.injective.comp hi) (e.symm v) (by
      intro a
      apply e.injective
      exact (he a).trans (hv a) |>.trans (e.apply_symm_apply v).symm)
  exact e.symm.injective (hz.trans e.symm.map_zero.symm)

end Representation.SpecialLinearThreeCartanFixed
