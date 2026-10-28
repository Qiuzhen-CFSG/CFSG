module

public import Theory.Representation.OrthogonalFourPlusMatrix.Binary
public import Theory.SpecificGroups.SL2.UpperUnipotent

/-!
# The fixed dimension of a Sylow subgroup on the binary determinant module

Two upper transvections, one in each actual SL₂(4) factor, force a fixed
matrix to have only its upper-right entry nonzero. Evaluation at that entry
embeds the fixed space into F₄. Sylow conjugacy transports the bound to every
Sylow subgroup. An equivariant linear equivalence then transports it along
an actual surjective group homomorphism.

This proves the intrinsic fixed-space bound used to exclude the tensor
alternative in Aschbacher--Smith, combined manuscript (1 March 2004),
Lemma 12.6.33, printed p.838. The source application is in
`CFSG.Quasithin.Chapter12.Section06.LocalAlternatives.Tensor`.
-/

@[expose] public section
open Matrix Module Representation.BinaryOffender
open scoped Pointwise
namespace ClassicalOrthogonal.FourPlusMatrix.Binary

private theorem coordinates_of_fixed (v : V)
    (hl : action (SpecialLinearGroup.transvection zero_ne_one (1 : F), 1) v = v)
    (hr : action (1, (SpecialLinearGroup.transvection zero_ne_one (1 : F))⁻¹) v = v) :
    v 0 0 = 0 ∧ v 1 0 = 0 ∧ v 1 1 = 0 := by
  change (SpecialLinearGroup.transvection zero_ne_one (1 : F)).val * v *
    (1 : SpecialLinearGroup (Fin 2) F)⁻¹.val = v at hl
  simp only [inv_one] at hl
  change (SpecialLinearGroup.transvection zero_ne_one (1 : F)).val * v * (1 : V) = v at hl
  rw [mul_one] at hl
  have hrow (j : Fin 2) : v 1 j = 0 := by
    have h := congrArg (fun w : V => w 0 j) hl
    simpa [SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Fin.sum_univ_two] using h
  have hcol (i : Fin 2) : v i 0 = 0 := by
    have h := congrArg (fun w : V => w i 1) hr
    simpa [action_apply, SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Fin.sum_univ_two] using h
  exact ⟨hcol 0, hrow 0, hrow 1⟩

theorem finrank_le_two_of_fixed_transvections (W : Submodule (ZMod 2) V)
    (hl : ∀ v ∈ W, action (SpecialLinearGroup.transvection zero_ne_one (1 : F), 1) v = v)
    (hr : ∀ v ∈ W, action (1, (SpecialLinearGroup.transvection zero_ne_one (1 : F))⁻¹) v = v) :
    finrank (ZMod 2) W ≤ 2 := by
  let f : W →ₗ[ZMod 2] F := {
    toFun v := v.val 0 1
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro v w he
    obtain ⟨hv00, hv10, hv11⟩ := coordinates_of_fixed v (hl v v.property) (hr v v.property)
    obtain ⟨hw00, hw10, hw11⟩ := coordinates_of_fixed w (hl w w.property) (hr w w.property)
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · exact hv00.trans hw00.symm
    · exact he
    · exact hv10.trans hw10.symm
    · exact hv11.trans hw11.symm
  exact (LinearMap.finrank_le_finrank_of_injective hf).trans_eq finrank_field

theorem finrank_fixedSpace_sylow_le_two (P : Sylow 2 G) :
    finrank (ZMod 2) (fixedSpace action (P : Subgroup G)) ≤ 2 := by
  let S := SpecialLinearGroup.upperUnipotent F
  have hS : Nat.card S = 4 := by
    rw [SpecialLinearGroup.card_upperUnipotent, Nat.card_eq_fintype_card,
      Representation.SL2FourNatural.card_field]
  have hp : IsPGroup 2 (S.prod S) := by
    apply IsPGroup.of_card (n := 4)
    rw [Nat.card_congr (S.prodEquiv S).toEquiv, Nat.card_prod, hS]
    decide
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  let W := fixedSpace action (P : Subgroup G)
  let W' := W.map (action g⁻¹)
  have hfix (v : V) (hv : v ∈ W') (a : G) (ha : a ∈ S.prod S) : action a v = v := by
    obtain ⟨w, hw, rfl⟩ := hv
    have hconj : g * a * g⁻¹ ∈ P := by
      rw [← hg]
      change g * a * g⁻¹ ∈ MulAut.conj g • (Q : Set G)
      exact ⟨a, hQ ha, rfl⟩
    have he : action (g * a * g⁻¹) w = w := hw ⟨_, hconj⟩
    have hm (x y : G) (v : V) : action (x * y) v = action x (action y v) :=
      congrArg (fun f : Module.End (ZMod 2) V => f v) (action.map_mul x y)
    calc
      action a (action g⁻¹ w) = action (a * g⁻¹) w := (hm _ _ _).symm
      _ = action (g⁻¹ * (g * a * g⁻¹)) w := by rw [mul_assoc g a g⁻¹, inv_mul_cancel_left]
      _ = action g⁻¹ (action (g * a * g⁻¹) w) := hm _ _ _
      _ = action g⁻¹ w := congrArg (action g⁻¹) he
  have hu : SpecialLinearGroup.transvection zero_ne_one (1 : F) ∈ S := ⟨Multiplicative.ofAdd 1, rfl⟩
  have hb : finrank (ZMod 2) W' ≤ 2 := finrank_le_two_of_fixed_transvections W'
    (fun v hv => hfix v hv _ ⟨hu, S.one_mem⟩)
    (fun v hv => hfix v hv _ ⟨S.one_mem, S.inv_mem hu⟩)
  have hd : finrank (ZMod 2) W' = finrank (ZMod 2) W :=
    (linearAction g⁻¹).finrank_map_eq W
  exact hd.symm.le.trans hb
end ClassicalOrthogonal.FourPlusMatrix.Binary

namespace ClassicalOrthogonal.FourPlusMatrix.Binary
open Module Representation.BinaryOffender
variable {K U : Type*} [Group K] [Finite K] [AddCommGroup U]
  [Module (ZMod 2) U]

theorem finrank_le_two_of_equivariant_sylow_fixed
    (ρ : Representation (ZMod 2) K U)
    (κ : K →* G) (hκ : Function.Surjective κ) (e : U ≃ₗ[ZMod 2] V)
    (he : ∀ (k : K) (u : U), e (ρ k u) = action (κ k) (e u))
    (S : Sylow 2 K) (W : Submodule (ZMod 2) U)
    (hW : ∀ k ∈ S, ∀ u ∈ W, ρ k u = u) : finrank (ZMod 2) W ≤ 2 := by
  let P := S.mapSurjective hκ
  let f : W →ₗ[ZMod 2] fixedSpace action (P : Subgroup G) :=
    (e.toLinearMap.comp W.subtype).codRestrict _ (by
      intro u a
      obtain ⟨k, hk, ha⟩ := a.property
      change κ k = a.val at ha
      change action a.val (e u.val) = e u.val
      rw [← ha, ← he, hW k hk u.val u.property])
  have hf : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    apply e.injective
    exact congrArg Subtype.val huv
  exact (LinearMap.finrank_le_finrank_of_injective hf).trans
    (finrank_fixedSpace_sylow_le_two P)
end ClassicalOrthogonal.FourPlusMatrix.Binary
