module
public import Theory.GroupAction.QuotientConjugation
public import Theory.Representation.InvertedCubicTransvection
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.FieldTheory.Finiteness

/-!
# The faithful binary action on a normal elementary subgroup

Conjugation on V factors through the literal centralizer quotient G/C_G(V)
and gives a faithful binary representation on Additive V. A subgroup E of
order at most two containing all commutators [g,V] bounds the displacement
range by one dimension. Over F₂ the resulting automorphism is a transvection.
This supplies the action, faithfulness, and transvection construction used
in the A₃ branch of Aschbacher–Smith C.5.13, printed p.162.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Representation
variable {G : Type*} [Group G] (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
noncomputable def centralizerQuotient :
    Representation (ZMod 2) (G ⧸ centralizer (V : Set G)) (Additive V) where
  toFun g := (MulAut.quotientConjNormal V (centralizer (V : Set G)) le_rfl g).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul (MulAut.quotientConjNormal V (centralizer (V : Set G)) le_rfl 1 v.toMul) = v
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul (MulAut.quotientConjNormal V (centralizer (V : Set G)) le_rfl (g*h) v.toMul) = _
    rw [map_mul]
    rfl

theorem centralizerQuotient_apply (g : G) (v : Additive V) :
    ((centralizerQuotient V (QuotientGroup.mk' (centralizer (V : Set G)) g) v).toMul : G) =
      g*(v.toMul : G)*g⁻¹ := rfl

theorem centralizerQuotient_faithful : Function.Injective (centralizerQuotient V).asGroupHom := by
  have hi : Function.Injective (MulAut.quotientConjNormal V (centralizer (V : Set G)) le_rfl) := by
    apply (QuotientGroup.injective_lift_iff _ _ _).mpr
    exact (MulAut.conjNormal_ker_eq_centralizer V).symm
  intro a b hab
  apply hi
  apply DFunLike.ext
  intro v
  exact Additive.ofMul.injective (congrArg (fun f => LinearMap.GeneralLinearGroup.toLinearEquiv f (Additive.ofMul v)) hab)
end Representation

namespace Representation
variable {G : Type*} [Group G] [Finite G]
variable (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]

private theorem binary_transvection_of_small_displacement
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (e : W ≃ₗ[ZMod 2] W)
    (h : Module.finrank (ZMod 2) (LinearMap.range (e.toLinearMap - LinearMap.id)) ≤ 1) :
    e ∈ LinearEquiv.transvections (ZMod 2) W := by
  obtain ⟨f,v,he⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr h
  have hf : f v = 0 := by
    rcases (by decide : ∀ z : ZMod 2, z=0 ∨ z=1) (f v) with hz | ho
    · exact hz
    have hez : e v = 0 := by
      change e.toLinearMap v=0
      rw [he,LinearMap.transvection.apply,ho,one_smul,ZModModule.add_self]
    have hv := e.map_eq_zero_iff.mp hez
    rw [hv,map_zero] at ho
    exact (zero_ne_one ho).elim
  exact LinearEquiv.mem_transvections_iff.mpr ⟨f,v,hf,by
    ext w
    exact congrArg (fun l : W →ₗ[ZMod 2] W => l w) he⟩

/-- A commutator subgroup of order at most two makes the actual quotient
conjugation a transvection. No representation or linear coordinate is assumed. -/
theorem centralizerQuotient_transvection_of_commutator_card
    (g : G) (E : Subgroup G) (hE : Nat.card E ≤ 2)
    (hcomm : ∀ v ∈ V, ⁅g,v⁆ ∈ E) :
    LinearMap.GeneralLinearGroup.toLinearEquiv
      ((centralizerQuotient V).asGroupHom (QuotientGroup.mk' (centralizer (V : Set G)) g)) ∈
        LinearEquiv.transvections (ZMod 2) (Additive V) := by
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv
    ((centralizerQuotient V).asGroupHom (QuotientGroup.mk' (centralizer (V : Set G)) g))
  let D := LinearMap.range (e.toLinearMap - LinearMap.id)
  have hDE (w : D) : (w.val.toMul : G) ∈ E := by
    obtain ⟨v,hv⟩ := w.property
    have he : (w.val.toMul : G)=⁅g,(v.toMul : G)⁆ := by
      rw [← hv]
      simp only [LinearMap.sub_apply,LinearMap.id_apply,toMul_sub,div_eq_mul_inv]
      change ((centralizerQuotient V (QuotientGroup.mk' (centralizer (V : Set G)) g) v).toMul : G) *
        (v.toMul : G)⁻¹ = _
      rw [centralizerQuotient_apply]
      rfl
    rw [he]
    exact hcomm _ v.toMul.property
  have hd : Nat.card D ≤ 2 :=
    (Nat.card_le_card_of_injective (fun w : D => (⟨w.val.toMul,hDE w⟩ : E))
      (by
        intro a b h
        apply Subtype.ext
        apply Additive.toMul.injective
        apply Subtype.ext
        exact congrArg (fun z : E => (z : G)) h)).trans hE
  apply binary_transvection_of_small_displacement
  have hn : Nat.card D = 2 ^ Module.finrank (ZMod 2) D := by
    simpa only [Nat.card_eq_fintype_card,ZMod.card] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D))
  have hpow : 2 ^ Module.finrank (ZMod 2) D ≤ 2 ^ 1 := by simpa only [pow_one,← hn] using hd
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).mp hpow
end Representation

