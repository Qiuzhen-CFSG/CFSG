module

public import Theory.LinearAlgebra.BinaryPolarity
public import Theory.Representation.BinaryPolarity.SymmetricSix
public import Theory.Representation.ElementaryPerfectSplit

/-!
# The original elementary-sixteen polarity action

An index-two subgroup of the elementary abelian group E is a binary hyperplane.
The original symmetric, self-incident point-to-hyperplane correspondence gives
an invariant alternating form on Additive E, retaining those exact subgroup
kernels. If |E|=16, symplectic coordinates and the concrete Sp₄(2)≃S₆ map yield
an injective six-letter action of the original actor.

This is the literal elementary-group input to the Rᵢ normalizer application:
ρ is the actual quotient conjugation action and π(zᵍ) is the actual E∩Qᵍ.
The source owner constructs that correspondence and subsequently uses index two
to recognize A₆. No transitive order-360 subgroup of GL₄(2) is presumed to be A₆.
Source: Aschbacher, Sporadic Groups, Lemma45.6, printed p.244.
-/

public section

open scoped IsMulCommutative
namespace BinaryPolarity
variable {E A : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E] [Group A]

private abbrev subspace : Subgroup E ≃o Submodule (ZMod 2) (Additive E) :=
  Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)

omit [Finite E] [IsElementaryAbelian 2 E] in
private theorem index_two_isCoatom (D : Subgroup E) (hi : D.index=2) : IsCoatom D := by
  refine ⟨fun ht => by simp [ht] at hi, fun B hDB => ?_⟩
  have hm := Subgroup.relIndex_mul_index hDB.le
  rw [hi] at hm
  have hp : (D.relIndex B * B.index).Prime := hm ▸ Nat.prime_two
  rcases Nat.prime_mul_iff.mp hp with ⟨_,hB⟩ | ⟨_,hr⟩
  · exact Subgroup.index_eq_one.mp hB
  · exact (hDB.not_ge (Subgroup.relIndex_eq_one.mp hr)).elim

private noncomputable def linearAut (g : MulAut E) : Additive E ≃ₗ[ZMod 2] Additive E :=
  g.toAdditive.toLinearEquiv (fun c x => ZMod.map_smul g.toAdditive.toAddMonoidHom c x)

private noncomputable def linearHyperplanes
    (π : {x : E // x≠1} → {D : Subgroup E // D.index=2})
    (x : {x : Additive E // x≠0}) :
    {W : Submodule (ZMod 2) (Additive E) // IsCoatom W} :=
  ⟨subspace (π ⟨x.val.toMul,x.property⟩).val,
    (subspace.isCoatom_iff _).mpr (index_two_isCoatom _ (π ⟨x.val.toMul,x.property⟩).property)⟩

omit [Finite E] in
theorem exists_invariant_form_of_elementary_hyperplanes
    (ρ : A →* MulAut E)
    (π : {x : E // x≠1} → {D : Subgroup E // D.index=2})
    (hs : ∀ x y : {x : E // x≠1}, x.val∈(π y).val ↔ y.val∈(π x).val)
    (ha : ∀ x, x.val∈(π x).val)
    (he : ∀ (a : A) (x : {x : E // x≠1}),
      (π ⟨ρ a x,fun h => x.property ((ρ a).map_eq_one_iff.mp h)⟩).val =
        (π x).val.map (ρ a).toMonoidHom) :
    ∃ B : LinearMap.BilinForm (ZMod 2) (Additive E), B.IsAlt ∧ B.Nondegenerate ∧
      (∀ a x y, B (Additive.ofMul (ρ a x.toMul)) (Additive.ofMul (ρ a y.toMul))=B x y) ∧
      ∀ (x : {x : E // x≠1}) (y : E),
        B (Additive.ofMul x) (Additive.ofMul y)=0 ↔ y∈(π x).val := by
  let P := linearHyperplanes π
  obtain ⟨B,hA,hN,hB⟩ := exists_form_of_hyperplanes P
    (fun x y => hs ⟨x.val.toMul,x.property⟩ ⟨y.val.toMul,y.property⟩)
    (fun x => ha ⟨x.val.toMul,x.property⟩)
  refine ⟨B,hA,hN,?_,?_⟩
  · intro a x y
    apply invariant_of_hyperplane_equivariance P B hB (linearAut (ρ a)) ?_ x y
    intro v
    ext w
    change w.toMul∈(π ⟨ρ a v.val.toMul,_⟩).val ↔ _
    rw [he a ⟨v.val.toMul,v.property⟩]
    constructor
    · rintro ⟨z,hz,hzw⟩
      exact ⟨Additive.ofMul z,hz,congrArg Additive.ofMul hzw⟩
    · rintro ⟨z,hz,hzw⟩
      exact ⟨z.toMul,hz,congrArg Additive.toMul hzw⟩
  · intro x y
    exact hB ⟨Additive.ofMul x,x.property⟩ (Additive.ofMul y)

theorem exists_injective_six_action_of_elementary_polarity
    (hE : Nat.card E=16) (ρ : A →* MulAut E) (hf : Function.Injective ρ)
    (π : {x : E // x≠1} ≃ {D : Subgroup E // D.index=2})
    (hs : ∀ x y : {x : E // x≠1}, x.val∈(π y).val ↔ y.val∈(π x).val)
    (ha : ∀ x, x.val∈(π x).val)
    (he : ∀ (a : A) (x : {x : E // x≠1}),
      (π ⟨ρ a x,fun h => x.property ((ρ a).map_eq_one_iff.mp h)⟩).val =
        (π x).val.map (ρ a).toMonoidHom) :
    ∃ φ : A →* Equiv.Perm (Fin 6), Function.Injective φ := by
  obtain ⟨B,hAlt,hN,hB,_⟩ := exists_invariant_form_of_elementary_hyperplanes ρ π hs ha he
  let σ := Representation.elementaryRepresentation (p:=2) ρ
  have hσ : Function.Injective σ := by
    intro a b hab
    apply hf
    ext x
    exact congrArg Additive.toMul (congrArg (fun f => f (Additive.ofMul x)) hab)
  have hd : Module.finrank (ZMod 2) (Additive E)=4 := by
    apply Nat.pow_right_injective (by decide : 2≤2)
    have hc := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive E)
    rw [Nat.card_zmod] at hc
    exact hc.symm.trans hE
  exact exists_injective_six_action_of_form σ hσ hd B hAlt hN hB
end BinaryPolarity
