module
public import Theory.Representation.CentralizerQuotientAction
public import Theory.Representation.NormalClosureDisplacement
/-!
# Rank-one involutions on the literal centralizer quotient

A nonzero commutator line determines the exact displacement range of the
original quotient action. Its binary dimension is one. The same automorphism
is a transvection and squares to one, and faithfulness transfers this equality
to the literal centralizer quotient actor.

Source application: Aschbacher–Smith 10.2.1, printed p.743, preparing G.6.4.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Representation
variable {G : Type*} [Group G] [Finite G]
    (W : Subgroup G) [W.Normal] [IsElementaryAbelian 2 W]

theorem centralizerQuotient_rank_one_of_commutator_line
    (g : G) (v : W) (hv : v ≠ 1)
    (hline : ∀ x∈W, ⁅g,x⁆=1 ∨ ⁅g,x⁆=(v:G))
    (hmove : ∃ x∈W, ⁅g,x⁆=(v:G)) :
    let q := QuotientGroup.mk' (centralizer (W : Set G))
    let ρ := centralizerQuotient W
    LinearMap.range (ρ (q g) - LinearMap.id) = Submodule.span (ZMod 2) {Additive.ofMul v} ∧
    Module.finrank (ZMod 2) (LinearMap.range (ρ (q g) - LinearMap.id)) = 1 ∧
    q g ≠ 1 ∧ (q g)^2=1 := by
  let q := QuotientGroup.mk' (centralizer (W : Set G))
  let ρ := centralizerQuotient W
  have hval (x : Additive W) :
      (((ρ (q g) - (LinearMap.id : Additive W →ₗ[ZMod 2] Additive W)) x).toMul : G)=⁅g,(x.toMul:G)⁆ := by
    simp only [LinearMap.sub_apply,LinearMap.id_apply,toMul_sub,div_eq_mul_inv]
    rfl
  have hi : Function.Injective (fun x : Additive W => (x.toMul : G)) :=
    Subtype.val_injective.comp Additive.toMul.injective
  have hr : LinearMap.range (ρ (q g)-LinearMap.id) =
      Submodule.span (ZMod 2) {Additive.ofMul v} := by
    apply le_antisymm
    · rintro y ⟨x,rfl⟩
      rcases hline (x.toMul:G) x.toMul.property with h | h
      · have hz : (ρ (q g)-(LinearMap.id : Additive W →ₗ[ZMod 2] Additive W)) x=0 := hi ((hval x).trans h)
        rw [hz]
        exact Submodule.zero_mem _
      · have he : (ρ (q g)-(LinearMap.id : Additive W →ₗ[ZMod 2] Additive W)) x=Additive.ofMul v := hi ((hval x).trans h)
        rw [he]
        exact Submodule.mem_span_singleton_self _
    · apply Submodule.span_le.mpr
      intro y hy
      obtain rfl := Set.mem_singleton_iff.mp hy
      obtain ⟨x,hx,he⟩ := hmove
      refine ⟨Additive.ofMul ⟨x,hx⟩,?_⟩
      exact hi ((hval _).trans he)
  have hv0 : Additive.ofMul v ≠ (0 : Additive W) := fun he => hv (Additive.ofMul.injective he)
  have hdim : Module.finrank (ZMod 2) (LinearMap.range (ρ (q g)-LinearMap.id))=1 := by
    rw [hr,finrank_span_singleton hv0]
  have hne : q g ≠ 1 := by
    intro h
    have hz : LinearMap.range (ρ (q g)-LinearMap.id)=⊥ := by
      rw [h,map_one]
      change LinearMap.range (LinearMap.id-LinearMap.id)=⊥
      rw [sub_self,LinearMap.range_zero]
    rw [hz,finrank_bot] at hdim
    omega
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom (q g))
  have htrans : e ∈ LinearEquiv.transvections (ZMod 2) (Additive W) := by
    apply centralizerQuotient_transvection_of_commutator_card W g (zpowers (v:G))
    · have hv2 : (v:G)^2=1 := elemPow_eq_one_of_isElementaryAbelian (v:G) v.property
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by decide) (orderOf_dvd_of_pow_eq_one hv2)
    · intro x hx
      rcases hline x hx with h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact mem_zpowers _
  have he2 : e^2=1 := by
    obtain ⟨f,v,hfv,he⟩ := LinearEquiv.mem_transvections_iff.mp htrans
    rw [he]
    apply LinearEquiv.ext
    intro x
    simp [pow_succ,LinearMap.transvection.apply,hfv]
    match_scalars <;> simp [ZModModule.add_self]
  have hq2 : (q g)^2=1 := by
    apply centralizerQuotient_faithful W
    rw [map_pow,map_one]
    apply Units.ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f : Additive W ≃ₗ[ZMod 2] Additive W => f x) he2
  exact ⟨hr,hdim,hne,hq2⟩
end Representation
