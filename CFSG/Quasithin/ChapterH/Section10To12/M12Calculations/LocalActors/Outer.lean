module

public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.Embedding
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Residual
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Automorphisms
public import Theory.Representation.BinaryPrimeDisplacement

/-!
# Outer involution displacement on the M₁₂ heart

The commutator of the two ATLAS degree-24 generators has order eleven.
The first generator is an outer involution, as witnessed by its movement of
the marked twelve-point block. Both orders are checked by the Lean kernel.
Transport through the proved full automorphism identification gives genuine
actors on every faithful extension of the heart. The order-eleven displacement
bound and the commutator rank inequality force displacement at least five;
the involution rank bound in dimension ten gives equality.

The sole remaining table premise in the outer calculation is fusion of the
outer involutions. No inversion, displacement or module dimension is a table
input. Together with the inner calculation this proves m = 4 conditionally on
that fusion premise, whose producer belongs to the parent H.11 assembly.
Source: Aschbacher–Smith H.11.1(2), printed p.392, combined manuscript of
1 March 2004. The literal generator attribution is in Extension/Seeds.lean.
-/

public section

open Subgroup Representation.BinaryOffender Sporadic.Mathieu
namespace CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors
open M12ExceptionalExtension

@[expose] def outerSeed : Carrier := ⟨generatorA, subset_closure (by simp)⟩
@[expose] def conjugatingSeed : Carrier := ⟨generatorB, subset_closure (by simp)⟩
@[expose] def elevenSeed : Carrier := outerSeed * conjugatingSeed * outerSeed⁻¹ * conjugatingSeed⁻¹

set_option maxRecDepth 4096 in
theorem outerSeed_order : orderOf outerSeed = 2 := by
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 4096 in
theorem elevenSeed_order : orderOf elevenSeed = 11 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

theorem outerSeed_not_mem_inner : outerSeed ∉ M12ExceptionalExtension.inner := by
  intro hi
  have h := blockRestriction_spec ⟨outerSeed, hi⟩ 0
  have hn : ∀ i : Fin 12, generatorA (blockLabel 0) ≠ blockLabel i := by decide +kernel
  exact hn ((blockRestriction ⟨outerSeed, hi⟩).val 0) h

@[expose] noncomputable def outerInvolution : MulAut M12 := automorphismEquiv outerSeed
@[expose] noncomputable def conjugatingAutomorphism : MulAut M12 := automorphismEquiv conjugatingSeed

theorem outerInvolution_order : orderOf outerInvolution = 2 :=
  (automorphismEquiv.orderOf_eq outerSeed).trans outerSeed_order

theorem outerInvolution_not_inner : outerInvolution ∉ MulAut.innerSubgroup M12 := by
  rintro ⟨x, hx⟩
  have he : innerModel.embedding x = outerSeed := by
    apply automorphismEquiv.injective
    rw [automorphismEquiv_embedding]
    exact hx
  apply outerSeed_not_mem_inner
  rw [← he]
  exact (innerModel.equiv x).property

theorem commutator_order_eleven :
    orderOf (outerInvolution * conjugatingAutomorphism * outerInvolution⁻¹ *
      conjugatingAutomorphism⁻¹) = 11 := by
  have he := automorphismEquiv.orderOf_eq elevenSeed
  simpa only [elevenSeed, map_mul, map_inv, outerInvolution, conjugatingAutomorphism]
    using he.trans elevenSeed_order

variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

private theorem twice_fixedCodim_le_finrank (σ : Representation (ZMod 2) H W) {t : H} (ht : t ^ 2 = 1) :
    2 * fixedCodim σ (zpowers t) ≤ Module.finrank (ZMod 2) W := by
  have hr : LinearMap.range (σ t - LinearMap.id) ≤ fixedSpace σ (zpowers t) := by
    rintro w ⟨v, rfl⟩
    rw [mem_fixedSpace_zpowers_iff]
    change σ t (σ t v - v) = σ t v - v
    have hv : σ t (σ t v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, ← pow_two, ht, map_one, Module.End.one_apply]
    rw [map_sub, hv]
    have hneg (u : W) : -u = u := by
      have hu : u + u = 0 := by
        simpa only [add_smul, one_smul, zero_smul] using
          congrArg (fun c : ZMod 2 => c • u) (by decide : (1 : ZMod 2) + 1 = 0)
      exact neg_eq_of_add_eq_zero_left hu
    simp only [sub_eq_add_neg, hneg, add_comm]
  have hrank := Submodule.finrank_mono hr
  rw [← fixedCodim_zpowers_eq_displacement_rank] at hrank
  have hdim := fixedCodim_add_finrank σ (zpowers t)
  omega

theorem fixedCodim_outerInvolution
    (σ : Representation (ZMod 2) (MulAut M12) M12Heart) (hσ : Function.Injective σ) :
    fixedCodim σ (zpowers outerInvolution) = 5 := by
  have hl := ten_le_fixedCodim_of_order_eleven σ hσ _ commutator_order_eleven
  have hb := fixedCodim_commutator_le_twice σ outerInvolution conjugatingAutomorphism
  have hu := twice_fixedCodim_le_finrank σ (outerInvolution_order ▸ pow_orderOf_eq_one outerInvolution)
  rw [finrank_m12Heart] at hu
  omega

/-- The single outer involution class, stated in the full automorphism group. -/
@[expose] def OuterInvolutionFusion : Prop :=
  ∀ s t : MulAut M12, s ∉ MulAut.innerSubgroup M12 → t ∉ MulAut.innerSubgroup M12 →
    orderOf s = 2 → orderOf t = 2 → IsConj s t

theorem fixedCodim_native_outer (hfusion : OuterInvolutionFusion)
    (σ : Representation (ZMod 2) (MulAut M12) M12Heart) (hσ : Function.Injective σ)
    {t : MulAut M12} (hto : t ∉ MulAut.innerSubgroup M12) (ht : orderOf t = 2) :
    fixedCodim σ (zpowers t) = 5 := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp
    (hfusion outerInvolution t outerInvolution_not_inner hto outerInvolution_order ht)
  rw [fixedCodim_zpowers_conj, fixedCodim_outerInvolution σ hσ]

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : M12ModuleInput ρ) (d : AmbientExtension ρ h)

include d in
omit [FiniteDimensional (ZMod 2) V] in
theorem fixedCodim_outer_involution (hfusion : OuterInvolutionFusion)
    {t : G} (hto : t ∉ solvableResidual G) (ht : orderOf t = 2) :
    fixedCodim ρ (zpowers t) = 5 := by
  rw [d.fixedCodim_map, MonoidHom.map_zpowers]
  exact fixedCodim_native_outer hfusion d.automorphismRepresentation
    d.automorphismRepresentation_faithful
    (fun hi => hto ((d.embedding_mem_inner_iff t).mp hi))
    ((orderOf_injective d.embedding d.embedding_injective t).trans ht)

include d in
/-- The ambient outer involution has exactly five fixed dimensions. -/
theorem finrank_fixedSpace_outer_involution (hfusion : OuterInvolutionFusion)
    {t : G} (hto : t ∉ solvableResidual G) (ht : orderOf t = 2) :
    Module.finrank (ZMod 2) (fixedSpace ρ (zpowers t)) = 5 := by
  have hd := fixedCodim_add_finrank ρ (zpowers t)
  rw [fixedCodim_outer_involution ρ h d hfusion hto ht, h.finrank_eq_ten ρ] at hd
  omega

include d in
theorem moduleM_eq_four (hfusion : OuterInvolutionFusion) : ChapterE.moduleM ρ = 4 :=
  moduleM_eq_four_of_outer_displacement ρ h (fun _ ho ht =>
    fixedCodim_outer_involution ρ h d hfusion ho ht)

end CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors
