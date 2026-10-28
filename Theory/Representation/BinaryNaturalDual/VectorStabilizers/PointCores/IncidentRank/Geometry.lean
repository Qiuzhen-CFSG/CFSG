module

public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.PointCores

/-!
# Coordinates of the binary incident flag radical

Choose t with f(t) = 1 and write V = F₂ t ⊕ H, where H = ker(f).
An element of the actual radical is uniquely determined by its displacement
of t in H and its restriction in the line radical fixing x in H. Conversely,
every such pair is realized by a transverse shear followed by extension of
the hyperplane operator. The multiplication rule is the natural semidirect
product rule. In dimension four the two parameter spaces have orders eight
and four, giving order 32 for the actual flag-(1,3) radical.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1(6),
geometric argument on printed p.103, used on printed p.1145.
-/

public section

open Subgroup BinaryLinear
namespace BinaryNaturalDual.VectorStabilizers.PointCores
open Theory.LinearAlgebra
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {x t : V} {f : Module.Dual (ZMod 2) V}

private theorem projection_on_kernel (ht : f t = 1) (v : f.ker) :
    kernelProjection ht v = v := by
  apply Subtype.ext
  simp only [kernelProjection_apply, show f v = 0 from v.property, zero_smul, sub_zero]

/-- Restriction of the flag radical is the line radical of its hyperplane. -/
def incidentRadicalRestriction (hfx : f x = 0) :
    incidentRadical x f →* Pure.pointKernel (⟨x, hfx⟩ : f.ker) where
  toFun g := ⟨incidentRestriction hfx ⟨g.val, g.property.1⟩, by
    apply (BinaryFivePointStabilizer.mem_kernel_iff _ _).mpr
    intro v
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (g.property.2 v v.property)
    exact Submodule.mem_span_singleton.mpr ⟨a, Subtype.ext ha⟩⟩
  map_one' := by apply Subtype.ext; exact (incidentRestriction hfx).map_one
  map_mul' g k := by apply Subtype.ext; apply Subtype.ext; ext v; rfl

@[simp] theorem incidentRadicalRestriction_apply (hfx : f x = 0)
    (g : incidentRadical x f) (v : f.ker) :
    ((incidentRadicalRestriction hfx g).val.val v : V) = g.val v := by rfl

private def transverseDisplacement (g : incidentRadical x f) (t : V) : f.ker :=
  ⟨g.val t - t, by
    change f (g.val t - t) = 0
    rw [map_sub, g.property.1.2, sub_self]⟩

/-- The actual operator in coordinates V = F₂ t ⊕ ker(f). -/
theorem incidentRadical_action_decomposition (ht : f t = 1) (hfx : f x = 0)
    (g : incidentRadical x f) (v : V) :
    g.val v = f v • (t + (g.val t - t)) +
      ((incidentRadicalRestriction hfx g).val.val (kernelProjection ht v) : V) := by
  rw [incidentRadicalRestriction_apply, kernelProjection_apply, map_sub, map_smul]
  module

private def transverseShear (w : f.ker) : BinaryLinear.GL V where
  toLinearMap := LinearMap.id + f.smulRight (w : V)
  invFun v := v - f v • (w : V)
  left_inv v := by
    change v + f v • (w : V) - f (v + f v • (w : V)) • (w : V) = v
    simp
  right_inv v := by
    change v - f v • (w : V) + f (v - f v • (w : V)) • (w : V) = v
    simp

private def radicalTranslate (hfx : f x = 0) (w : f.ker) : incidentRadical x f :=
  ⟨transverseShear w, by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change x + f x • (w : V) = x
      simp [hfx]
    · intro v
      change f (v + f v • (w : V)) = f v
      simp
    · intro v hv
      change v + f v • (w : V) - v ∈ Submodule.span (ZMod 2) {x}
      simp [hv]⟩

private def radicalExtend (ht : f t = 1) (hfx : f x = 0)
    (k : Pure.pointKernel (⟨x, hfx⟩ : f.ker)) : incidentRadical x f :=
  ⟨extendKernel ht k.val.val, by
    refine ⟨⟨?_, (extendKernel_mem ht k.val.val).2⟩, ?_⟩
    · rw [extendKernel_apply, hfx, zero_smul, zero_add]
      have hp := projection_on_kernel ht (⟨x, hfx⟩ : f.ker)
      rw [hp]
      exact congrArg Subtype.val k.val.property
    · intro v hv
      rw [extendKernel_apply, hv, zero_smul, zero_add]
      have hp := projection_on_kernel ht (⟨v, hv⟩ : f.ker)
      rw [hp]
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
        ((BinaryFivePointStabilizer.mem_kernel_iff _ _).mp k.property ⟨v, hv⟩)
      exact Submodule.mem_span_singleton.mpr ⟨a, congrArg Subtype.val ha⟩⟩

private def parameterMap (_ht : f t = 1) (hfx : f x = 0) :
    incidentRadical x f → f.ker × Pure.pointKernel (⟨x, hfx⟩ : f.ker) :=
  fun g => (transverseDisplacement g t, incidentRadicalRestriction hfx g)

private theorem parameterMap_injective (ht : f t = 1) (hfx : f x = 0) :
    Function.Injective (parameterMap ht hfx) := by
  intro g k he
  have hw := congrArg (fun p : f.ker × Pure.pointKernel (⟨x, hfx⟩ : f.ker) => (p.1 : V)) he
  have hr := congrArg Prod.snd he
  change g.val t - t = k.val t - t at hw
  change incidentRadicalRestriction hfx g = incidentRadicalRestriction hfx k at hr
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  rw [incidentRadical_action_decomposition ht hfx g,
    incidentRadical_action_decomposition ht hfx k, hw, hr]

private theorem parameterMap_surjective (ht : f t = 1) (hfx : f x = 0) :
    Function.Surjective (parameterMap ht hfx) := by
  rintro ⟨w, k⟩
  refine ⟨radicalTranslate hfx w * radicalExtend ht hfx k, ?_⟩
  have he_t : extendKernel ht k.val.val t = t := by
    rw [extendKernel_apply, ht, one_smul]
    have hp : kernelProjection ht t = 0 := by apply Subtype.ext; simp [ht]
    rw [hp, map_zero]
    simp
  apply Prod.ext
  · apply Subtype.ext
    change (transverseShear w) (extendKernel ht k.val.val t) - t = (w : V)
    rw [he_t]
    change t + f t • (w : V) - t = (w : V)
    simp [ht]
  · apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    change (transverseShear w) (extendKernel ht k.val.val v) = (k.val.val v : V)
    rw [extendKernel_apply, v.property, zero_smul, zero_add, projection_on_kernel ht v]
    change (k.val.val v : V) + f (k.val.val v : V) • (w : V) = (k.val.val v : V)
    simp only [show f (k.val.val v : V) = 0 from (k.val.val v).property, zero_smul, add_zero]

/-- Parameters for every element of the actual flag radical: its transverse
 displacement and its line-radical restriction to the hyperplane. -/
noncomputable def incidentRadicalEquivParameters (ht : f t = 1) (hfx : f x = 0) :
    incidentRadical x f ≃ f.ker × Pure.pointKernel (⟨x, hfx⟩ : f.ker) :=
  Equiv.ofBijective (parameterMap ht hfx)
    ⟨parameterMap_injective ht hfx, parameterMap_surjective ht hfx⟩

/-- The transverse parameter is the displacement of the chosen vector outside the hyperplane. -/
@[simp] theorem incidentRadicalEquivParameters_fst (ht : f t = 1) (hfx : f x = 0)
    (g : incidentRadical x f) :
    ((incidentRadicalEquivParameters ht hfx g).1 : V) = g.val t - t := by rfl

/-- The second parameter is the actual hyperplane restriction. -/
@[simp] theorem incidentRadicalEquivParameters_snd (ht : f t = 1) (hfx : f x = 0)
    (g : incidentRadical x f) :
    (incidentRadicalEquivParameters ht hfx g).2 = incidentRadicalRestriction hfx g := by rfl

/-- The parameters multiply by the natural semidirect-product rule. -/
theorem incidentRadicalEquivParameters_mul (ht : f t = 1) (hfx : f x = 0)
    (g k : incidentRadical x f) :
    incidentRadicalEquivParameters ht hfx (g * k) =
      ((incidentRadicalEquivParameters ht hfx g).1 +
        (incidentRadicalRestriction hfx g).val.val (incidentRadicalEquivParameters ht hfx k).1,
       (incidentRadicalEquivParameters ht hfx g).2 *
        (incidentRadicalEquivParameters ht hfx k).2) := by
  apply Prod.ext
  · apply Subtype.ext
    change g.val (k.val t) - t = (g.val t - t) + g.val (k.val t - t)
    rw [map_sub]
    abel
  · exact (incidentRadicalRestriction hfx).map_mul g k

/-- The concrete flag radical in four dimensions has order 32. -/
theorem incidentRadical_card_eq_thirty_two
    {x : Fin 4 → ZMod 2} {f : Module.Dual (ZMod 2) (Fin 4 → ZMod 2)}
    (hx : x ≠ 0) (hf : f ≠ 0) (hfx : f x = 0) :
    Nat.card (incidentRadical x f) = 32 := by
  have ht : ∃ t, f t ≠ 0 := by
    by_contra! ht
    exact hf (LinearMap.ext ht)
  obtain ⟨t, ht⟩ := ht
  have ht1 : f t = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ ht
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  rw [Module.finrank_pi, Fintype.card_fin] at hd
  have hd3 : Module.finrank (ZMod 2) f.ker = 3 := by omega
  have hxH : (⟨x, hfx⟩ : f.ker) ≠ 0 := fun he => hx (congrArg Subtype.val he)
  rw [Nat.card_congr (incidentRadicalEquivParameters ht1 hfx), Nat.card_prod,
    Pure.pointKernel_card hxH, Module.natCard_eq_pow_finrank (K := ZMod 2),
    hd3, Nat.card_zmod]
  norm_num

end BinaryNaturalDual.VectorStabilizers.PointCores
