module

public import Theory.Representation.PSL3Two.SmallModules
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models

/-!
# Faithfulness and dimension of the small binary SL₃ modules

The natural action is the literal matrix action and its dual separates vectors.
The trace map is onto in dimension three over F₂, so its kernel has dimension
eight. A coordinate transposition moves a trace-zero matrix unit; simplicity
then makes the adjoint action faithful. Simplicity is reused from the checked
ATLAS port for these actual matrix carriers.

These properties concern the models in `SmallModules`, corresponding to
Aschbacher–Smith H.6.1, printed p.386 (1 March 2004 manuscript).
-/

public section

open Representation Representation.BinaryOffender
namespace BinaryLinearThree

/-- The natural matrix action is faithful. -/
theorem natural_injective : Function.Injective W := by
  intro g h he
  apply Matrix.SpecialLinearGroup.toLin'_injective
  exact LinearEquiv.toLinearMap_injective he

/-- The contragredient natural action is faithful. -/
theorem dual_injective : Function.Injective W.dual := by
  intro g h he
  apply inv_injective
  apply natural_injective
  apply LinearMap.ext
  intro v
  funext i
  exact congrArg (fun f : Module.Dual (ZMod 2) Vector => f v)
    (LinearMap.congr_fun he (LinearMap.proj i))

/-- The trace-zero adjoint space has binary dimension eight. -/
theorem finrank_steinberg : Module.finrank (ZMod 2) Steinberg = 8 := by
  have hsurj : Function.Surjective (LinearMap.trace (ZMod 2) Vector) := by
    intro c
    refine ⟨c • LinearMap.id, ?_⟩
    simp only [map_smul, LinearMap.trace_id]
    have hv : Module.finrank (ZMod 2) Vector = 3 := by simp [Vector, Matrix.PSL3Two.Fano.Vector]
    rw [hv]
    change c * (3 : ZMod 2) = c
    rw [show (3 : ZMod 2) = 1 by decide, mul_one]
  have hh := (LinearMap.trace (ZMod 2) Vector).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top,
    Module.finrank_self, Module.finrank_linearMap] at hh
  change 1 + Module.finrank (ZMod 2) Steinberg =
    Module.finrank (ZMod 2) Vector * Module.finrank (ZMod 2) Vector at hh
  have hv : Module.finrank (ZMod 2) Vector = 3 := by simp [Vector, Matrix.PSL3Two.Fano.Vector]
  rw [hv] at hh
  omega

private def swap01 : Group := ⟨!![0,1,0;1,0,0;0,0,1], by decide⟩
private noncomputable def matrixUnit : Steinberg :=
  ⟨(LinearMap.proj 1).smulRight (Pi.single 0 (1 : ZMod 2)), by
    change LinearMap.trace (ZMod 2) Vector _ = 0
    simp⟩

private theorem steinberg_nontrivial : S swap01 matrixUnit ≠ matrixUnit := by
  intro he
  have hh := congrArg (fun f : Steinberg => f.val (Pi.single 0 1) 1) he
  have hi : swap01⁻¹ = swap01 := by
    apply inv_eq_of_mul_eq_one_right
    decide
  change (W swap01 ((matrixUnit : Module.End (ZMod 2) Vector)
    (W swap01⁻¹ (Pi.single 0 1)))) 1 =
      (matrixUnit : Module.End (ZMod 2) Vector) (Pi.single 0 1) 1 at hh
  rw [hi] at hh
  change (1 : ZMod 2) = 0 at hh
  exact one_ne_zero hh

/-- The concrete trace-zero adjoint action is faithful. -/
theorem steinberg_injective : Function.Injective S := by
  let : IsSimpleGroup Group := Atlas.Comparisons.Exceptional.sl3Two_simple
  rcases (inferInstance : S.ker.Normal).eq_bot_or_eq_top with hb | ht
  · exact S.ker_eq_bot_iff.mp hb
  · have he : S = 1 := MonoidHom.ker_eq_top_iff.mp ht
    exact False.elim (steinberg_nontrivial (by rw [he]; rfl))

end BinaryLinearThree
