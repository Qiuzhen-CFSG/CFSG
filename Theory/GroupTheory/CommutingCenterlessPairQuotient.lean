module
public import Theory.GroupTheory.CentralKernelSubgroupEmbedding
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.QuotientGroup.Basic
/-!
# Commuting centerless factors in the ambient central quotient

The central quotient is injective on each centerless embedded factor. Any overlap of their images centralizes the first factor and is consequently trivial. Their multiplication map therefore embeds the external direct product in the literal central quotient.

Source: Aschbacher–Smith 2.5.19, printed pp.560–563.
-/

public section
open Subgroup
namespace MonoidHom
variable {A B E : Type*} [Group A] [Group B] [Group E]

private theorem quotient_center_comp_injective
    (f : A →* E) (hf : Function.Injective f) (hz : center A = ⊥) :
    Function.Injective ((QuotientGroup.mk' (center E)).comp f) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  have hc : x ∈ center A := by
    apply mem_center_iff.mpr
    intro y
    apply hf
    have hfx : f x ∈ center E := (QuotientGroup.eq_one_iff (f x)).mp hx
    simpa only [map_mul] using mem_center_iff.mp hfx (f y)
  simpa only [hz,mem_bot] using hc

/-- Two commuting centerless embedded groups remain an independent product
in the literal ambient central quotient. -/
theorem central_quotient_noncommCoprod_injective
    (f : A →* E) (g : B →* E) (hf : Function.Injective f) (hg : Function.Injective g)
    (hA : center A = ⊥) (hB : center B = ⊥)
    (hc : ∀ x y, Commute (f x) (g y)) :
    Function.Injective (((QuotientGroup.mk' (center E)).comp f).noncommCoprod
      ((QuotientGroup.mk' (center E)).comp g)
      (fun x y => (hc x y).map (QuotientGroup.mk' (center E)))) := by
  let q := QuotientGroup.mk' (center E)
  let f' := q.comp f
  let g' := q.comp g
  have hfi : Function.Injective f' := quotient_center_comp_injective f hf hA
  have hgi : Function.Injective g' := quotient_center_comp_injective g hg hB
  apply (noncommCoprod_injective _ _ _).mpr
  refine ⟨hfi,hgi,disjoint_def.mpr ?_⟩
  rintro z ⟨x,rfl⟩ ⟨y,hy⟩
  have hx : x ∈ center A := by
    apply mem_center_iff.mpr
    intro w
    apply hfi
    have hcomm : Commute (f' w) (g' y) := (hc w y).map q
    rw [hy] at hcomm
    simpa only [map_mul] using hcomm.eq
  have hx1 : x = 1 := by simpa only [hA,mem_bot] using hx
  rw [hx1,map_one]
end MonoidHom
