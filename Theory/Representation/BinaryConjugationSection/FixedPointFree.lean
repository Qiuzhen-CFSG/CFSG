module
public import Theory.Representation.BinaryConjugationSection
public import Mathlib.GroupTheory.FixedPointFree

/-!
# Full commutators lifted from a fixed-point-free section action

If one element of an actor subgroup acts fixed-point-freely on a finite
binary section, its commutator map is surjective. The original section
coordinates lift this to S=[S,B]E in the ambient group. This separates
the lifting argument from any particular natural-module recognition.

Source application: Aschbacher–Smith,G.2.4(8), printed p.335.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] {H S E : Subgroup G}
  {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
  {ρ : Representation (ZMod 2) H M}

theorem section_eq_commutator_sup_of_fixedPointFree
    (c : BinaryConjugationSection H S E ρ) (B : Subgroup G) (hB : B≤H)
    (t : H) (ht : t.val∈B) (hf : ∀v,ρ t v=v→v=0) : S=⁅S,B⁆⊔E := by
  let α : Multiplicative M→*Multiplicative M := (ρ t).toAddMonoidHom.toMultiplicative
  have hfree : MonoidHom.FixedPointFree α := by
    intro x hx
    exact Multiplicative.toAdd.injective (hf x.toAdd (congrArg Multiplicative.toAdd hx))
  have hc : ⁅S,B⁆≤S := le_normalizer_iff_commutator_le_left.mp (hB.trans c.normalized)
  apply le_antisymm ?_ (sup_le hc c.kernel_le)
  intro x hx
  let xS : S := ⟨x,hx⟩
  obtain ⟨y,hy⟩ := hfree.commutatorMap_surjective (c.coordinates xS)
  obtain ⟨z,rfl⟩ := c.onto y
  let zt : S := ⟨t.val*z.val*t.val⁻¹,
    (mem_normalizer_iff.mp (c.normalized t.property) z.val).mp z.property⟩
  have hα : c.coordinates zt=α (c.coordinates z) :=
    Multiplicative.toAdd.injective (c.equivariant t z)
  change c.coordinates z / α (c.coordinates z)=c.coordinates xS at hy
  rw [←hα,←map_div] at hy
  let w := z/zt
  have hw : w.val∈⁅S,B⁆ := by
    have he : w.val=⁅z.val,t.val⁆ := by
      dsimp [w,zt]
      simp only [commutatorElement_def,div_eq_mul_inv,mul_inv_rev,inv_inv]
      group
    rw [he]
    exact commutator_mem_commutator z.property ht
  have hxw : x/w.val∈E := by
    apply (c.coordinates_eq_one_iff (xS/w)).mp
    rw [map_div,hy,div_self']
  have hh := (⁅S,B⁆⊔E).mul_mem (mem_sup_right hxw) (mem_sup_left hw)
  simpa only [div_mul_cancel] using hh

end Representation.BinaryConjugationSection
end
