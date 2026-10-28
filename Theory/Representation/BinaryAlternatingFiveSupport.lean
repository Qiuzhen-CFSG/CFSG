module
public import Theory.Representation.BinaryOffender.InvariantAction
public import Theory.Representation.BinaryPermutation
public import Mathlib.GroupTheory.SpecificGroups.Alternating
/-!
# Supported actors in a natural A₅ summand

In a faithful split action, an actor fixing the component's fixed complement
has every ambient commutator in that component. On the natural summand this
follows because permutation commutators are even; on the complement it follows
from normality. Faithfulness identifies the two ambient elements.
Source application: Aschbacher–Smith, 13.6.15, printed p.930.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement
namespace BinaryPermutation.AlternatingFiveSupport
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]

theorem commutator_mem_component
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (C : Subgroup D) [C.Normal]
    (I : Submodule (ZMod 2) W) (e : I ≃ₗ[ZMod 2] natural (Fin 5))
    (c : C ≃* alternatingGroup (Fin 5))
    (r : D →* Equiv.Perm (Fin 5)) (hr : ∀ k : C, r k.val = (c k).val)
    (he : ∀ g (w : I), ρ g w = (e.symm (naturalRepresentation (Fin 5) (r g) (e w)) : W))
    (hs : IsCompl I (fixedSpace ρ C))
    (a : D) (ha : ∀ x ∈ fixedSpace ρ C, ρ a x=x) (d : D) : ⁅d,a⁆ ∈ C := by
  let g := ⁅d,a⁆
  have hrg : r g ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    change (Equiv.Perm.sign.comp r) ⁅d,a⁆ = 1
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  let k : C := c.symm ⟨r g,hrg⟩
  have hrk : r k.val = r g := (hr k).trans (congrArg Subtype.val (c.apply_symm_apply _))
  have hfg : ∀ x ∈ fixedSpace ρ C, ρ g x=x := by
    intro x hx
    have hxa : ρ a⁻¹ x=x := (ρ.inv_apply_eq_iff).mpr (ha x hx).symm
    have hdx : ρ d⁻¹ x ∈ fixedSpace ρ C :=
      (fixedSpace_stable_of_normal ρ C (mem_top d⁻¹) x).mpr hx
    change ρ (d*a*d⁻¹*a⁻¹) x=x
    simp only [map_mul,Module.End.mul_apply]
    rw [hxa,ha _ hdx,ρ.self_inv_apply]
  have hgk : g=k.val := by
    apply hf
    apply LinearMap.ext
    intro x
    have hx : x ∈ I ⊔ fixedSpace ρ C := hs.sup_eq_top.symm ▸ Submodule.mem_top
    obtain ⟨w,hw,z,hz,rfl⟩ := Submodule.mem_sup.mp hx
    have hzk : ρ k.val z=z := hz k
    rw [map_add,map_add,hfg z hz,hzk]
    congr 1
    have hm := he k.val ⟨w,hw⟩
    rw [hrk] at hm
    exact (he g ⟨w,hw⟩).trans hm.symm
  change g ∈ C
  rw [hgk]
  exact k.property
end BinaryPermutation.AlternatingFiveSupport
