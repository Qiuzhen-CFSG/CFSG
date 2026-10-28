module
public import Theory.GroupTheory.DihedralCyclicDerived
public import Mathlib.GroupTheory.Sylow
/-!
# Cyclic Sylow derived subgroups in sections

A subgroup of a group with cyclic derived subgroup has cyclic derived
subgroup, and so does every surjective image. Extending a subgroup Sylow
inside an ambient Sylow and lifting quotient Sylows therefore preserves
this property through every literal section map.

Source application: the odd containing rows of Aschbacher–Smith A.3.12,
pp.47–48, and their A₈-section application in 15.3.32(3), p.1133.
-/

open Subgroup
public section
namespace Theory.GroupTheory
variable {p : ℕ} [Fact p.Prime]
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
omit [Finite G] [Finite H] in
theorem derived_cyclic_of_surjective
    (f : G →* H) (hf : Function.Surjective f) (hG : IsCyclic (commutator G)) :
    IsCyclic (commutator H) := by
  let := hG
  have hm : (commutator G).map f = commutator H := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
    rfl
  rw [← hm]
  exact isCyclic_of_surjective (f.subgroupMap (commutator G)) (f.subgroupMap_surjective _)
omit [Fact p.Prime] [Finite G] [Finite H] in
theorem sylow_derived_cyclic_of_injective
    (f : G →* H) (hf : Function.Injective f)
    (hH : ∀ S : Sylow p H, IsCyclic (commutator S)) (P : Sylow p G) :
    IsCyclic (commutator P) := by
  obtain ⟨S,hS⟩ := (P.isPGroup'.map f).exists_le_sylow
  let g : P →* S := (f.comp (P : Subgroup G).subtype).codRestrict S
    (fun x => hS (mem_map_of_mem f x.property))
  exact derived_cyclic_of_injective g
    (fun x y h => Subtype.ext (hf (congrArg Subtype.val h))) (hH S)
omit [Finite H] in
theorem sylow_derived_cyclic_of_surjective
    (f : G →* H) (hf : Function.Surjective f)
    (hG : ∀ S : Sylow p G, IsCyclic (commutator S)) (P : Sylow p H) :
    IsCyclic (commutator P) := by
  obtain ⟨S,hS⟩ := Sylow.mapSurjective_surjective (p := p) hf P
  have he : (S : Subgroup G).map f = (P : Subgroup H) := by
    rw [← Sylow.coe_mapSurjective hf, hS]
  let e := MulEquiv.subgroupCongr he
  let g := e.toMonoidHom.comp (f.subgroupMap (S : Subgroup G))
  exact derived_cyclic_of_surjective g
    (e.surjective.comp (f.subgroupMap_surjective _)) (hG S)
end Theory.GroupTheory
