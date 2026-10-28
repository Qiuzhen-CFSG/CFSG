module

public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Mathlib.GroupTheory.Sylow

/-!
# Conjugate elements with simultaneously marked centralizer Sylows

Conjugation of the elements identifies their centralizers. Sylow conjugacy
inside the target centralizer adjusts that conjugator to carry the chosen
Sylow subgroups as well. Both ambient maps are retained.

Source application: Aschbacher--Smith F.5.5, printed pp.301--302.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise

namespace Sylow
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_conj_element_and_centralizer_sylow (x y : G) (hxy : IsConj x y)
    (P : Sylow p (centralizer ({x} : Set G)))
    (Q : Sylow p (centralizer ({y} : Set G))) :
    ∃ g : G, MulAut.conj g x = y ∧
      ((P : Subgroup (centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype).map
        (MulAut.conj g).toMonoidHom =
      (Q : Subgroup (centralizer ({y} : Set G))).map (centralizer ({y} : Set G)).subtype := by
  obtain ⟨g,hg⟩ := isConj_iff.mp hxy
  let e : centralizer ({x} : Set G) ≃* centralizer ({y} : Set G) :=
    ((MulAut.conj g).subgroupMap (centralizer ({x} : Set G))).trans
      (MulEquiv.subgroupCongr ((CentralizerSmallKernelTransport.map_centralizer
        (MulAut.conj g) x).trans (congrArg (fun x : G => centralizer ({x} : Set G)) hg)))
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨k,hk⟩ := MulAction.exists_smul_eq (centralizer ({y} : Set G)) P' Q
  have hkm : (P' : Subgroup (centralizer ({y} : Set G))).map
      (MulAut.conj k).toMonoidHom = Q := by
    rw [←hk,Sylow.coe_subgroup_smul]
    rfl
  refine ⟨k.val*g,?_,?_⟩
  · change (k.val*g)*x*(k.val*g)⁻¹=y
    have hfix : k.val*y*k.val⁻¹=y :=
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp k.property)
    calc
      _ = k.val*(g*x*g⁻¹)*k.val⁻¹ := by group
      _ = y := by rw [hg,hfix]
  · have hh := congrArg (fun K : Subgroup (centralizer ({y} : Set G)) =>
      K.map (centralizer ({y} : Set G)).subtype) hkm
    change (((P : Subgroup (centralizer ({x} : Set G))).map e.toMonoidHom).map
      (MulAut.conj k).toMonoidHom).map (centralizer ({y} : Set G)).subtype = _ at hh
    rw [map_map,map_map] at hh
    rw [map_map]
    convert hh using 1
    congr 1
    ext a
    change (k.val*g)*a.val*(k.val*g)⁻¹=k.val*(g*a.val*g⁻¹)*k.val⁻¹
    group

end Sylow
