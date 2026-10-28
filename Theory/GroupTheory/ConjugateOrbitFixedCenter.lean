module
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
/-!
# Fixed points in a conjugate orbit

A subgroup centralizing the conjugators has the same fixed intersection
with an original subgroup as with the join of its conjugates. This retains
the actual conjugate orbit, as needed for the Sylow-center calculations in
Aschbacher–Smith 10.2.3(4), printed p.746.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- Centralizing the conjugators makes the original and orbit fixed centers equal. -/
theorem fixed_center_componentOrbit_eq (L T Z : Subgroup G)
    (hZT : Z ≤ centralizer (T : Set G)) :
    Z ⊓ centralizer (componentOrbit L T : Set G) = Z ⊓ centralizer (L : Set G) := by
  apply le_antisymm (inf_le_inf_left _ (centralizer_le (le_componentOrbit L T)))
  intro z hz
  refine ⟨hz.1,?_⟩
  have hc : componentOrbit L T ≤ centralizer ({z} : Set G) := by
    apply iSup_le
    intro t
    rintro _ ⟨l,hl,rfl⟩
    intro x hx
    have hxe : x = z := Set.mem_singleton_iff.mp hx
    rw [hxe]
    have ht : (t : G) * z = z * t := hZT hz.1 t t.property
    have hlz : l * z = z * l := hz.2 l hl
    change z * ((t : G) * l * (t : G)⁻¹) = _
    exact (((show Commute (t : G) z from ht).mul_left
      (show Commute l z from hlz)).mul_left
        (show Commute (t : G)⁻¹ z from (show Commute (t : G) z from ht).inv_left)).symm.eq
  intro l hl
  exact (hc hl z (Set.mem_singleton _)).symm
end Theory.GroupTheory
