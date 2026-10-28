module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
A full local action can be matched inside a specified Sylow subgroup, so a crossing is adjusted without changing its Sylow position.
Source application: Aschbacher--Smith 2.5.15, printed pp.558--559.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem exists_sylow_adjustment_to_centralizer
    (R C M : Subgroup G) (hCN : C ≤ normalizer (R : Set G))
    (hMN : M ≤ normalizer (R : Set G)) (hM : IsPGroup 2 M)
    (P : Sylow 2 C)
    (hPM : (P : Subgroup C).map C.subtype ≤ M)
    (hsurj : Function.Surjective (R.normalizerMonoidHom.comp (inclusion hCN)))
    (x : G) (hx : x ∈ M) :
    ∃ p : C, p ∈ P ∧ (p : G)⁻¹*x ∈ centralizer (R : Set G) := by
  let α := R.normalizerMonoidHom.comp (inclusion hCN)
  let β := R.normalizerMonoidHom.comp (inclusion hMN)
  let Q := P.mapSurjective hsurj
  have hQle : (Q : Subgroup (MulAut R)) ≤ β.range := by
    rintro _ ⟨p,hp,rfl⟩
    exact ⟨⟨p,hPM (mem_map_of_mem C.subtype hp)⟩,rfl⟩
  have hβp : IsPGroup 2 β.range := hM.of_surjective β.rangeRestrict β.rangeRestrict_surjective
  have heq : β.range = (Q : Subgroup (MulAut R)) := Q.is_maximal' hβp hQle
  have hxQ : β ⟨x,hx⟩ ∈ (P : Subgroup C).map α := by
    change β ⟨x,hx⟩ ∈ (Q : Subgroup (MulAut R))
    exact heq ▸ (show β ⟨x,hx⟩ ∈ β.range from ⟨⟨x,hx⟩,rfl⟩)
  obtain ⟨p,hp,hpx⟩ := hxQ
  refine ⟨p,hp,?_⟩
  let pp : normalizer (R : Set G) := inclusion hCN p
  let xx : normalizer (R : Set G) := inclusion hMN ⟨x,hx⟩
  have hk : pp⁻¹*xx ∈ R.normalizerMonoidHom.ker := by
    apply MonoidHom.mem_ker.mpr
    change R.normalizerMonoidHom pp = R.normalizerMonoidHom xx at hpx
    rw [map_mul,map_inv,hpx,inv_mul_cancel]
  rw [normalizerMonoidHom_ker] at hk
  exact hk
end Subgroup
