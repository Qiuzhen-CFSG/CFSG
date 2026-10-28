module

public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.Sylow

/-!
# Inner Sylow images inside prime-group automorphism groups

The image of a Sylow subgroup in Inn(G) is Sylow. Hence a prime subgroup
of Aut(G) containing that image contains no other inner actors. This works
with a nontrivial conjugation kernel. The coordinate-change lemmas transport
subgroup stability and innerness along actual multiplicative equivalences.

Source application: Aschbacher–Smith 13.8.20, printed p.954.
-/

public section
open Subgroup
namespace MulAut
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
theorem mem_innerSylow_of_mem_inner (S : Sylow p G) (A : Subgroup (MulAut G))
    (hA : IsPGroup p A) (hSA : (S : Subgroup G).map MulAut.conj ≤ A)
    {α : MulAut G} (hα : α ∈ A) (hi : α ∈ innerSubgroup G) :
    α ∈ (S : Subgroup G).map MulAut.conj := by
  let f : G →* innerSubgroup G := MulAut.conj.rangeRestrict
  let P := S.mapSurjective (f := f) MulAut.conj.rangeRestrict_surjective
  let H := A.comap (innerSubgroup G).subtype
  have hH : IsPGroup p H := hA.comap_of_injective _ Subtype.coe_injective
  have hPH : (P : Subgroup (innerSubgroup G)) ≤ H := by
    rintro _ ⟨g,hg,rfl⟩
    exact hSA (Subgroup.mem_map_of_mem _ hg)
  have he : H = P := P.is_maximal' hH hPH
  have hm : (⟨α,hi⟩ : innerSubgroup G) ∈ (P : Subgroup (innerSubgroup G)) := he ▸ hα
  obtain ⟨g,hg,hgα⟩ := hm
  exact ⟨g,hg,congrArg Subtype.val hgα⟩
end MulAut
namespace MulAut
variable {D : Type*} [Group D]
/-- Conjugating an actor along a specified Sylow alignment preserves stability. -/
theorem aligned_actor_stable (e : D ≃* D) (U V : Subgroup D)
    (hUV : U.map e.toMonoidHom = V) (α : MulAut D)
    (hα : V.map α.toMonoidHom = V) :
    U.map ((MulAut.congr e.symm) α).toMonoidHom = U := by
  have he : ((MulAut.congr e.symm) α).toMonoidHom =
      e.symm.toMonoidHom.comp (α.toMonoidHom.comp e.toMonoidHom) := rfl
  have hback : V.map e.symm.toMonoidHom = U := by
    rw [← hUV, Subgroup.map_map]
    have hi : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id D := by
      ext x
      exact e.symm_apply_apply x
    rw [hi, Subgroup.map_id]
  rw [he, ← Subgroup.map_map, ← Subgroup.map_map, hUV, hα, hback]

/-- Innerness is preserved by a genuine change of coordinates. -/
theorem inner_of_aligned_inner (e : D ≃* D) (α : MulAut D)
    (hi : (MulAut.congr e.symm) α ∈ MulAut.innerSubgroup D) :
    α ∈ MulAut.innerSubgroup D := by
  obtain ⟨y,hy⟩ := hi
  refine ⟨e y, ?_⟩
  ext x
  have hh := DFunLike.congr_fun hy (e.symm x)
  change y * e.symm x * y⁻¹ = e.symm (α (e (e.symm x))) at hh
  have hh' := congrArg e hh
  change e y * x * (e y)⁻¹ = α x
  simpa only [map_mul, map_inv, e.apply_symm_apply] using hh'


end MulAut
