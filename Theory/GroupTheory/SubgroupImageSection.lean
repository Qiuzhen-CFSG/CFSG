module
public import Theory.GroupTheory.MarkedProductAxis

/-!
# Sections retained under a quotient coordinate change

A section of a quotient coordinate map descends to a section of the literal
subgroup image whenever the two maps have the same kernel. This preserves
the original ambient quotient map and is used to transport source centralizer
sections by the original conjugating element.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G H K : Type*} [Group G] [Group H] [Group K]

theorem exists_image_section_of_ker_eq (q : G →* H) (P : Subgroup G)
    (f : P →* K) (hf : f.ker = q.ker.subgroupOf P)
    (σ : K →* P) (hσ : f.comp σ = MonoidHom.id K) :
    ∃ τ : P.map q →* P, (q.comp P.subtype).comp τ = (P.map q).subtype := by
  let r := (q.comp P.subtype).codRestrict (P.map q) (fun x => mem_map_of_mem q x.property)
  have hr : Function.Surjective r := by
    rintro ⟨x,hx⟩
    obtain ⟨g,hg,hgx⟩ := hx
    exact ⟨⟨g,hg⟩,Subtype.ext hgx⟩
  have hkr : r.ker ≤ f.ker := by
    rw [hf]
    intro x hx
    exact congrArg (P.map q).subtype hx
  let φ := MonoidHom.liftOfSurjective r hr ⟨f,hkr⟩
  refine ⟨σ.comp φ,?_⟩
  ext x
  obtain ⟨g,rfl⟩ := hr x
  have hφ : φ (r g) = f g := by simp [φ]
  change q ((σ (φ (r g)) : P):G) = q (g:G)
  rw [hφ]
  have hh : σ (f g) * g⁻¹ ∈ f.ker := by
    change f (σ (f g) * g⁻¹) = 1
    rw [map_mul,map_inv,show f (σ (f g)) = f g from DFunLike.congr_fun hσ (f g),mul_inv_cancel]
  rw [hf] at hh
  have hz : q ((σ (f g):P):G) * (q (g:G))⁻¹ = 1 := by
    simpa only [mem_subgroupOf,MonoidHom.mem_ker,Subgroup.coe_mul,Subgroup.coe_inv,map_mul,map_inv] using hh
  exact mul_inv_eq_one.mp hz
end Theory.GroupTheory
