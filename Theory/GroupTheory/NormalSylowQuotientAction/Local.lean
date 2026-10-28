module
public import Theory.GroupTheory.NormalSylowQuotientAction

/-!
# Quotient displacements from a local Sylow

A finite local subgroup L has Sylow R=S∩L inside a two-group S normalizing
L. If the embedded normalizer of R preserves S, the induced S-action on
any quotient of L preserves the quotient Sylow and is trivial on its
normalizer modulo that Sylow. The proof works entirely in the original
local group and does not require S to be Sylow in the ambient group.

This is the local action step in Aschbacher–Smith F.1.12, printed p.264.
The actual F.1.1 consumer supplies R from its local Sylow hypothesis.
-/

public section
open Subgroup
namespace Subgroup.NormalSylowQuotientAction
variable {G H : Type*} [Group G] [Group H] {p : ℕ} [Fact p.Prime]

/-- Relative Borel normality controls the original quotient action using
only the specified local Sylow subgroup. -/
theorem quotient_displacements_of_local_sylow
    (S L : Subgroup G) [Finite L] (hSL : S ≤ normalizer (L : Set G))
    (R : Sylow p L) (hR : (R : Subgroup L) = S.subgroupOf L)
    (hBS : (normalizer (R : Set L)).map L.subtype ≤ normalizer (S : Set G))
    (f : L →* H) (hf : Function.Surjective f)
    (a : S → MulAut H)
    (ha : ∀ (s : S) (x : L), a s (f x) =
      f (L.normalizerMonoidHom ⟨s, hSL s.property⟩ x)) :
    ∃ P : Sylow p H,
      (P : Subgroup H) = (S.subgroupOf L).map f ∧
      ∀ s : S, (P : Subgroup H).map (a s).toMonoidHom = P ∧
        ∀ x ∈ normalizer (P : Set H), x⁻¹ * a s x ∈ (P : Subgroup H) := by
  have hstable (s : S) :
      (S.subgroupOf L).map (L.normalizerMonoidHom ⟨s,hSL s.property⟩).toMonoidHom =
        S.subgroupOf L := by
    have hmap (s : S) :
        (S.subgroupOf L).map (L.normalizerMonoidHom ⟨s,hSL s.property⟩).toMonoidHom ≤
          S.subgroupOf L := by
      rintro x ⟨y,hy,rfl⟩
      change (L.normalizerMonoidHom ⟨s,hSL s.property⟩ y : G) ∈ S
      rw [normalizerMonoidHom_apply_apply_coe]
      exact S.mul_mem (S.mul_mem s.property hy) (S.inv_mem s.property)
    apply le_antisymm (hmap s)
    intro x hx
    have hi := hmap s⁻¹ (mem_map_of_mem _ hx)
    refine mem_map.mpr ⟨_,hi,?_⟩
    change L.normalizerMonoidHom ⟨s,hSL s.property⟩
      (L.normalizerMonoidHom ⟨(s:G)⁻¹,hSL (S.inv_mem s.property)⟩ x) = x
    rw [show (⟨(s:G)⁻¹,hSL (S.inv_mem s.property)⟩ : normalizer (L:Set G)) =
      (⟨s,hSL s.property⟩ : normalizer (L:Set G))⁻¹ from rfl, map_inv]
    exact (L.normalizerMonoidHom ⟨s,hSL s.property⟩).apply_symm_apply x
  refine ⟨R.mapSurjective hf,?_,?_⟩
  · change (R : Subgroup L).map f = _
    rw [hR]
  · intro s
    have he : (a s).toMonoidHom.comp f =
        f.comp (L.normalizerMonoidHom ⟨s,hSL s.property⟩).toMonoidHom := by
      ext x
      exact ha s x
    constructor
    · change ((R : Subgroup L).map f).map (a s).toMonoidHom = (R : Subgroup L).map f
      rw [hR, map_map, he, ←map_map, hstable]
    · intro x hx
      change x ∈ normalizer ((R : Subgroup L).map f : Set H) at hx
      rw [←R.normalizer_map_surjective f hf] at hx
      obtain ⟨y,hy,rfl⟩ := hx
      change (f y)⁻¹ * a s (f y) ∈ (R : Subgroup L).map f
      rw [ha, ←map_inv, ←map_mul]
      apply mem_map_of_mem
      rw [hR]
      have hyB : (y:G) ∈ (normalizer (R:Set L)).map L.subtype :=
        mem_map_of_mem L.subtype hy
      have hc : (y:G)⁻¹ * (s:G) * y ∈ S :=
        (mem_normalizer_iff''.mp (hBS hyB) s).mp s.property
      change (y⁻¹ * L.normalizerMonoidHom ⟨s,hSL s.property⟩ y : L).val ∈ S
      rw [coe_mul,coe_inv,normalizerMonoidHom_apply_apply_coe]
      simpa only [mul_assoc] using S.mul_mem hc (S.inv_mem s.property)

end Subgroup.NormalSylowQuotientAction
