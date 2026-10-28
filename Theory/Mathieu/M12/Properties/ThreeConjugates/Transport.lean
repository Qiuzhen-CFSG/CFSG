module
public import Theory.Mathieu.M12.Properties.ThreeConjugates.Certificates
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Automorphisms
public import Theory.GroupTheory.ThreeConjugateAutomorphisms
/-!
# Transport of three-conjugate generation in the M₁₂ extension

Normality of the marked inner subgroup keeps both conjugators inner under
arbitrary ambient conjugation. The proved automorphism equivalence then carries
the literal subgroup containment to the actual inner automorphism group.
This connects the finite ATLAS permutation certificates to the group used in
the Chapter K degree-window reduction (printed pp.451 and 457).
-/

public section
namespace Sporadic.Mathieu.M12ThreeConjugates
open M12ExceptionalExtension Subgroup

theorem generates_conjugate {t : Carrier} (ht : Generates t) (k : Carrier) :
    Generates (k * t * k⁻¹) := by
  have hn : inner.Normal := normal_of_index_eq_two inner_index
  obtain ⟨g, hg, h, hh, hgen⟩ := ht
  refine ⟨k * g * k⁻¹, hn.conj_mem g hg k,
    k * h * k⁻¹, hn.conj_mem h hh k, ?_⟩
  let D := zpowers t ⊔ zpowers (g * t * g⁻¹) ⊔ zpowers (h * t * h⁻¹)
  have hmap : D.map (MulAut.conj k).toMonoidHom =
      zpowers (k * t * k⁻¹) ⊔
      zpowers ((k * g * k⁻¹) * (k * t * k⁻¹) * (k * g * k⁻¹)⁻¹) ⊔
      zpowers ((k * h * k⁻¹) * (k * t * k⁻¹) * (k * h * k⁻¹)⁻¹) := by
    simp only [D, Subgroup.map_sup, MonoidHom.map_zpowers, map_mul, map_inv,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [← hmap]
  intro x hx
  refine ⟨k⁻¹ * x * k, hgen ?_, ?_⟩
  · simpa only [inv_inv] using hn.conj_mem x hx k⁻¹
  · change k * (k⁻¹ * x * k) * k⁻¹ = x
    group

theorem generates_of_isConj {s t : Carrier} (hs : Generates s) (h : IsConj s t) :
    Generates t := by
  obtain ⟨k, rfl⟩ := isConj_iff.mp h
  exact generates_conjugate hs k

theorem automorphisms_of_carrier
    (h : ∀ t : Carrier, t ≠ 1 → t ^ 2 = 1 → Generates t) :
    Theory.GroupTheory.ThreeConjugateAutomorphisms M12 := by
  intro t ht ht2
  obtain ⟨s, rfl⟩ := automorphismEquiv.surjective t
  have hs : s ≠ 1 := by intro h; apply ht; rw [h, map_one]
  have hs2 : s ^ 2 = 1 := by
    apply automorphismEquiv.injective
    simpa only [map_pow, map_one] using ht2
  obtain ⟨g, hg, k, hk, hgen⟩ := h s hs hs2
  rw [← innerModel.embedding_range] at hg hk
  obtain ⟨g, rfl⟩ := hg
  obtain ⟨k, rfl⟩ := hk
  refine ⟨g, k, ?_⟩
  have hm := Subgroup.map_mono (f := automorphismEquiv.toMonoidHom) hgen
  rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers,
    MonoidHom.map_zpowers, MonoidHom.map_zpowers] at hm
  simp only [map_mul, map_inv, MulEquiv.coe_toMonoidHom,
    automorphismEquiv_embedding] at hm
  apply le_trans ?_ hm
  rintro x ⟨a, rfl⟩
  exact ⟨innerModel.embedding a, innerModel.embedding_range ▸ ⟨a, rfl⟩,
    automorphismEquiv_embedding a⟩
end Sporadic.Mathieu.M12ThreeConjugates
