module

public import Theory.GroupTheory.ElementFusionTransport

/-!
# Uniqueness of a conjugate through a controlled element

Fusion control corrects a conjugator into the centralizer of a marked element.
If this centralizer normalizes the subgroup, there is just one conjugate
containing that element. Conjugation by the normalizer extends uniqueness
to its whole orbit.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), Lemma 13.6.24(1), printed p.933.
-/

namespace Subgroup

variable {G : Type*} [Group G] (V : Subgroup G) (v : G)

/-- Fusion control and centralizer containment give uniqueness through `v`. -/
public theorem conjugate_eq_of_fusion_of_centralizer_le_normalizer
    (hfusion : ∀ a : G, MulAut.conj a v ∈ V →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v = MulAut.conj a v)
    (hC : centralizer ({v} : Set G) ≤ normalizer (V : Set G))
    (g : G) (hv : v ∈ V.map (MulAut.conj g).toMonoidHom) :
    V.map (MulAut.conj g).toMonoidHom = V := by
  obtain ⟨c, hc⟩ := exists_centralizer_conjugator_of_element_fusion hfusion hv
  exact hc.symm.trans (mem_normalizer_iff_map_conj_eq.mp (hC c.property))

/-- Uniqueness through one element extends to its normalizer orbit. -/
public theorem conjugate_eq_of_fusion_of_mem_normalizer_orbit
    (hfusion : ∀ a : G, MulAut.conj a v ∈ V →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v = MulAut.conj a v)
    (hC : centralizer ({v} : Set G) ≤ normalizer (V : Set G))
    (g n : G) (hn : n ∈ normalizer (V : Set G))
    (hx : MulAut.conj n v ∈ V.map (MulAut.conj g).toMonoidHom) :
    V.map (MulAut.conj g).toMonoidHom = V := by
  have hv : v ∈ V.map (MulAut.conj (n⁻¹ * g)).toMonoidHom := by
    obtain ⟨x, hxV, hxn⟩ := hx
    refine mem_map.mpr ⟨x, hxV, ?_⟩
    change MulAut.conj g x = MulAut.conj n v at hxn
    change MulAut.conj (n⁻¹ * g) x = v
    calc
      MulAut.conj (n⁻¹ * g) x = MulAut.conj n⁻¹ (MulAut.conj g x) := by
        simp [MulAut.conj_apply, mul_assoc]
      _ = v := by rw [hxn]; simp [MulAut.conj_apply, mul_assoc]
  have heq := conjugate_eq_of_fusion_of_centralizer_le_normalizer V v hfusion hC _ hv
  have hcomp : (MulAut.conj n).toMonoidHom.comp
      (MulAut.conj (n⁻¹ * g)).toMonoidHom = (MulAut.conj g).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  calc
    V.map (MulAut.conj g).toMonoidHom =
        (V.map (MulAut.conj (n⁻¹ * g)).toMonoidHom).map
          (MulAut.conj n).toMonoidHom := by rw [map_map, hcomp]
    _ = V := by rw [heq]; exact mem_normalizer_iff_map_conj_eq.mp hn

end Subgroup
