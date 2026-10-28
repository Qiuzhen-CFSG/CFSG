module

public import Theory.GroupTheory.CComponent.Basic

/-!
# A unique noncentral component is normalized by the section stabilizer

Conjugation preserves C-components. If a conjugate of a component centralizes
a subgroup stabilized by the conjugator, the original component centralizes it
as well, by transport of the commutator. Uniqueness therefore forces the
conjugate component to equal the original one.

This is the elementary normalizer consequence of the uniqueness assertion in
Aschbacher–Smith, 11.1.3 (printed p.765). The uniqueness assertion itself requires
the component and representation theory of that lemma.
-/

namespace Subgroup.IsCComponent

variable {G : Type*} [Group G] {K V : Subgroup G}

/-- The stabilizer of V normalizes its unique noncentralizing C-component. -/
public theorem normalizer_le_of_unique_noncentral (hK : K.IsCComponent)
    (hnoncentral : ¬ K ≤ centralizer (V : Set G))
    (hunique : ∀ J : Subgroup G, J.IsCComponent →
      ¬ J ≤ centralizer (V : Set G) → J = K) :
    normalizer (V : Set G) ≤ normalizer (K : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply hunique _ (hK.map_equiv (MulAut.conj g))
  intro hcentral
  apply hnoncentral
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply (map_eq_bot_iff_of_injective _
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).mp
  have hfix : V.map (MulAut.conj g).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp hg
  rw [map_commutator, hfix]
  exact commutator_eq_bot_iff_le_centralizer.mpr hcentral

/-- If the subgroup is normal, its unique noncentralizing C-component is normal. -/
public theorem normal_of_unique_noncentral (hK : K.IsCComponent) [V.Normal]
    (hnoncentral : ¬ K ≤ centralizer (V : Set G))
    (hunique : ∀ J : Subgroup G, J.IsCComponent →
      ¬ J ≤ centralizer (V : Set G) → J = K) : K.Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  simpa only [V.normalizer_eq_top] using
    hK.normalizer_le_of_unique_noncentral hnoncentral hunique

end Subgroup.IsCComponent
