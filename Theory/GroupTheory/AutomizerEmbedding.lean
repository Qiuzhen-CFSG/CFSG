module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Solvable

/-!
# Induced automizers under faithful ambient embeddings

An injective homomorphism identifies a subgroup with its image. Transporting
its automorphisms along that identification sends every ambient conjugation
to conjugation by the image element. Thus the induced automizer embeds in the
image subgroup's automizer. Solvability and permutation embeddings descend
along this map.

This is the ambient-change step for the degree-three matrix groups in
Aschbacher–Smith, Lemma A.3.21(c), printed pp. 55–56.
-/

public section

namespace Subgroup

variable {G H : Type*} [Group G] [Group H]

/-- A faithful ambient homomorphism induces a faithful map of automizers. -/
theorem exists_injective_automizer_map (Q : Subgroup G)
    (f : G →* H) (hf : Function.Injective f) :
    ∃ j : Q.normalizerMonoidHom.range →* (Q.map f).normalizerMonoidHom.range,
      Function.Injective j := by
  let e := Q.equivMapOfInjective f hf
  let c := MulAut.congr e
  have hc (a : Q.normalizerMonoidHom.range) : c a.val ∈ (Q.map f).normalizerMonoidHom.range := by
    obtain ⟨g, hg⟩ := a.property
    let g' : Subgroup.normalizer (Q.map f : Set H) :=
      ⟨f g, Q.le_normalizer_map f (Subgroup.mem_map_of_mem f g.property)⟩
    refine ⟨g', ?_⟩
    rw [← hg]
    apply MulEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    change _ = e (Q.normalizerMonoidHom g (e.symm (e y)))
    rw [e.symm_apply_apply]
    apply Subtype.ext
    change f g * f y * (f g)⁻¹ = f (g * y * (g : G)⁻¹)
    simp only [map_mul, map_inv]
  let j : Q.normalizerMonoidHom.range →* (Q.map f).normalizerMonoidHom.range :=
    (c.toMonoidHom.comp Q.normalizerMonoidHom.range.subtype).codRestrict _ hc
  refine ⟨j, ?_⟩
  intro a b hab
  apply Subtype.ext
  apply c.injective
  exact congrArg Subtype.val hab

/-- A permutation realization of the larger automizer restricts faithfully. -/
theorem automizer_embeds_perm_of_map (Q : Subgroup G)
    (f : G →* H) (hf : Function.Injective f) {ι : Type*}
    (h : ∃ j : (Q.map f).normalizerMonoidHom.range →* Equiv.Perm ι,
      Function.Injective j) :
    ∃ j : Q.normalizerMonoidHom.range →* Equiv.Perm ι, Function.Injective j := by
  obtain ⟨i, hi⟩ := Q.exists_injective_automizer_map f hf
  obtain ⟨j, hj⟩ := h
  exact ⟨j.comp i, hj.comp hi⟩

/-- Solvability of the larger automizer descends along a faithful embedding. -/
theorem automizer_isSolvable_of_map (Q : Subgroup G)
    (f : G →* H) (hf : Function.Injective f)
    [Group.IsSolvable (Q.map f).normalizerMonoidHom.range] :
    Group.IsSolvable Q.normalizerMonoidHom.range := by
  obtain ⟨j, hj⟩ := Q.exists_injective_automizer_map f hf
  exact Group.isSolvable_of_isSolvable_injective hj

end Subgroup
