module
public import Theory.GroupTheory.InnerActorSylowNormalizer
/-! Inner representatives of a two-group action preserving a subgroup lie in
one Sylow subgroup of its normalizer. Every overgroup of this Sylow is invariant
under the original action. This action form also applies to characteristic
quotients, so the ambient group need not itself be centerless.
Source application: Aschbacher--Smith 2.4.25, printed p.543. -/
public section
open Subgroup
namespace Theory.GroupTheory
variable {R D : Type*} [Group R] [Group D]

/-- Inner representatives of a two-group action preserving A lie in one
Sylow subgroup of its normalizer; all overgroups of this Sylow are invariant. -/
theorem exists_inner_action_normalizer_sylow
    (a : R →* MulAut D) (hR : IsPGroup 2 R) (A : Subgroup D)
    (hc : center D = ⊥)
    (hi : Function.Surjective (MulAut.conj : D →* MulAut D))
    (hA : ∀ r : R, A.map (a r).toMonoidHom = A) :
    ∃ P : Sylow 2 (normalizer (A : Set D)),
      ∀ N : Subgroup D,
        (P : Subgroup (normalizer (A : Set D))).map
          (normalizer (A : Set D)).subtype ≤ N →
        ∀ r : R, N.map (a r).toMonoidHom = N := by
  let e : D ≃* MulAut D := MulEquiv.ofBijective (MulAut.conj : D →* MulAut D)
    ⟨MulAut.conj_injective_of_center_eq_bot hc,hi⟩
  let f : R →* D := e.symm.toMonoidHom.comp a
  have he (r : R) : MulAut.conj (f r) = a r := e.apply_symm_apply (a r)
  let B := normalizer (A : Set D)
  have hf (r : R) : f r ∈ B := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [he]
    exact hA r
  let fB : R →* B := f.codRestrict B hf
  obtain ⟨P,hP⟩ := (hR.of_surjective fB.rangeRestrict fB.rangeRestrict_surjective).exists_le_sylow
  refine ⟨P,?_⟩
  intro N hPN r
  rw [←he]
  apply mem_normalizer_iff_map_conj_eq.mp
  apply N.le_normalizer
  exact hPN (mem_map_of_mem B.subtype (hP (show fB r ∈ fB.range from ⟨r,rfl⟩)))
end Theory.GroupTheory
