module
public import Theory.SpecificGroups.AlternatingSevenSylowNormalizer
public import Theory.Alternating.Aut
public import Theory.GroupAction.QuotientConjugation
/-!
# Sylow normalizers above a normal A₇ subgroup

Conjugation on the specified normal A₇ subgroup gives an actual permutation
homomorphism with its centralizer as kernel. Its image contains A₇ and is
therefore A₇ or S₇. Self-normalization of their Sylow two-subgroups gives
N_H(T)≤T C_H(L), retaining the original subgroup and its action.
Source: Aschbacher–Smith C.5.13, printed pp.162–163.
-/
public section
open Subgroup
namespace AlternatingSevenNormal
variable {H : Type*} [Group H] [Finite H]
private noncomputable def permAut : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
  MulEquiv.ofBijective _ (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by decide) (by decide))
omit [Finite H] in
theorem exists_permutation_action (L : Subgroup H) [L.Normal]
    (e : L ≃* alternatingGroup (Fin 7)) :
    ∃ f : H →* Equiv.Perm (Fin 7), f.ker = centralizer (L : Set H) ∧
      L.map f = alternatingGroup (Fin 7) := by
  let f : H →* Equiv.Perm (Fin 7) := permAut.symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : H →* MulAut L))
  have hf (l : L) : f l = (e l : Equiv.Perm (Fin 7)) := by
    apply permAut.injective
    change permAut (permAut.symm (MulAut.congr e (MulAut.conjNormal (l : H)))) = _
    rw [permAut.apply_symm_apply]
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    change (e (MulAut.conjNormal (l : H) (e.symm z)) : Equiv.Perm (Fin 7)) =
      (e l : Equiv.Perm (Fin 7)) * z * (e l : Equiv.Perm (Fin 7))⁻¹
    change (e (l * e.symm z * l⁻¹) : Equiv.Perm (Fin 7)) = _
    simp only [map_mul,map_inv,e.apply_symm_apply,Subgroup.coe_mul,Subgroup.coe_inv]
  refine ⟨f,?_,?_⟩
  · ext g
    change permAut.symm (MulAut.congr e (MulAut.conjNormal g)) = 1 ↔ _
    rw [← map_one permAut.symm,permAut.symm.injective.eq_iff,
      ← map_one (MulAut.congr e),(MulAut.congr e).injective.eq_iff]
    change g ∈ (MulAut.conjNormal : H →* MulAut L).ker ↔ _
    rw [MulAut.conjNormal_ker_eq_centralizer]
  · apply le_antisymm
    · rintro _ ⟨l,hl,rfl⟩
      rw [hf ⟨l,hl⟩]
      exact (e ⟨l,hl⟩).property
    · intro z hz
      refine ⟨e.symm ⟨z,hz⟩,(e.symm ⟨z,hz⟩).property,?_⟩
      rw [hf,e.apply_symm_apply]

theorem sylow_normalizer_le (L : Subgroup H) [L.Normal]
    (e : L ≃* alternatingGroup (Fin 7)) (P : Sylow 2 H) :
    normalizer (P : Set H) ≤ (P : Subgroup H) ⊔ centralizer (L : Set H) := by
  obtain ⟨f,hker,hL⟩ := exists_permutation_action L e
  let Q := P.mapSurjective f.rangeRestrict_surjective
  have hA : alternatingGroup (Fin 7) ≤ f.range := hL ▸ L.map_le_range f
  have hn := AlternatingSevenSylow.overgroup_sylow_normalizer f.range hA Q
  have hm : (normalizer (P : Set H)).map f.rangeRestrict ≤ (P : Subgroup H).map f.rangeRestrict := by
    rw [← show normalizer (Q : Set f.range) = (P : Subgroup H).map f.rangeRestrict from hn]
    exact (P : Subgroup H).le_normalizer_map f.rangeRestrict
  have hh := map_le_iff_le_comap.mp hm
  rwa [comap_map_eq,MonoidHom.ker_rangeRestrict,hker] at hh
end AlternatingSevenNormal
