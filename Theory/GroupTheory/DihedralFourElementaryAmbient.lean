module
public import Theory.GroupTheory.DihedralFourElementaryAction
public import Theory.SpecificGroups.DihedralProduct.AmbientCentralEnlargements
public import Stellmacher.ElementaryAbelianMaxFamilyMap

/-!
# The two elementary choices in an ambient dihedral fourth power

Conjugation by a subgroup of the normalizer transports the coordinate
two-choice theorem without changing the ambient elementary subgroups.
The hypothesis is precisely transitivity on the canonical enlargements.

Source: Aschbacher--Smith, quasithin 10.2.1, printed p.743.
-/

public section
open Subgroup DihedralProductCanonical Stellmacher
namespace DihedralFourChoices
variable {G : Type*} [Group G]

/-- A transitive subgroup of the factor normalizer fixes at most two maximum
elementary subgroups once one invariant member is given. -/
theorem two_normalized_maximum_subgroups
    (S K V : Subgroup G) (e : S ≃* Model)
    (hKS : K ≤ normalizer (S : Set G))
    (htrans : ∀ i j : Fin 4, ∃ k : K,
      normalizerFactorAction S e (inclusion hKS k) i = j)
    (hV : V ∈ elementaryAbelianMaxSubgroups S)
    (hKV : K ≤ normalizer (V : Set G)) :
    ∃ A : Subgroup G, A ≠ V ∧ A ∈ elementaryAbelianMaxSubgroups S ∧
      K ≤ normalizer (A : Set G) ∧
      (∀ W ∈ elementaryAbelianMaxSubgroups S,
        K ≤ normalizer (W : Set G) → W = V ∨ W = A) := by
  let α : Model →* G := S.subtype.comp e.symm.toMonoidHom
  have hα : Function.Injective α := S.subtype_injective.comp e.symm.injective
  let φ : K →* MulAut Model := (MulAut.congr e).toMonoidHom.comp
    (S.normalizerMonoidHom.comp (inclusion hKS))
  have hcomp (k : K) : α.comp (φ k).toMonoidHom =
      (MulAut.conj (k : G)).toMonoidHom.comp α := by
    ext x
    change (e.symm (e (S.normalizerMonoidHom (inclusion hKS k) (e.symm x))) : G) = _
    rw [e.symm_apply_apply]
    rfl
  have hnorm (B : Subgroup Model) :
      (∀ k : K, B.map (φ k).toMonoidHom = B) ↔
        K ≤ normalizer (B.map α : Set G) := by
    constructor
    · intro h k hk
      apply mem_normalizer_iff_map_conj_eq.mpr
      change (B.map α).map (MulAut.conj k).toMonoidHom = B.map α
      rw [map_map,←hcomp ⟨k,hk⟩,←map_map,h ⟨k,hk⟩]
    · intro h k
      apply map_injective (f := α) hα
      rw [map_map,hcomp,←map_map]
      exact mem_normalizer_iff_map_conj_eq.mp (h k.property)
  obtain ⟨B,hB,hVB⟩ := (maxFamily_equiv_iff S e.symm V).mp hV
  have hBfix : ∀ k : K, B.map (φ k).toMonoidHom = B :=
    (hnorm B).mpr (by rw [←hVB]; exact hKV)
  obtain ⟨C,hCB,hC,hCfix,hpair⟩ := two_fixed_choices φ htrans B hB hBfix
  refine ⟨C.map α,?_,?_,(hnorm C).mp hCfix,?_⟩
  · intro he
    apply hCB
    apply map_injective hα
    exact he.trans hVB
  · exact (maxFamily_equiv_iff S e.symm _).mpr ⟨C,hC,rfl⟩
  · intro W hW hKW
    obtain ⟨B',hB',hWB'⟩ := (maxFamily_equiv_iff S e.symm W).mp hW
    have hh := hpair B' hB' ((hnorm B').mpr (by
      rw [←hWB']; exact hKW))
    rcases hh with hh | hh
    · left
      rw [hWB',hh]
      exact hVB.symm
    · right
      rw [hWB',hh]

end DihedralFourChoices
