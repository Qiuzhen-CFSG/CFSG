module

public import Mathlib.GroupTheory.Sylow

/-!
# Choosing a conjugate with a Sylow normalizer intersection

For a Sylow subgroup `S` and any subgroup `H` of a finite group, some
conjugate of `H` intersects `S` in a Sylow subgroup of that conjugate.
Choose a Sylow subgroup of `H`, extend it to an ambient Sylow subgroup,
and conjugate the latter to `S`. We express the conclusion by its index.

The relative version conjugates inside an overgroup `M` of `S`, and
applies to `N_M(E)`. It does not assume that `E` is normal in `M`.

Source: the Sylow conjugacy adjustment before Lemma 15.3.66 in
Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1152.
-/

namespace Sylow

open Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A conjugate of `H` has Sylow intersection with the specified Sylow subgroup. -/
public theorem exists_conjugate_not_dvd_relIndex (S : Sylow p G) (H : Subgroup G) :
    ∃ g : G, ¬ p ∣ (S : Subgroup G).relIndex (H.map (MulAut.conj g).toMonoidHom) := by
  let P : Sylow p H := Classical.choice inferInstance
  obtain ⟨U, hU⟩ := P.exists_comap_subtype_eq
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G U S
  have hi : ¬ p ∣ (U : Subgroup G).relIndex H := by
    change ¬ p ∣ ((U : Subgroup G).comap H.subtype).index
    rw [hU]
    exact P.not_dvd_index
  refine ⟨g, ?_⟩
  have he : (U : Subgroup G).map (MulAut.conj g).toMonoidHom = (S : Subgroup G) :=
    congrArg Sylow.toSubgroup hg
  rw [← he, relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  exact hi

/-- Conjugation inside `M` makes `S ∩ N_M(Eᵐ)` Sylow in `N_M(Eᵐ)`. -/
public theorem exists_conjugate_normalizer_not_dvd_relIndex
    (S : Sylow p G) (M E : Subgroup G) (hSM : (S : Subgroup G) ≤ M) :
    ∃ m ∈ M, ¬ p ∣ (S : Subgroup G).relIndex
      (M ⊓ normalizer (E.map (MulAut.conj m).toMonoidHom : Set G)) := by
  let K := (normalizer (E : Set G)).subgroupOf M
  obtain ⟨m, hm⟩ := (S.subtype hSM).exists_conjugate_not_dvd_relIndex K
  have hM : M.map (MulAut.conj (m : G)).toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer m.property)
  have hmap : (K.map (MulAut.conj m).toMonoidHom).map M.subtype =
      M ⊓ normalizer (E.map (MulAut.conj (m : G)).toMonoidHom : Set G) := by
    have he : M.subtype.comp (MulAut.conj m).toMonoidHom =
        (MulAut.conj (m : G)).toMonoidHom.comp M.subtype := by ext x; rfl
    rw [map_map, he, ← map_map]
    change ((normalizer (E : Set G)).subgroupOf M |>.map M.subtype).map _ = _
    rw [subgroupOf_map_subtype, map_inf _ _ _ (MulAut.conj (m : G)).injective,
      map_equiv_normalizer_eq, hM, inf_comm]
  refine ⟨m, m.property, ?_⟩
  rw [← hmap, ← map_subgroupOf_eq_of_le hSM,
    relIndex_map_map_of_injective _ _ M.subtype_injective]
  exact hm

end Sylow
