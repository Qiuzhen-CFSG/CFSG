module

public import Theory.GroupTheory.ComponentLocalOrbitCore
public import Theory.GroupTheory.SylowCommutingJoin

/-!
# Sylow subgroups of actual local-factor orbits

Distinct conjugates of a local factor in a component commute when the
component stabilizer normalizes the factor. Index the distinct actual
subgroups, transport the local Sylow by the same conjugators, and apply
the commuting-product Sylow theorem. This proves containment in the
specified ambient p-subgroup without choosing an abstract product equivalence.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.11, printed p.213.
-/

public section
open Subgroup

namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
/-- Conjugating the specified local Sylow subgroup inside T constructs a
Sylow subgroup of the entire local-factor orbit inside T. -/
theorem IsComponent.exists_sylow_local_orbit_le {p : ℕ} [Fact p.Prime]
    {J E D T : Subgroup G} (hJ : IsComponent G J) (hEJ : E ≤ J)
    (hinv : D ⊓ normalizer (J : Set G) ≤ normalizer (E : Set G))
    (hDT : D ≤ T) (S : Sylow p E) (hST : (S : Subgroup E).map E.subtype ≤ T) :
    ∃ R : Sylow p (componentOrbit E D),
      (R : Subgroup (componentOrbit E D)).map (componentOrbit E D).subtype ≤ T := by
  classical
  let I := {F : Subgroup G // ∃ d : D, E.map (MulAut.conj (d : G)).toMonoidHom = F}
  let d : I → D := fun i => Classical.choose i.property
  have hd (i : I) : E.map (MulAut.conj (d i : G)).toMonoidHom = i.val :=
    Classical.choose_spec i.property
  let C := fun i : I => i.val
  have hc : Pairwise fun i j => ∀ x y : G, x ∈ C i → y ∈ C j → Commute x y := by
    intro i j hij x y hx hy
    rcases hJ.local_conjugates_eq_or_commute hEJ hinv (d j) (d i) with he | he
    · exact (hij (Subtype.ext ((hd i).symm.trans (he.trans (hd j))))).elim
    · have he' : ⁅C i, C j⁆ = ⊥ := by simpa only [hd] using he
      exact (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he' hx) y hy).symm
  let e (i : I) : E ≃* C i :=
    ((MulAut.conj (d i : G)).subgroupMap E).trans (MulEquiv.subgroupCongr (hd i))
  let S' (i : I) : Sylow p (C i) := S.mapSurjective (f := (e i).toMonoidHom) (e i).surjective
  have hS' (i : I) : (S' i : Subgroup (C i)).map (C i).subtype ≤ T := by
    rintro _ ⟨x, ⟨y, hy, rfl⟩, rfl⟩
    change (d i : G) * (y : G) * (d i : G)⁻¹ ∈ T
    exact T.mul_mem (T.mul_mem (hDT (d i).property) (hST (mem_map_of_mem _ hy)))
      (T.inv_mem (hDT (d i).property))
  have hsup : (⨆ i, C i) = componentOrbit E D := by
    apply le_antisymm
    · apply iSup_le
      intro i
      rw [show C i = E.map (MulAut.conj (d i : G)).toMonoidHom from (hd i).symm]
      exact le_iSup (fun a : D => E.map (MulAut.conj (a : G)).toMonoidHom) (d i)
    · apply iSup_le
      intro a
      exact le_iSup C ⟨_, a, rfl⟩
  obtain ⟨R, hR⟩ := exists_sylow_iSup_le_of_commuting C hc S' T hS'
  let f := MulEquiv.subgroupCongr hsup
  refine ⟨R.mapSurjective (f := f.toMonoidHom) f.surjective, ?_⟩
  change ((R : Subgroup (⨆ i, C i : Subgroup G)).map f.toMonoidHom).map
    (componentOrbit E D).subtype ≤ T
  rw [map_map]
  exact hR
end Theory.GroupTheory

