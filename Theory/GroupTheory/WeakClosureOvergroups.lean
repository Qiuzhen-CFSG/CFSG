module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Prime-power overgroups of a weakly closed subgroup

If a subgroup is weakly closed in a Sylow subgroup, every prime-power
overgroup normalizes it. Conjugate the overgroup into the chosen Sylow;
weak closure fixes the smaller subgroup, both before and after conjugation
by an element of the overgroup.

This is the overgroup observation used in Janko–Thompson, Math. Z. 113
(1970), §6, p.395. No solvability or simplicity hypothesis is needed.
-/

namespace Subgroup

/-- Every prime-power overgroup normalizes a weakly closed subgroup. -/
public theorem le_normalizer_of_isPGroup_of_weakly_closed
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (W R : Subgroup G)
    (hweak : ∀ g : G, W.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) →
      W.map (MulAut.conj g).toMonoidHom = W)
    (hR : IsPGroup p R) (hWR : W ≤ R) : R ≤ normalizer (W : Set G) := by
  obtain ⟨T, hRT⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  let f := (MulAut.conj g).toMonoidHom
  have hRS : R.map f ≤ (S : Subgroup G) := by
    rw [← hg]
    exact map_mono hRT
  have hWg : W.map f = W := hweak g ((map_mono hWR).trans hRS)
  intro r hr
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply map_injective (f := f) (MulAut.conj g).injective
  change (W.map (MulAut.conj r).toMonoidHom).map f = W.map f
  rw [hWg, map_map]
  have hcomp : f.comp (MulAut.conj r).toMonoidHom =
      (MulAut.conj (g * r)).toMonoidHom := by
    ext x
    simp [f, mul_assoc]
  rw [hcomp]
  apply hweak
  have hconjR : W.map (MulAut.conj r).toMonoidHom ≤ R := by
    rintro x ⟨w, hw, rfl⟩
    exact R.mul_mem (R.mul_mem hr (hWR hw)) (R.inv_mem hr)
  have h := (map_mono (f := f) hconjR).trans hRS
  rwa [map_map, hcomp] at h

end Subgroup
