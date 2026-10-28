module
public import Mathlib.GroupTheory.Sylow

/-!
# Conjugate overgroups of a fixed Sylow subgroup

If H contains a Sylow subgroup S and its full ambient normalizer, then
an ambient conjugate of S lying in H has its conjugator in H. Sylow
conjugacy inside H proves this by correcting the given conjugator with
an element of H. Consequently any conjugate of H containing S equals H.

In particular, a self-normalizing Sylow selects a unique overgroup in
each ambient conjugacy class. This aligns independently chosen native
local placements without changing the marked Sylow or the subgroups.
The original J4 actor application is in Chapter12 Section05,
NaturalSource/Local/Normalizers/JankoLocalAlignment.
-/

public section
open Subgroup
open scoped Pointwise
namespace Sylow
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- An ambient conjugator carrying the marked Sylow into its overgroup
belongs to that overgroup when it contains the full Sylow normalizer. -/
theorem mem_overgroup_of_conjugate_le (S : Sylow p G) (H : Subgroup G)
    (hSH : (S : Subgroup G) ≤ H) (hNS : normalizer (S : Set G) ≤ H)
    (g : G) (hg : ((g • S : Sylow p G) : Subgroup G) ≤ H) : g ∈ H := by
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq H ((g • S).subtype hg) (S.subtype hSH)
  simp_rw [smul_subtype, Subgroup.smul_def, smul_smul] at ha
  have hn : (a : G) * g ∈ normalizer (S : Set G) :=
    smul_eq_iff_mem_normalizer.mp (subtype_injective ha)
  have hh := H.mul_mem (H.inv_mem a.property) (hNS hn)
  simpa only [inv_mul_cancel_left] using hh

/-- Two conjugates containing the same Sylow coincide if its ambient
normalizer is contained in the first overgroup. -/
theorem conjugate_overgroup_eq (S : Sylow p G) (H : Subgroup G)
    (hSH : (S : Subgroup G) ≤ H) (hNS : normalizer (S : Set G) ≤ H)
    (g : G) (hg : (S : Subgroup G) ≤ H.map (MulAut.conj g).toMonoidHom) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  have hback : (((g⁻¹ • S : Sylow p G)) : Subgroup G) ≤ H := by
    change (S : Subgroup G).map (MulAut.conj g⁻¹).toMonoidHom ≤ H
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hg
    have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    simpa only [map_map, he, map_id] using hh
  have hginv := S.mem_overgroup_of_conjugate_le H hSH hNS g⁻¹ hback
  exact mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer (inv_mem_iff.mp hginv))

end Sylow
