module

public import Theory.GroupAction.TypedCosetGeometry
public import Mathlib.GroupTheory.Sylow

/-!
# Fixed chambers in a parabolic coset action

If all members of a subgroup family contain one ambient Sylow p-subgroup,
every p-subgroup fixes a common translate of their standard cosets. Conversely,
a subgroup fixing a typed left coset conjugates into that vertex subgroup.
The conjugator in the latter assertion is the inverse coset representative.

These are the group-action steps in the finite-building proof of Borel--Tits,
GLS3 Theorem 3.1.3 (`refs/KGroup/GLS3/chapter3.tex`). No normalizer coverage or
building geometry is assumed here.
-/

public section
namespace Subgroup.CosetGeometry

open scoped Pointwise

variable {G I : Type*} [Group G] [Finite G] (F : I → Subgroup G)

/-- Sylow conjugacy supplies an entire fixed chamber, with one representative
for all vertex types. The subgroup need not be nonidentity. -/
theorem exists_fixed_chamber {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (hS : ∀ i, (S : Subgroup G) ≤ F i)
    (R : Subgroup G) (hR : IsPGroup p R) :
    ∃ g : G, ∀ i, ∀ r ∈ R, r • (g • base F i) = g • base F i := by
  obtain ⟨T, hRT⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  have hconj : ∀ r ∈ R, g * r * g⁻¹ ∈ (S : Subgroup G) := by
    intro r hr
    have hm : (MulAut.conj g) r ∈ (MulAut.conj g) • (T : Subgroup G) :=
      Subgroup.mem_map.mpr ⟨r, hRT hr, rfl⟩
    change g * r * g⁻¹ ∈ (g • T : Sylow p G) at hm
    rwa [hg] at hm
  refine ⟨g⁻¹, fun i r hr => ?_⟩
  have hmem : g * r * g⁻¹ ∈ MulAction.stabilizer G (base F i) := by
    rw [stabilizer_base]
    exact hS i (hconj r hr)
  calc
    r • (g⁻¹ • base F i) = g⁻¹ • ((g * r * g⁻¹) • base F i) := by
      simp [mul_smul]
    _ = g⁻¹ • base F i :=
      congrArg (g⁻¹ • ·) (MulAction.mem_stabilizer_iff.mp hmem)

omit [Finite G] in
/-- A fixed left coset gives conjugate containment with the inverse of its
representative. This applies to the whole normalizer once it fixes a vertex. -/
theorem conjugate_le_of_fixed_vertex (H : Subgroup G)
    (v : Vertex F) (hv : ∀ h ∈ H, h • v = v) :
    ∃ g : G, H.map (MulAut.conj g).toMonoidHom ≤ F v.type := by
  obtain ⟨g, hg⟩ := exists_smul_base F v
  refine ⟨g⁻¹, ?_⟩
  rintro x ⟨h, hh, rfl⟩
  have he : (g⁻¹ * h * g) • base F v.type = base F v.type := by
    calc
      _ = g⁻¹ • (h • (g • base F v.type)) := by simp only [mul_smul]
      _ = g⁻¹ • (g • base F v.type) := by
        congr 1
        rw [hg]
        exact hv h hh
      _ = _ := inv_smul_smul g _
  have hm : g⁻¹ * h * g ∈ MulAction.stabilizer G (base F v.type) := he
  rw [stabilizer_base] at hm
  simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    MulAut.conj_apply, inv_inv] using hm

end Subgroup.CosetGeometry
