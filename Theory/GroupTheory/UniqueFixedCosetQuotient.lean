module
public import Theory.GroupTheory.UniqueFixedCosetFusion

/-!
# Unique fixed cosets under quotients and local conjugacy

A surjection whose kernel lies in the point stabilizer preserves the
unique fixed coset of an element. The proof lifts transporters through
the homomorphism. Conjugacy by the stabilizer also preserves uniqueness.

These transport facts retain the literal quotient used in
Aschbacher–Smith F.4.42 when passing from the short-root centralizer to
its quotient by the central short-root line, before applying I.8.5.
-/

public section
open Subgroup
namespace UniqueFixedCoset
variable {G H : Type*} [Group G] [Group H]

theorem unique_of_transporter {M : Subgroup G} {x : G} (hxM : x ∈ M)
    (htrans : ∀ g : G, g * x * g⁻¹ ∈ M → g ∈ M) :
    ∃! q : G ⧸ M, x • q = q := by
  refine ⟨QuotientGroup.mk 1, (fixed_iff M x 1).mpr (by simpa using hxM), ?_⟩
  intro q
  refine Quotient.inductionOn' q ?_
  intro g hg
  apply QuotientGroup.eq.mpr
  simpa using htrans g⁻¹ (by simpa using (fixed_iff M x g).mp hg)

theorem unique_map_of_surjective (f : G →* H) (hf : Function.Surjective f)
    {M : Subgroup G} (hk : f.ker ≤ M) {x : G} (hxM : x ∈ M)
    (hunique : ∃! q : G ⧸ M, x • q = q) :
    ∃! q : H ⧸ M.map f, f x • q = q := by
  apply unique_of_transporter (show f x ∈ M.map f from ⟨x,hxM,rfl⟩)
  intro h hh
  obtain ⟨g,rfl⟩ := hf h
  have hgm : g * x * g⁻¹ ∈ M := by
    obtain ⟨m,hm,he⟩ := hh
    have hk' : m⁻¹ * (g * x * g⁻¹) ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      simpa only [map_mul,map_inv,inv_mul_cancel] using
        congrArg (fun y => (f m)⁻¹ * y) he.symm
    simpa only [mul_inv_cancel_left] using M.mul_mem hm (hk hk')
  exact ⟨g,transporter_mem hxM hunique hgm,rfl⟩

theorem unique_conjugate {M : Subgroup G} {x : G} (hxM : x ∈ M)
    (hunique : ∃! q : G ⧸ M, x • q = q) (m : M) :
    ∃! q : G ⧸ M, (m.val * x * m.val⁻¹) • q = q := by
  apply unique_of_transporter (M.mul_mem (M.mul_mem m.property hxM) (M.inv_mem m.property))
  intro g hg
  have ht : g * m.val * x * (g * m.val)⁻¹ ∈ M := by
    simpa only [mul_inv_rev,mul_assoc] using hg
  have hm := transporter_mem hxM hunique ht
  simpa only [mul_inv_cancel_right] using M.mul_mem hm (M.inv_mem m.property)


/-- Conjugate elements have bijective fixed-coset sets under the original action. -/
theorem unique_of_isConj {M : Subgroup G} {x y : G}
    (hunique : ∃! q : G ⧸ M, x • q = q) (hxy : IsConj x y) :
    ∃! q : G ⧸ M, y • q = q := by
  obtain ⟨q,hq,hu⟩ := hunique
  obtain ⟨g,hg⟩ := isConj_iff.mp hxy
  refine ⟨g • q, ?_, ?_⟩
  · rw [← hg]
    simp only [mul_smul, inv_smul_smul, hq]
  · intro r hr
    have h : x • (g⁻¹ • r) = g⁻¹ • r := by
      calc
        _ = g⁻¹ • ((g * x * g⁻¹) • r) := by simp only [mul_smul, inv_smul_smul]
        _ = g⁻¹ • r := by rw [hg,hr]
    have he := congrArg (fun s : G ⧸ M => g • s) (hu _ h)
    simpa only [smul_inv_smul] using he

end UniqueFixedCoset
