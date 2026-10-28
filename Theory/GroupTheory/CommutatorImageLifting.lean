module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise


/-!
# Lifting a normalized commutator image

Suppose B normalizes A, B lies in a normal subgroup K, and the image of A
under f is its commutator with the image of B. Factoring through the actual
kernel shows A ≤ K whenever A ∩ ker(f) ≤ K. The normalizer hypothesis is
essential: image containment and a bound on A ∩ ker(f) alone do not lift
containment into an arbitrary subgroup K.

This is the elementary lifting step needed for the marked partner in
Aschbacher–Smith 15.3.59, printed p.1150 (combined manuscript, 1 March 2004).
-/

public section

namespace Subgroup
variable {G D : Type*} [Group G] [Group D]

/-- A normalized commutator image lifts into a normal subgroup containing
the acting group and the restricted kernel. -/
theorem le_of_commutator_image_of_normalized (f : G →* D) (A B K : Subgroup G)
    [K.Normal] (hBK : B ≤ K) (hnorm : B ≤ normalizer (A : Set G))
    (himage : A.map f = ⁅A.map f, B.map f⁆)
    (hker : A ⊓ f.ker ≤ K) : A ≤ K := by
  have hCA : ⁅A, B⁆ ≤ A := le_normalizer_iff_commutator_le_left.mp hnorm
  have hCK : ⁅A, B⁆ ≤ K := (commutator_mono le_rfl hBK).trans (commutator_le_right A K)
  have hcover : A ≤ ⁅A, B⁆ ⊔ f.ker := by
    rw [← comap_map_eq]
    apply map_le_iff_le_comap.mp
    rw [map_commutator, ← himage]
  intro a ha
  obtain ⟨c, hc, z, hz, he⟩ := mem_sup_of_normal_right.mp (hcover ha)
  have hzA : z ∈ A := by
    have h := A.mul_mem (A.inv_mem (hCA hc)) ha
    rwa [← he, inv_mul_cancel_left] at h
  rw [← he]
  exact K.mul_mem (hCK hc) (hker ⟨hzA, hz⟩)

end Subgroup
