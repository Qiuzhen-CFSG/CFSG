module

public import Theory.GroupTheory.Commutator.CentralizingComplement
public import Mathlib.GroupTheory.IsPerfect

/-!
# Recovering perfect subgroups across a central kernel

A perfect subgroup whose image lies in the image of L already lies in L:
the derived subgroup of L ker(f) lies in L. Consequently normalizing the
image of a perfect subgroup is equivalent to normalizing the subgroup.
No surjectivity or ambient normality of L is required.

This is the normalization transport used in Aschbacher–Smith, 16.3.11(3),
printed p.1181, when recovering L from its image in K/Z(K).
-/

public section
namespace Subgroup
variable {G D : Type*} [Group G] [Group D]

/-- Containment of perfect subgroups is reflected by a homomorphism with
central kernel, even when the comparison subgroup is not normal. -/
theorem perfect_le_of_map_le_of_central_kernel (f : G →* D)
    (hker : f.ker ≤ center G) (P L : Subgroup G) [Group.IsPerfect P]
    (hPL : P.map f ≤ L.map f) : P ≤ L := by
  have hPS : P ≤ L ⊔ f.ker := by
    rw [← comap_map_eq]
    exact map_le_iff_le_comap.mp hPL
  have hder : ⁅L ⊔ f.ker, L ⊔ f.ker⁆ = ⁅L, L⁆ := by
    calc
      _ = ⁅L ⊔ f.ker, L⁆ := (commutator_eq_of_centralizing_sup
        (sup_comm f.ker L) (hker.trans (center_le_centralizer _))
        (le_sup_left.trans (L ⊔ f.ker).le_normalizer)).symm
      _ = ⁅L, L ⊔ f.ker⁆ := commutator_comm _ _
      _ = ⁅L, L⁆ := (commutator_eq_of_centralizing_sup
        (sup_comm f.ker L) (hker.trans (center_le_centralizer _)) L.le_normalizer).symm
  have hd := commutator_mono hPS hPS
  rw [commutator_eq_self, hder] at hd
  exact hd.trans L.commutator_le_self

/-- The full normalizer of a perfect subgroup is reflected across a central
kernel. This does not identify fixed subgroups under quotient maps. -/
theorem comap_normalizer_map_eq_of_perfect (f : G →* D)
    (hker : f.ker ≤ center G) (L : Subgroup G) [Group.IsPerfect L] :
    (normalizer (L.map f : Set D)).comap f = normalizer (L : Set G) := by
  apply le_antisymm
  · apply le_normalizer_iff.mpr
    intro g hg l hl
    let P := L.map (MulAut.conj g).toMonoidHom
    let : Group.IsPerfect P := Group.IsPerfect.map _
    have hPL : P.map f ≤ L.map f := by
      rintro _ ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      change f (g * y * g⁻¹) ∈ L.map f
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp hg (f y)).mp (mem_map_of_mem f hy)
    exact perfect_le_of_map_le_of_central_kernel f hker P L hPL
      (mem_map_of_mem _ hl)
  · exact map_le_iff_le_comap.mp (le_normalizer_map f)

end Subgroup
