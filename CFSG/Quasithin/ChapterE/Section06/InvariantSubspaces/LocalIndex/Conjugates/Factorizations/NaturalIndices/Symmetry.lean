module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices.Coordinates

/-!
# Inverse-conjugation symmetry of the action indices

An automorphism transports centralizers and relative indices. Applying
conjugation by x to the pair (U, U^(x⁻¹)) computes the index inside Uˣ
using a fixed-space calculation on the original U. Thus no configuration
for a new conjugate block, or invariance of L under x, is required.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the symmetry
argument following (*) in C.5.6, printed p.156 (PDF p.167).
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices
open Subgroup
universe u
variable {G : Type u} [Group G]

private theorem map_centralizer (B : Subgroup G) (e : G ≃* G) :
    (centralizer (B : Set G)).map e.toMonoidHom = centralizer (B.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro g hg
    refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hg (e y) (mem_map_of_mem _ hy)

private theorem inverse_conjugate_map (B : Subgroup G) (x : G) :
    (B.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj x).toMonoidHom = B := by
  rw [map_map]
  have he : (MulAut.conj x).toMonoidHom.comp (MulAut.conj x⁻¹).toMonoidHom = MonoidHom.id G := by
    ext g
    simp [MulAut.conj_apply, mul_assoc]
  rw [he, map_id]

/-- Noncentralization is symmetric after replacing the conjugator by its inverse. -/
theorem inverse_not_centralizing (B : Subgroup G) (x : G)
    (hnc : ¬ B.map (MulAut.conj x).toMonoidHom ≤ centralizer (B : Set G)) :
    ¬ B.map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (B : Set G) := by
  intro hc
  have hm := map_mono (f := (MulAut.conj x).toMonoidHom) hc
  rw [inverse_conjugate_map, map_centralizer] at hm
  exact hnc (le_centralizer_iff.mp hm)

/-- Transporting the index for the inverse conjugate gives the actor index
inside the full conjugate Uˣ, without assuming that U is centerless. -/
theorem conjugate_index_eq_inverse (B : Subgroup G) (x : G) :
    (centralizer (B : Set G)).relIndex (B.map (MulAut.conj x).toMonoidHom) =
      (centralizer (B.map (MulAut.conj x⁻¹).toMonoidHom : Set G)).relIndex B := by
  have hh := relIndex_map_map_of_injective (f := (MulAut.conj x).toMonoidHom)
    (centralizer (B.map (MulAut.conj x⁻¹).toMonoidHom : Set G)) B (MulAut.conj x).injective
  rwa [map_centralizer, inverse_conjugate_map] at hh

variable {K : GroupClass.{u}} {A H R L : Subgroup G}

/-- Every allowed conjugate remains inside the same Baumann subgroup. -/
theorem conjugate_le_baumann (h : Configuration K A H R L)
    (hb : BaumannStructure H R L) {x : G} (hx : x ∈ A) :
    (U L).map (MulAut.conj x).toMonoidHom ≤ S R := by
  have hs := mem_normalizer_iff_map_conj_eq.mp (h.normalizes_S hx)
  exact hs ▸ map_mono hb.module_le

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices
end
