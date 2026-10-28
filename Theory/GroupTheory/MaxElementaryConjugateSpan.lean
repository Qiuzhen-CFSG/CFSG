module
public import Stellmacher.ElementaryAbelianMaxDefs
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# Maximum elementary subgroups inside a normalized subgroup

Suppose every maximum elementary subgroup of S centralizes Z. If N lies in
S and is normalized by H, a maximum elementary subgroup A of S lying in N
centralizes every H-conjugate of Z. Conjugating A by H preserves its order
and keeps it inside S, so it remains in the same maximum family. Consequently
A centralizes the full conjugate span.

Source application: Aschbacher–Smith, D.1.3(2), printed p.173. This supplies
the escape argument for the quadratic replacement on the actual span.
-/

public section
namespace Stellmacher
open Subgroup
variable {G : Type*} [Group G]

private theorem maxFamily_conj_of_le (S N A : Subgroup G)
    (hNS : N ≤ S) (hA : A ∈ elementaryAbelianMaxSubgroups S) (hAN : A ≤ N)
    (g : G) (hg : g ∈ normalizer (N : Set G)) :
    A.map (MulAut.conj g).toMonoidHom ∈ elementaryAbelianMaxSubgroups S := by
  have hm : A.map (MulAut.conj g).toMonoidHom ≤ N :=
    (map_mono hAN).trans_eq (mem_normalizer_iff_map_conj_eq.mp hg)
  refine ⟨hm.trans hNS, hA.2.1.map _, ?_⟩
  intro B hBS hBe
  rw [card_map_of_injective (MulAut.conj g).injective]
  exact hA.2.2 B hBS hBe

theorem maxElementary_inside_centralizes_conjugateSpan (S N Z H A : Subgroup G)
    (hNS : N ≤ S) (hHN : H ≤ normalizer (N : Set G))
    (hall : ∀ D ∈ elementaryAbelianMaxSubgroups S, D ≤ centralizer (Z : Set G))
    (hA : A ∈ elementaryAbelianMaxSubgroups S) (hAN : A ≤ N) :
    A ≤ centralizer (conjugateSpanBy Z H : Set G) := by
  apply le_centralizer_iff.mpr
  apply (closure_le _).mpr
  rintro x ⟨g,hg,z,hz,rfl⟩ a ha
  have hc := hall (A.map (MulAut.conj g⁻¹).toMonoidHom)
    (maxFamily_conj_of_le S N A hNS hA hAN g⁻¹ (hHN (H.inv_mem hg)))
    (mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom ha) z hz
  change z * (g⁻¹ * a * g⁻¹⁻¹) = (g⁻¹ * a * g⁻¹⁻¹) * z at hc
  have he := congrArg (fun t : G => g * t * g⁻¹) hc
  simpa only [inv_inv, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left,
    mul_inv_cancel_right, inv_mul_cancel_right, mul_inv_cancel, mul_one] using he.symm

end Stellmacher
