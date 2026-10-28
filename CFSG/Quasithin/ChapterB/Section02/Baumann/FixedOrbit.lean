module
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Stellmacher.ElementaryAbelianMaxJFixedIntersection
/-!
# Baumann fixed points from Thompson orbit representatives

An elementary subgroup of S fixed by J(S) lies in Ω₁(Z(J(S))). Baum(S)
therefore fixes the elementary Thompson fixed subgroup. If every vector
of W has a K-conjugate in that subgroup, each vector of a conjugate of W
is fixed by an M-conjugate of Baum(S), provided K and the conjugator lie
in M. This retains literal ambient conjugation and allows a central kernel.

Source application: Aschbacher–Smith10.2.9, printed pp.750–751.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]

theorem baumann_centralizes_elementary_thompson_fixed
    (S W : Subgroup G) [IsElementaryAbelian 2 W] (hWS : W ≤ S) :
    baumann S ≤ centralizer (W ⊓ centralizer (elementaryAbelianMaxJ S : Set G) : Set G) := by
  have hF : W ⊓ centralizer (elementaryAbelianMaxJ S : Set G) ≤ thompsonAlpha S := by
    rw [← omegaCenter_maxJ_inf_elementary_eq_fixed S W hWS]
    exact inf_le_left
  exact inf_le_right.trans (centralizer_le hF)

theorem baumann_conjugate_centralizes_of_thompson_fixed_representative
    (S W : Subgroup G) [IsElementaryAbelian 2 W] (hWS : W ≤ S)
    (v m : G)
    (hm : (MulAut.conj m) v ∈ W ⊓ centralizer (elementaryAbelianMaxJ S : Set G)) :
    (baumann S).map (MulAut.conj m⁻¹).toMonoidHom ≤ centralizer ({v} : Set G) := by
  have hB : baumann S ≤ centralizer ({(MulAut.conj m) v} : Set G) :=
    (baumann_centralizes_elementary_thompson_fixed S W hWS).trans
      (centralizer_le (Set.singleton_subset_iff.mpr hm))
  have hmap := (map_mono (f := (MulAut.conj m⁻¹).toMonoidHom) hB).trans
    (map_centralizer_le_centralizer_image _ _)
  rw [Set.image_singleton] at hmap
  simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using hmap

theorem exists_baumann_conjugate_centralizing_of_elementary_orbits
    (S W M K : Subgroup G) [IsElementaryAbelian 2 W]
    (hWS : W ≤ S) (hKM : K ≤ M)
    (horbit : ∀ w ∈ W, ∃ k ∈ K,
      (MulAut.conj k) w ∈ W ⊓ centralizer (elementaryAbelianMaxJ S : Set G))
    {t v : G} (ht : t ∈ M) (hv : v ∈ W.map (MulAut.conj t).toMonoidHom) :
    ∃ m ∈ M, (baumann S).map (MulAut.conj m).toMonoidHom ≤ centralizer ({v} : Set G) := by
  obtain ⟨w,hw,rfl⟩ := hv
  obtain ⟨k,hk,hfix⟩ := horbit w hw
  have hB := baumann_conjugate_centralizes_of_thompson_fixed_representative S W hWS w k hfix
  refine ⟨t*k⁻¹,M.mul_mem ht (M.inv_mem (hKM hk)),?_⟩
  have hmap := (map_mono (f := (MulAut.conj t).toMonoidHom) hB).trans
    (map_centralizer_le_centralizer_image _ _)
  rw [Set.image_singleton] at hmap
  have he : ((baumann S).map (MulAut.conj k⁻¹).toMonoidHom).map
      (MulAut.conj t).toMonoidHom = (baumann S).map (MulAut.conj (t*k⁻¹)).toMonoidHom :=
    (baumann S).conjBy_conjBy k⁻¹ t
  exact he ▸ hmap

end CFSG.Quasithin.ChapterB
