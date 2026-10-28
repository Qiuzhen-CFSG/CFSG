module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Orthogonal

/-!
# Complementary singular planes in the terminal natural action

For two distinct singular four-groups E and F with a common nonidentity
vector, an element of the actual residual Y_E sends F to a complement.
The proof checks the six graph planes and their cubic rotations, then lifts
both spanning and disjointness through the compatible natural coordinates.
The resulting conjugator belongs to Y_E, even when Y_E is external to G₀.

This is the geometric input to the repaired local character-kernel argument.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), the orthogonal
four-space in 15.3.2 and 15.3.66, printed pp.1121 and 1152–1154.
-/

public section

open Subgroup OrthogonalFourBinary OrthogonalFourBinary.TerminalLines
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam
open GoldschmidtCore.LocalRelations GoldschmidtCore.LocalRelations.OrthogonalProducts

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear

set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem finite_split : ∀ i j : LineCode, i ≠ j →
    (∃ w : Space, w ≠ 0 ∧ w.2 = planePermutation i w.1 ∧ w.2 = planePermutation j w.1) →
    ∃ k : RotationCode,
      (∀ v : Space, (rotation k v).2 = planePermutation i (rotation k v).1 ↔
        v.2 = planePermutation i v.1) ∧
      (∀ w : Space, ∃ u v : Space,
        u.2 = planePermutation j u.1 ∧ v.2 = planePermutation j v.1 ∧
        w = u + rotation k v) ∧
      (∀ u v : Space, u.2 = planePermutation j u.1 →
        v.2 = planePermutation j v.1 → u = rotation k v → u = 0) := by
  decide +kernel

private theorem coordinate_split (E F : Subgroup (Multiplicative Space))
    (hEcard : Nat.card E = 4) (hFcard : Nat.card F = 4)
    (hE : ∀ w ∈ E, form w.toAdd = 0) (hF : ∀ w ∈ F, form w.toAdd = 0)
    (hne : E ≠ F) (hcommon : ∃ w, w ≠ 1 ∧ w ∈ E ∧ w ∈ F) :
    ∃ a ∈ lineResidual E,
      (∀ w : Multiplicative Space, ∃ u ∈ F, ∃ v ∈ F, w = u * vectorAction a v) ∧
      (∀ u ∈ F, ∀ v ∈ F, u = vectorAction a v → u = 1) := by
  obtain ⟨i,rfl⟩ := singular_four_eq_graph E hEcard hE
  obtain ⟨j,rfl⟩ := singular_four_eq_graph F hFcard hF
  obtain ⟨w,hw,hwi,hwj⟩ := hcommon
  obtain ⟨k,hk,hspan,hdisj⟩ := finite_split i j
    (fun h => hne (h ▸ rfl)) ⟨w.toAdd,hw,hwi,hwj⟩
  refine ⟨rotationHom k, ?_, ?_, ?_⟩
  · rw [lineResidual_eq_rotations_inter]
    exact ⟨⟨k,rfl⟩,hk⟩
  · intro w
    obtain ⟨u,v,hu,hv,he⟩ := hspan w.toAdd
    exact ⟨Multiplicative.ofAdd u,hu,Multiplicative.ofAdd v,hv,he⟩
  · intro u hu v hv he
    exact hdisj u.toAdd v.toAdd hu hv he

variable {G : Type*} [Group G] [Finite G]

/-- A residual element carries the second singular plane to a literal ambient complement. -/
theorem exists_lineY_complementary_conjugate (V M Y E F : Subgroup G)
    (d : NaturalAction V M) (hYM : Y ≤ M) (hEV : E ≤ V) (hFV : F ≤ V)
    (hEcard : Nat.card E = 4) (hFcard : Nat.card F = 4)
    (hE : ∀ e : E, d.singular ⟨e,hEV e.property⟩)
    (hF : ∀ f : F, d.singular ⟨f,hFV f.property⟩)
    (hne : E ≠ F) (hcommon : ∃ z, z ≠ 1 ∧ z ∈ E ∧ z ∈ F)
    (himage : actionImage d Y = pResidual 2 TerminalLines.IsometryGroup) :
    ∃ b ∈ lineY Y E,
      V = F ⊔ F.map (MulAut.conj b).toMonoidHom ∧
      Disjoint F (F.map (MulAut.conj b).toMonoidHom) := by
  obtain ⟨z,hz,hzE,hzF⟩ := hcommon
  obtain ⟨a,ha,hspan,hdisj⟩ := coordinate_split (coordinateLine d E) (coordinateLine d F)
    ((coordinateLine_card d E hEV).trans hEcard)
    ((coordinateLine_card d F hFV).trans hFcard)
    (coordinateLine_singular d E hEV hE) (coordinateLine_singular d F hFV hF)
    (fun he => hne (coordinateLine_injective d E F hEV hFV he))
    (coordinateLine_common_vector d E F hEV z hzE hzF hz)
  rw [← actionImage_lineY d Y E hYM hEV himage] at ha
  obtain ⟨b,hb,rfl⟩ := ha
  refine ⟨b,hb,le_antisymm ?_ ?_,?_⟩
  · intro v hv
    obtain ⟨u,hu,w,hw,he⟩ := hspan (d.coordinates ⟨v,hv⟩)
    have he' := congrArg (fun x => (d.coordinates.symm x : G)) he
    rw [map_mul, Subgroup.coe_mul, d.coordinates.symm_apply_apply] at he'
    have ha' := d.intertwines b (d.coordinates.symm w)
    rw [d.coordinates.apply_symm_apply] at ha'
    change (d.coordinates.symm (vectorAction (d.action b) w) : G) = _ at ha'
    rw [ha'] at he'
    change v = _ at he'
    rw [he']
    exact (F ⊔ F.map (MulAut.conj (b : G)).toMonoidHom).mul_mem
      (mem_sup_left ((mem_coordinateLine d F u).mp hu))
      (mem_sup_right (mem_map.mpr ⟨d.coordinates.symm w,
        (mem_coordinateLine d F w).mp hw,rfl⟩))
  · apply sup_le hFV
    exact (map_mono hFV).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (d.normalizes b.property))
  · apply disjoint_iff.mpr
    apply le_antisymm ?_ bot_le
    rintro v ⟨hv,w,hw,rfl⟩
    have hc : d.coordinates ⟨MulAut.conj (b : G) w,hFV hv⟩ =
        vectorAction (d.action b) (d.coordinates ⟨w,hFV hw⟩) := by
      apply d.coordinates.symm.injective
      apply Subtype.ext
      rw [d.coordinates.symm_apply_apply]
      exact (d.intertwines b ⟨w,hFV hw⟩).symm
    have hz := hdisj (d.coordinates ⟨MulAut.conj (b : G) w,hFV hv⟩)
      ((mem_coordinateLine d F _).mpr (by simpa using hv))
      (d.coordinates ⟨w,hFV hw⟩)
      ((mem_coordinateLine d F _).mpr (by simpa using hw)) hc
    have hz' := d.coordinates.injective (hz.trans (map_one d.coordinates).symm)
    exact congrArg Subtype.val hz'

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
