module

public import Theory.Representation.PSL3Two.FourGroupGeometry
public import Theory.Representation.PSL3Two.FourGroupGeometry.Normalizers.FourGroupCoverage
public import Theory.Representation.PSL3Two.FourGroupGeometry.Normalizers.PointModel
/-!
# Inner elementary four-group normalizers in Aut(SL₃(2))

Pull an inner elementary four-group back through the injective inner map.
The two translation classes are conjugate under the full automorphism group,
so coverage transports it to the point four-group. There the full normalizer
is the inner S₄ parabolic and the centralizer is the four-group. Transport of
the actual normalizer action gives automizer order six for every such group.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the intrinsic
model geometry in the last paragraph of 15.3.61(2), printed p.1151. Source
quotient transport and the natural-plus-dual fixed spaces are separate results.
-/

public section
open Subgroup Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
namespace BinaryLinearThree.FourGroupGeometry
open Normalizers

/-- Every inner elementary four-group has an inner S₄ normalizer and automizer of order six. -/
theorem inner_fourGroup_normalizer (A : Subgroup (MulAut Group))
    (hAI : A ≤ MulAut.innerSubgroup Group) (hA : IsElementaryAbelian 2 A)
    (hcard : Nat.card A = 4) :
    normalizer (A : Set (MulAut Group)) ≤ MulAut.innerSubgroup Group ∧
      Nonempty (normalizer (A : Set (MulAut Group)) ≃* Equiv.Perm (Fin 4)) ∧
      Nat.card A.normalizerMonoidHom.range = 6 := by
  let := hA
  let B := A.comap MulAut.conj
  have hmap : B.map MulAut.conj = A := map_comap_eq_self hAI
  let : IsElementaryAbelian 2 B := {
    toIsMulCommutative := A.comap_injective_isMulCommutative
      MarkedAutomorphisms.conj_injective
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Subtype.ext
      apply MarkedAutomorphisms.conj_injective
      simpa only [map_pow, map_one, coe_pow, coe_one] using
        elemPow_eq_one_of_isElementaryAbelian (MulAut.conj (x : Group)) x.property) }
  have hB : Nat.card B = 4 :=
    (Nat.card_congr ((B.equivMapOfInjective MulAut.conj
      MarkedAutomorphisms.conj_injective).trans (MulEquiv.subgroupCongr hmap)).toEquiv).trans hcard
  obtain ⟨e,he⟩ := fourGroup_map_point B hB
  let E := MulAut.conj e
  have hE : A.map E.toMonoidHom = innerPoint := by
    rw [← hmap, map_map]
    have hcomp : E.toMonoidHom.comp MulAut.conj = MulAut.conj.comp e.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      exact conjugate_conj e x
    rw [hcomp, ← map_map, he]
  have hNI : normalizer (innerPoint : Set (MulAut Group)) ≤
      MulAut.innerSubgroup Group := by
    rw [point_normalizer]
    exact map_le_range _ _
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    have hm : E a ∈ normalizer (innerPoint : Set (MulAut Group)) := by
      rw [← hE]
      exact A.le_normalizer_map E.toMonoidHom (mem_map_of_mem _ ha)
    have h := (inferInstance : (MulAut.innerSubgroup Group).Normal).conj_mem
      (E a) (hNI hm) e⁻¹
    simpa only [E, MulAut.conj_apply, inv_inv, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, mul_one] using h
  · exact ⟨(normalizerEquivMap E A).trans
      ((MulEquiv.subgroupCongr (congrArg (fun H : Subgroup (MulAut Group) =>
        normalizer (H : Set (MulAut Group))) hE)).trans pointNormalizerEquiv)⟩
  · have h := card_normalizerActionRange_map E A
    rw [hE, point_action_card] at h
    exact h.symm
end BinaryLinearThree.FourGroupGeometry
