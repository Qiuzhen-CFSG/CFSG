module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer.Contracts

/-!
# Extending local agreement to both ambient involution classes

A centralizer equivalence agreeing on K ∩ L with the literal A₈ → A₉ map
sends t to t9. Every involution of K is K-conjugate into K ∩ L by its odd
index. The two internal A₈ classes and their ambient separation therefore
propagate this local agreement to both ambient classes on all of K.
This constructs the exact `SecondCentralizerData` and applies it to the
Thompson order formula with the finite model counts still explicit.

The centralizer equivalence itself remains an input, to be constructed
from the recognized A₅ residual and the actual local intersection.

Source: Aschbacher, “A 2-local characterization of M12”, Proposition 3.3,
printed p.38, the last centralizer-and-fusion comparison.
-/

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index
open Subgroup
variable {G : Type*} [Group G] {z : G} {L : Subgroup G}

private theorem conjugate_order {H : Type*} [Group H] {a b : H}
    (h : IsConj a b) : orderOf a = orderOf b := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact ((MulAut.conj g).orderOf_eq a).symm

/-- The standard inclusion preserves both labels on involutions of L. -/
public theorem InvolutionData.local_class_comparison (d : InvolutionData z L)
    (a : L) (ha : orderOf a = 2) :
    (IsConj z (a : G) ↔ IsConj z9 (eightToNine (d.equiv a))) ∧
    (IsConj (d.t : G) (a : G) ↔ IsConj t9 (eightToNine (d.equiv a))) := by
  let f : L →* Nine := eightToNine.comp d.equiv.toMonoidHom
  rcases d.classes a ha with hc | hc
  · have hg := L.subtype.map_isConj hc
    have h9 : IsConj z9 (eightToNine (d.equiv a)) := by
      simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, d.z_image,
        eightToNine_z8] using f.map_isConj hc
    exact ⟨iff_of_true hg h9,
      iff_of_false (fun ht => d.not_conjugate (hg.trans ht.symm))
        (fun ht => z9_not_conjugate_t9 (h9.trans ht.symm))⟩
  · have hg := L.subtype.map_isConj hc
    have h9 : IsConj t9 (eightToNine (d.equiv a)) := by
      simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        d.equiv.apply_symm_apply, eightToNine_t8] using f.map_isConj hc
    exact ⟨iff_of_false (fun hz => d.not_conjugate (hz.trans hg.symm))
      (fun hz => z9_not_conjugate_t9 (hz.trans h9.symm)), iff_of_true hg h9⟩

namespace CentralizerExtension
variable {d : InvolutionData z L} (c : CentralizerExtension d)

/-- Local agreement sends the actual central involution to the model mark. -/
public theorem involution_image : c.equiv (distinguished (d.t : G)) = distinguished t9 := by
  apply Subtype.ext
  change (c.equiv (distinguished (d.t : G)) : Nine) = t9
  have he := c.agrees_on_local (distinguished (d.t : G)) d.t.property
  change (c.equiv (distinguished (d.t : G)) : Nine) = eightToNine (d.equiv d.t) at he
  simpa only [InvolutionData.t, d.equiv.apply_symm_apply, eightToNine_t8] using he

variable [Finite G]

private theorem fusion_on_involutions (hz : orderOf z = 2) (hCL : Centralizer z ≤ L)
    (a : d.K) (ha : orderOf a = 2) :
    (IsConj z (a : G) ↔ IsConj z9 (c.equiv a : Nine)) ∧
    (IsConj (d.t : G) (a : G) ↔ IsConj t9 (c.equiv a : Nine)) := by
  obtain ⟨k, hk⟩ := d.involution_conjugate_into_M hz hCL a ha
  let b : d.K := k * a * k⁻¹
  have hbL : (b : G) ∈ L := hk
  have hab : IsConj a b := isConj_iff.mpr ⟨k, rfl⟩
  have hb2 : orderOf (⟨(b : G), hbL⟩ : L) = 2 :=
    (Subgroup.orderOf_coe _).symm.trans
      ((Subgroup.orderOf_coe b).trans ((conjugate_order hab).symm.trans ha))
  have hc := d.local_class_comparison ⟨(b : G), hbL⟩ hb2
  rw [← c.agrees_on_local b hbL] at hc
  have hG := d.K.subtype.map_isConj hab
  have h9 := (Centralizer t9).subtype.map_isConj (c.equiv.toMonoidHom.map_isConj hab)
  exact ⟨⟨fun h => ((hc.1.mp (h.trans hG)).trans h9.symm),
      fun h => ((hc.1.mpr (h.trans h9)).trans hG.symm)⟩,
    ⟨fun h => ((hc.2.mp (h.trans hG)).trans h9.symm),
      fun h => ((hc.2.mpr (h.trans h9)).trans hG.symm)⟩⟩

/-- Odd local index promotes agreement on K ∩ L to the full ambient z-class. -/
public theorem z_fusion (hz : orderOf z = 2) (hCL : Centralizer z ≤ L) (a : d.K) :
    IsConj z (a : G) ↔ IsConj z9 (c.equiv a : Nine) := by
  by_cases ha : orderOf a = 2
  · exact (c.fusion_on_involutions hz hCL a ha).1
  · apply iff_of_false
    · intro h
      exact ha ((Subgroup.orderOf_coe a).symm.trans ((conjugate_order h).symm.trans hz))
    · intro h
      exact ha ((c.equiv.orderOf_eq a).symm.trans
        ((Subgroup.orderOf_coe (c.equiv a)).symm.trans
          ((conjugate_order h).symm.trans z9_order)))

/-- The same extension preserves the full ambient t-class. -/
public theorem t_fusion (hz : orderOf z = 2) (hCL : Centralizer z ≤ L) (a : d.K) :
    IsConj (d.t : G) (a : G) ↔ IsConj t9 (c.equiv a : Nine) := by
  by_cases ha : orderOf a = 2
  · exact (c.fusion_on_involutions hz hCL a ha).2
  · apply iff_of_false
    · intro h
      exact ha ((Subgroup.orderOf_coe a).symm.trans
        ((conjugate_order h).symm.trans d.t_ambient_order))
    · intro h
      exact ha ((c.equiv.orderOf_eq a).symm.trans
        ((Subgroup.orderOf_coe (c.equiv a)).symm.trans
          ((conjugate_order h).symm.trans t9_order)))

/-- A locally compatible centralizer extension supplies all fields needed by
the Thompson-order comparison, including both ambient classes. -/
public def secondCentralizerData (hz : orderOf z = 2) (hCL : Centralizer z ≤ L) :
    SecondCentralizerData d where
  equiv := c.equiv
  involution_image := c.involution_image
  z_fusion := c.z_fusion hz hCL
  t_fusion := c.t_fusion hz hCL

end CentralizerExtension

/-- Actual application of the extended centralizer to the ambient order formula.
The finite-model counts remain explicit and have their independent producer. -/
public theorem card_of_centralizer_extension [Finite G] (h : Hypotheses z)
    (local_intersections : ∀ g : G, g * z * g⁻¹ ∈ coreInG z → g * z * g⁻¹ ≠ z →
      IntersectionData z g)
    (d : InvolutionData z L) (hCL : Centralizer z ≤ L)
    (c : CentralizerExtension d) (counts : ModelCounts) : Nat.card G = 181440 :=
  card_of_centralizer_comparison h d (odd_index h local_intersections L hCL) hCL
    (c.secondCentralizerData h.involution hCL) counts

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index
