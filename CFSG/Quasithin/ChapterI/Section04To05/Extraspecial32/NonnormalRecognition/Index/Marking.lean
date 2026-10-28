module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Reduction
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Marking.Model
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Marking.CoreCensus

/-!
# Marking and separating the two involution classes in the A₈ overgroup

Containment of the full centralizer identifies C_L(z) with C_G(z), of order
192. The internal double-transposition centralizer has order 96, so an inner
relabeling of the supplied eight-point action sends z to the specified z8.
If the two internal classes fused in G, every involution of the core would
belong to CoreFusion z. The eighteen explicitly constructed core involutions
contradict its cardinality thirteen. This constructs the literal marking
record without assuming its marking, nonfusion, or class-coverage clauses.

The final source application combines this record with the proved odd index
to cover all ambient involutions and control their fusion in the actual L.
Nonnormality and the local intersection family are unnecessary for the
marking itself; the intersection family supplies the odd index in that
application. No ambient simplicity or index alternative is assumed here.

Source: Aschbacher, “A 2-local characterization of M12”, Proposition 3.3,
printed p.38, https://authors.library.caltech.edu/records/m3wrn-5w840/files/ASCijm03.pdf.
-/

open Subgroup
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition
namespace Index.Marking

private def centralizerEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    Centralizer x ≃ Centralizer (e x) :=
  e.toEquiv.subtypeEquiv fun y => by
    simp only [Centralizer, mem_centralizer_singleton_iff]
    change (y * x = x * y) ↔ (e y * e x = e x * e y)
    rw [← map_mul, ← map_mul, e.injective.eq_iff]

private theorem centralizer_card_of_isConj {G : Type*} [Group G] {x y : G}
    (h : IsConj x y) : Nat.card (Centralizer x) = Nat.card (Centralizer y) := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact Nat.card_congr (centralizerEquiv (MulAut.conj g) x)

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Relabel the supplied action so that the distinguished involution is z8. -/
public theorem exists_equiv_z8 (h : Hypotheses z) (L : Subgroup G) (e : L ≃* Eight)
    (hCL : Centralizer z ≤ L) :
    ∃ hz : z ∈ L, ∃ f : L ≃* Eight, f ⟨z, hz⟩ = z8 := by
  have hz : z ∈ L := hCL (distinguished z).property
  let zL : L := ⟨z, hz⟩
  have hz2 : orderOf (e zL) = 2 :=
    (e.orderOf_eq zL).trans ((Subgroup.orderOf_coe zL).symm.trans h.involution)
  have hcard : Nat.card (Centralizer (e zL)) = 192 := by
    rw [← Nat.card_congr (centralizerEquiv e zL),
      Nat.card_congr (Theory.GroupTheory.TwoInvolutionClassOrder.centralizerEquiv L zL hCL)]
    exact h.centralizer_card
  rcases involution_classes (e zL) hz2 with hzclass | htclass
  · obtain ⟨g, hg⟩ := isConj_iff.mp hzclass.symm
    exact ⟨hz, e.trans (MulAut.conj g), hg⟩
  · have hc := centralizer_card_of_isConj htclass
    rw [t8_centralizer_card, hcard] at hc
    omega

omit [Finite G] in
private theorem classes_of_marking {L : Subgroup G} (f : L ≃* Eight)
    (hz : z ∈ L) (hf : f ⟨z, hz⟩ = z8) (a : L) (ha : orderOf a = 2) :
    IsConj (⟨z, hz⟩ : L) a ∨ IsConj (f.symm t8) a := by
  rcases involution_classes (f a) ((f.orderOf_eq a).trans ha) with hc | hc
  · left
    have he : f.symm z8 = ⟨z, hz⟩ := f.symm_apply_eq.mpr hf.symm
    simpa only [he, MulEquiv.coe_toMonoidHom, f.symm_apply_apply] using
      f.symm.toMonoidHom.map_isConj hc
  · right
    simpa only [MulEquiv.coe_toMonoidHom, f.symm_apply_apply] using
      f.symm.toMonoidHom.map_isConj hc

/-- Fusion of both internal classes would put at least eighteen involutions
in the specified thirteen-element core-fusion set. -/
public theorem not_conjugate_of_thirteen (h : Hypotheses z) (h13 : Nat.card (CoreFusion z) = 13)
    (L : Subgroup G) (hCL : Centralizer z ≤ L)
    (f : L ≃* Eight) (hz : z ∈ L) (hf : f ⟨z, hz⟩ = z8) :
    ¬ IsConj z (f.symm t8 : G) := by
  intro hzt
  have hall (q : Core z) (hq : orderOf q = 2) : IsConj z ((q : Centralizer z) : G) := by
    let a : L := ⟨((q : Centralizer z) : G), hCL q.val.property⟩
    have ha : orderOf a = 2 := (Subgroup.orderOf_coe a).symm.trans
      ((Subgroup.orderOf_coe q.val).trans ((Subgroup.orderOf_coe q).trans hq))
    rcases classes_of_marking f hz hf a ha with hc | hc
    · exact L.subtype.map_isConj hc
    · exact hzt.trans (L.subtype.map_isConj hc)
  let j : {q : Core z // orderOf q = 2} → CoreFusion z := fun q =>
    ⟨((q.val : Centralizer z) : G),
      mem_map_of_mem (Centralizer z).subtype q.val.property, hall q.val q.property⟩
  have hj : Function.Injective j := by
    intro a b hab
    have hv : ((a.val : Centralizer z) : G) = ((b.val : Centralizer z) : G) :=
      congrArg (fun q : CoreFusion z => (q : G)) hab
    exact Subtype.ext (Subtype.ext (Subtype.ext hv))
  have hc := Nat.card_le_card_of_injective j hj
  have hl := core_involution_lower_bound h
  rw [h13] at hc
  omega

end Index.Marking

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Construct the actual marking and ambient separation required for the
index calculation. Only the indicated source inputs are needed. -/
public theorem exists_index_involutionData (h : Hypotheses z)
    (h13 : Nat.card (CoreFusion z) = 13) (L : Subgroup G)
    (e : L ≃* alternatingGroup (Fin 8)) (hCL : Centralizer z ≤ L) :
    Nonempty (Index.InvolutionData z L) := by
  obtain ⟨hz, f, hf⟩ := Index.Marking.exists_equiv_z8 h L e hCL
  exact ⟨⟨f, hz, hf, Index.Marking.not_conjugate_of_thirteen h h13 L hCL f hz hf,
    Index.Marking.classes_of_marking f hz hf⟩⟩

/-- Source application: the constructed marking and the local odd-index
result give exhaustive ambient classes and fusion control in L. -/
public theorem source_involution_classes (h : Hypotheses z)
    (_hn : QuaternionSubgroupsNonnormal z)
    (local_intersections : ∀ g : G, g * z * g⁻¹ ∈ coreInG z → g * z * g⁻¹ ≠ z →
      IntersectionData z g)
    (h13 : Nat.card (CoreFusion z) = 13) (L : Subgroup G)
    (e : L ≃* alternatingGroup (Fin 8)) (hCL : Centralizer z ≤ L) :
    ∃ d : Index.InvolutionData z L,
      (∀ u : G, orderOf u = 2 → IsConj z u ∨ IsConj (d.t : G) u) ∧
      (∀ a : L, IsConj (⟨z, d.z_mem⟩ : L) a ↔ IsConj z (a : G)) ∧
      (∀ a : L, IsConj d.t a ↔ IsConj (d.t : G) (a : G)) := by
  obtain ⟨d⟩ := exists_index_involutionData h h13 L e hCL
  exact ⟨d, d.ambient_classes (Index.odd_index h local_intersections L hCL),
    d.controls_z h.involution, d.controls_t⟩

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition
