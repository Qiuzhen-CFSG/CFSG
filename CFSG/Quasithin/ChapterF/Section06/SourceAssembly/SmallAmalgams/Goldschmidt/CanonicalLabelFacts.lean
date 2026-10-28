module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CanonicalLabelSetup
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Theory.GroupAction.CubicTree.CentralTranslation

/-!
# Canonical labels and all track-central involutions

The label at the appropriate endpoint belongs to the center of each edge
stabilizer. Cyclicity of that finite center identifies every edge-central
involution with this label, including involutions on other tracks. Label
commutation follows from the literal fixed-vertex action. Translation of the
chosen track gives the exact fixed intervals at every translated center.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.8)--(6.12),
printed pp.399--403. These facts are shared by the odd-radius bound and the
Mathieu recognition argument.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

/-- Labels commute whenever the first label fixes the second label's center. -/
theorem CanonicalLabelSetup.labels_commute_of_fixed (d : CanonicalLabelSetup F s)
    {v w : RankTwo.Vertex F} (hw : w.type = d.side)
    (hfix : d.label v • w = w) : Commute (d.label v) (d.label w) :=
  ((d.central w hw).2 (d.label v) hfix).symm

/-- The canonical radius and short-arc bound give commuting labels. -/
theorem CanonicalLabelSetup.labels_commute_of_dist_le (d : CanonicalLabelSetup F s)
    {v w : RankTwo.Vertex F} (hv : v.type = d.side) (hw : w.type = d.side)
    (hd : (RankTwo.graph F).dist v w ≤ d.radius + 1)
    (hs : (RankTwo.graph F).dist v w ≤ s) : Commute (d.label v) (d.label w) :=
  d.labels_commute_of_fixed hw (d.fixes_ball v hv w hd hs)

theorem CanonicalLabelSetup.shifted_type (d : CanonicalLabelSetup F s) (k : ℤ) :
    (d.track.vertex (d.center + 2*k)).type = d.side := by
  rw [← d.track.zpow_translate k d.center]
  exact d.center_type

theorem CanonicalLabelSetup.shifted_fixed_iff (d : CanonicalLabelSetup F s) (k i : ℤ) :
    d.label (d.track.vertex (d.center + 2*k)) • d.track.vertex i = d.track.vertex i ↔
      d.center + 2*k - (d.radius + 1) ≤ i ∧ i ≤ d.center + 2*k + (d.radius + 1) := by
  have hz : d.label (d.track.vertex (d.center + 2*k)) =
      (MulAut.conj (d.track.translation ^ k)) (d.label (d.track.vertex d.center)) := by
    rw [← d.track.zpow_translate k d.center]
    exact d.conjugate _ _ d.center_type
  rw [hz]
  have hh := d.track.fixed_shift_iff _ _ (d.track.zpow_translate k)
    (d.label (d.track.vertex d.center)) (i - 2*k)
  have he : i - 2*k + 2*k = i := by omega
  rw [he, d.interval.fixed_iff, d.fixed_left, d.fixed_right] at hh
  exact hh.trans (by omega)

theorem CanonicalLabelSetup.label_inv (d : CanonicalLabelSetup F s)
    {v : RankTwo.Vertex F} (hv : v.type = d.side) : (d.label v)⁻¹ = d.label v := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [d.order_two v hv, pow_two] using pow_orderOf_eq_one (d.label v)

theorem CanonicalLabelSetup.label_mul_self (d : CanonicalLabelSetup F s)
    {v : RankTwo.Vertex F} (hv : v.type = d.side) : d.label v * d.label v = 1 := by
  have h := pow_orderOf_eq_one (d.label v)
  rw [d.order_two v hv] at h
  simpa only [pow_two] using h

theorem CanonicalLabelSetup.eq_label_of_central_edge (d : CanonicalLabelSetup F s)
    (h : CubicTreeAction F) (hs : 1 ≤ s)
    {v w : RankTwo.Vertex F} (hadj : (RankTwo.graph F).Adj v w)
    (hv : v.type = d.side) {z : G} (hz : orderOf z = 2)
    (hmem : z ∈ RankTwo.stabilizer F v ⊓ RankTwo.stabilizer F w)
    (hcentral : ∀ g ∈ RankTwo.stabilizer F v ⊓ RankTwo.stabilizer F w, Commute z g) :
    z = d.label v := by
  let E := RankTwo.stabilizer F v ⊓ RankTwo.stabilizer F w
  let : Finite (RankTwo.stabilizer F v) := h.finite_stabilizer v
  let : Finite E := Finite.of_injective (Subgroup.inclusion (show E ≤ RankTwo.stabilizer F v from inf_le_left))
    (Subgroup.inclusion_injective _)
  let : IsCyclic (Subgroup.center E) := d.edge_center_cyclic v w hadj
  have hzE : (⟨z, hmem⟩ : E) ∈ Subgroup.center E := mem_center_iff.mpr (fun g =>
    Subtype.ext (hcentral g g.property).symm.eq)
  have hlabel : d.label v ∈ E := by
    refine ⟨(d.central v hv).1, ?_⟩
    exact d.fixes_ball v hv w (by rw [dist_eq_one_iff_adj.mpr hadj]; omega)
      (by rw [dist_eq_one_iff_adj.mpr hadj]; exact hs)
  have hlabelE : (⟨d.label v, hlabel⟩ : E) ∈ Subgroup.center E := mem_center_iff.mpr
    (fun g => Subtype.ext ((d.central v hv).2 g g.property.1).symm.eq)
  have he : (⟨⟨z, hmem⟩, hzE⟩ : Subgroup.center E) = ⟨⟨d.label v, hlabel⟩, hlabelE⟩ :=
    IsCyclic.eq_of_orderOf_eq_two
      ((orderOf_coe (⟨⟨z, hmem⟩, hzE⟩ : Subgroup.center E)).symm.trans
        ((orderOf_coe (⟨z, hmem⟩ : E)).symm.trans hz))
      ((orderOf_coe (⟨⟨d.label v, hlabel⟩, hlabelE⟩ : Subgroup.center E)).symm.trans
        ((orderOf_coe (⟨d.label v, hlabel⟩ : E)).symm.trans (d.order_two v hv)))
  exact congrArg (fun x : Subgroup.center E => (x.val : G)) he

theorem CanonicalLabelSetup.centralInvolution_eq_label (d : CanonicalLabelSetup F s)
    (h : CubicTreeAction F) (hs : 1 ≤ s)
    (t : Track (RankTwo.graph F) G) {z : G} (hz : t.CentralInvolution z) :
    ∃ i : ℤ, (t.vertex i).type = d.side ∧ z = d.label (t.vertex i) := by
  obtain ⟨j, hj⟩ := hz.2
  by_cases ht : (t.vertex j).type = d.side
  · exact ⟨j, ht, d.eq_label_of_central_edge h hs (t.adjacent j) ht hz.1 hj.1 hj.2⟩
  · have ht' : (t.vertex (j + 1)).type = d.side := by
      have hn := (t.adjacent j).1
      cases h0 : (t.vertex j).type <;> cases h1 : (t.vertex (j + 1)).type <;>
        cases h2 : d.side <;> simp_all
    exact ⟨j + 1, ht', d.eq_label_of_central_edge h hs (t.adjacent j).symm ht' hz.1
      ⟨hj.1.2, hj.1.1⟩ (fun g hg => hj.2 g ⟨hg.2, hg.1⟩)⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
