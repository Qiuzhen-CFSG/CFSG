module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralCoreIndex
public import Theory.GroupTheory.CubicCentralizerCount
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.LargeLocalQuotients

/-!
# Chief bounds at both ends of the actual fixed interval

The involution lies outside the two-core of each endpoint stabilizer, while
its centralizer in that two-core has index at most two to the corresponding
margin. The cubic centralizer estimate bounds the complete noncentral binary
chief count and makes the margin positive. The final theorem applies the
proved large-residual local quotient results to discharge those local inputs.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.3), p.397.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

private theorem vertex_chiefBounds (h : CubicTreeAction F) (v : RankTwo.Vertex F)
    {z : G} (hzfix : z ∈ RankTwo.stabilizer F v) (hz : orderOf z = 2)
    (hn : z ∉ (pCore 2 (RankTwo.stabilizer F v)).map (RankTwo.stabilizer F v).subtype)
    (r : ℕ) (hi : (centralizer ({z} : Set G)).relIndex
      ((pCore 2 (RankTwo.stabilizer F v)).map (RankTwo.stabilizer F v).subtype) ≤ 2 ^ r)
    (e : ((RankTwo.stabilizer F v) ⧸ pCore 2 (RankTwo.stabilizer F v)) ≃*
      Equiv.Perm (Fin 3))
    (hself : centralizer (pCore 2 (RankTwo.stabilizer F v) : Set _) ≤
      pCore 2 (RankTwo.stabilizer F v)) :
    (∀ s : NoncentralChiefRefinement.ChiefSeries (RankTwo.stabilizer F v),
      s.head = ⊥ → s.last = ⊤ → s.noncentralTwoCount ≤ r) ∧ 0 < r := by
  let : ∀ i, Finite (F i) := h.finite
  let H := RankTwo.stabilizer F v
  let zz : H := ⟨z, hzfix⟩
  have hzz : orderOf zz = 2 :=
    (orderOf_injective H.subtype H.subtype_injective zz).symm.trans hz
  have hzn : zz ∉ pCore 2 H := fun hzQ => hn ⟨zz, hzQ, rfl⟩
  have hc : centralizer ({zz} : Set H) = (centralizer ({z} : Set G)).comap H.subtype := by
    ext a
    simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext_iff
  have hib : (centralizer ({zz} : Set H)).relIndex (pCore 2 H) ≤ 2 ^ r := by
    rw [hc, Subgroup.relIndex_comap]
    exact hi
  exact ⟨fun s h0 h1 => Theory.GroupTheory.CubicCentralizerCount.noncentralTwoCount_le
    e hzz hzn r hib s h0 h1,
    Theory.GroupTheory.CubicCentralizerCount.bound_positive_of_core_selfCentralizing
      e hself hzz hzn r hib⟩

theorem CubicTreeAction.centralInterval_right_chiefBounds (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) {z : G} (hz : t.CentralInvolution z)
    (d : t.CentralInterval z)
    (e : ((RankTwo.stabilizer F (t.vertex d.fixedRight)) ⧸
      pCore 2 (RankTwo.stabilizer F (t.vertex d.fixedRight))) ≃* Equiv.Perm (Fin 3))
    (hself : centralizer (pCore 2 (RankTwo.stabilizer F (t.vertex d.fixedRight)) : Set _) ≤
      pCore 2 (RankTwo.stabilizer F (t.vertex d.fixedRight))) :
    (∀ s : NoncentralChiefRefinement.ChiefSeries (RankTwo.stabilizer F (t.vertex d.fixedRight)),
      s.head = ⊥ → s.last = ⊤ → s.noncentralTwoCount ≤ d.rightMargin) ∧
        0 < d.rightMargin := by
  apply vertex_chiefBounds h (t.vertex d.fixedRight) (z := z)
  · exact (d.fixed_iff _).2 ⟨le_trans d.centralRight_mem.1 d.centralRight_mem.2, le_rfl⟩
  · exact hz.1
  · exact h.centralInvolution_not_mem_rightCore t d
  · exact h.centralizer_core_relIndex_le_rightMargin t d
  · exact e
  · exact hself

theorem CubicTreeAction.centralInterval_left_chiefBounds (h : CubicTreeAction F)
    (t : Track (RankTwo.graph F) G) {z : G} (hz : t.CentralInvolution z)
    (d : t.CentralInterval z)
    (e : ((RankTwo.stabilizer F (t.vertex d.fixedLeft)) ⧸
      pCore 2 (RankTwo.stabilizer F (t.vertex d.fixedLeft))) ≃* Equiv.Perm (Fin 3))
    (hself : centralizer (pCore 2 (RankTwo.stabilizer F (t.vertex d.fixedLeft)) : Set _) ≤
      pCore 2 (RankTwo.stabilizer F (t.vertex d.fixedLeft))) :
    (∀ s : NoncentralChiefRefinement.ChiefSeries (RankTwo.stabilizer F (t.vertex d.fixedLeft)),
      s.head = ⊥ → s.last = ⊤ → s.noncentralTwoCount ≤ d.leftMargin) ∧
        0 < d.leftMargin := by
  apply vertex_chiefBounds h (t.vertex d.fixedLeft) (z := z)
  · exact (d.fixed_iff _).2 ⟨le_rfl, le_trans d.centralLeft_mem.1 d.centralLeft_mem.2⟩
  · exact hz.1
  · exact h.centralInvolution_not_mem_leftCore t d
  · exact h.centralizer_core_relIndex_le_leftMargin t d
  · exact e
  · exact hself

/-- The source large-residual branch discharges both local quotient premises
and both self-centralizing two-core premises in the interval chief bounds. -/
theorem CubicTreeAction.centralInterval_chiefBounds_of_large_residual (h : CubicTreeAction F)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (t : Track (RankTwo.graph F) G) {z : G} (hz : t.CentralInvolution z)
    (d : t.CentralInterval z) :
    (∀ s : NoncentralChiefRefinement.ChiefSeries (RankTwo.stabilizer F (t.vertex d.fixedRight)),
      s.head = ⊥ → s.last = ⊤ → s.noncentralTwoCount ≤ d.rightMargin) ∧
    (∀ s : NoncentralChiefRefinement.ChiefSeries (RankTwo.stabilizer F (t.vertex d.fixedLeft)),
      s.head = ⊥ → s.last = ⊤ → s.noncentralTwoCount ≤ d.leftMargin) ∧
      0 < d.rightMargin ∧ 0 < d.leftMargin := by
  obtain ⟨eR⟩ := h.stabilizer_quotient_symmetricThree_of_large_residual hC hA (t.vertex d.fixedRight)
  obtain ⟨eL⟩ := h.stabilizer_quotient_symmetricThree_of_large_residual hC hA (t.vertex d.fixedLeft)
  have hr := h.centralInterval_right_chiefBounds t hz d eR
    (h.stabilizer_centralizer_twoCore_le_of_large_residual hC hA (t.vertex d.fixedRight))
  have hl := h.centralInterval_left_chiefBounds t hz d eL
    (h.stabilizer_centralizer_twoCore_le_of_large_residual hC hA (t.vertex d.fixedLeft))
  exact ⟨hr.1, hl.1, hr.2, hl.2⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
