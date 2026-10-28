module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralCoreAction
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralChiefCount
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralBalance
public import Theory.GroupTheory.CentralNormalInvolutionCommutator

/-!
# Central commutators at matched interval boundaries

At a shared central/fixed boundary the vertex two-core is the intersection
of its adjacent edge stabilizers. One involution is central in that core;
the other supplements it to the forward edge stabilizer. Their nontrivial
commutator is an involution central in that edge. Matching both boundary
pairs gives two central edges of the commutator and bounds the margin by two.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.4), p.397.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

private theorem sup_zpowers_eq_of_relIndex_two {Q E : Subgroup G} (hQE : Q ≤ E)
    (hi : Q.relIndex E = 2) {x : G} (hx : x ∈ E) (hxQ : x ∉ Q) :
    E = Q ⊔ zpowers x := by
  have hsup : Q ⊔ zpowers x ≤ E := sup_le hQE (zpowers_le.mpr hx)
  have hi' := Subgroup.relIndex_mul_relIndex Q (Q ⊔ zpowers x) E le_sup_left hsup
  rw [hi] at hi'
  have hp : (Q.relIndex (Q ⊔ zpowers x) * (Q ⊔ zpowers x).relIndex E).Prime :=
    hi' ▸ Nat.prime_two
  rcases Nat.prime_mul_iff.mp hp with ⟨_, he⟩ | ⟨_, he⟩
  · exact (le_antisymm hsup (Subgroup.relIndex_eq_one.mp he)).symm
  · exact (hxQ ((Subgroup.relIndex_eq_one.mp he)
      ((le_sup_right : zpowers x ≤ Q ⊔ zpowers x) (mem_zpowers x)))).elim

theorem CubicTreeAction.central_commutator_at_right_boundary (h : CubicTreeAction F)
    {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) {z z' : G}
    (hz : t.CentralInvolution z) (hz' : t.CentralInvolution z')
    (d : t.CentralInterval z) (d' : t.CentralInterval z')
    (hr : 0 < d.rightMargin) (hl : 0 < d'.leftMargin)
    (halign : d.centralRight = d'.fixedLeft)
    (e : ((RankTwo.stabilizer F (t.vertex d.centralRight)) ⧸
      pCore 2 (RankTwo.stabilizer F (t.vertex d.centralRight))) ≃* Equiv.Perm (Fin 3)) :
    orderOf ⁅z, z'⁆ = 2 ∧ t.CentralEdge ⁅z, z'⁆ d.centralRight := by
  let b := d.centralRight
  let H := RankTwo.stabilizer F (t.vertex b)
  let Q := (pCore 2 H).map H.subtype
  have hprev : (RankTwo.graph F).Adj (t.vertex (b - 1)) (t.vertex b) := by
    simpa only [sub_add_cancel] using t.adjacent (b - 1)
  have hQprev : Q ≤ t.edgeStabilizer (b - 1) := by
    have hh := h.vertexTwoCore_le_edge hprev
    simpa only [Track.edgeStabilizer, sub_add_cancel] using hh
  have hQnext : Q ≤ t.edgeStabilizer b := by
    have hh := h.vertexTwoCore_le_edge (t.adjacent b).symm
    exact hh.trans (by rw [inf_comm]; rfl)
  have hQeq : Q = t.edgeStabilizer (b - 1) ⊓ t.edgeStabilizer b := by
    let P : ℤ → Prop := fun c =>
      (pCore 2 (RankTwo.stabilizer F (t.vertex c))).map
        (RankTwo.stabilizer F (t.vertex c)).subtype =
      t.edgeStabilizer (b - 1) ⊓ t.edgeStabilizer c
    have eh : ((RankTwo.stabilizer F (t.vertex (b - 1 + 1))) ⧸
        pCore 2 (RankTwo.stabilizer F (t.vertex (b - 1 + 1)))) ≃* Equiv.Perm (Fin 3) := by
      have he : b - 1 + 1 = b := by omega
      let R : ℤ → Type _ := fun c =>
        ((RankTwo.stabilizer F (t.vertex c)) ⧸ pCore 2 (RankTwo.stabilizer F (t.vertex c))) ≃*
          Equiv.Perm (Fin 3)
      exact (congrArg R he.symm).mp e
    have hh : P (b - 1 + 1) := h.vertexTwoCore_eq_twoEdges (by omega) hshort t (b - 1) eh
    exact (congrArg P (sub_add_cancel b 1)).mp hh
  have hd := d.central_lt
  have hzc := d.central (b - 1) (by dsimp [b]; omega) (by dsimp [b]; omega)
  have hzQ : z ∈ Q := by
    rw [hQeq]
    refine ⟨hzc.1, (d.fixed_iff b).2 d.centralRight_mem, ?_⟩
    change z • t.vertex (b + 1) = t.vertex (b + 1)
    apply (d.fixed_iff _).2
    have hcast := d.rightMargin_cast
    have hmem := d.centralRight_mem
    dsimp only [b] at *
    omega
  have hzC : ∀ a ∈ Q, Commute z a := fun a ha => hzc.2 a (hQprev ha)
  have hxE : z' ∈ t.edgeStabilizer b := by
    have hc := d'.leftMargin_cast
    have hm := d'.centralLeft_mem
    refine ⟨(d'.fixed_iff b).2 ⟨?_, ?_⟩, (d'.fixed_iff (b + 1)).2 ⟨?_, ?_⟩⟩ <;>
      dsimp only [b] <;> omega
  have hxQ : z' ∉ Q := by
    intro hh
    have hf : z' • t.vertex (b - 1) = t.vertex (b - 1) := (hQprev hh).1
    have hn := (d'.fixed_iff _).1 hf
    dsimp only [b] at hn
    omega
  have hi : Q.relIndex (t.edgeStabilizer b) = 2 := by
    have hh := h.vertexTwoCore_edge_relIndex (t.adjacent b).symm e
    simpa only [Track.edgeStabilizer, inf_comm] using hh
  have hn := h.not_commute_of_right_boundary hs hshort t hz d d' ⟨halign.le, by omega⟩
  have hz2 : z ^ 2 = 1 := by rw [← hz.1]; exact pow_orderOf_eq_one z
  have hz'2 : z' ^ 2 = 1 := by rw [← hz'.1]; exact pow_orderOf_eq_one z'
  exact Theory.GroupTheory.central_commutator_of_normalizing_involutions Q
    (t.edgeStabilizer b) hzQ hzC (vertexStabilizer_le_normalizer_twoCoreImage _ hxE.1)
    hz2 hz'2 (sup_zpowers_eq_of_relIndex_two hQnext hi hxE hxQ) hn

/-- The standing large-residual branch supplies both positive margins and the
local quotient needed by the central-commutator argument. -/
theorem CubicTreeAction.central_commutator_of_large_residual (h : CubicTreeAction F)
    {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (t : Track (RankTwo.graph F) G) {z z' : G}
    (hz : t.CentralInvolution z) (hz' : t.CentralInvolution z')
    (d : t.CentralInterval z) (d' : t.CentralInterval z')
    (halign : d.centralRight = d'.fixedLeft) :
    orderOf ⁅z, z'⁆ = 2 ∧ t.CentralEdge ⁅z, z'⁆ d.centralRight := by
  have hr := (h.centralInterval_chiefBounds_of_large_residual hC hA t hz d).2.2.1
  have hl := (h.centralInterval_chiefBounds_of_large_residual hC hA t hz' d').2.2.2
  obtain ⟨e⟩ := h.stabilizer_quotient_symmetricThree_of_large_residual hC hA
    (t.vertex d.centralRight)
  exact h.central_commutator_at_right_boundary hs hshort t hz hz' d d' hr hl halign e

/-- If both fixed/central boundary equalities hold, the two central edges of
the commutator force the original right margin to be at most two. -/
theorem CubicTreeAction.double_boundary_rightMargin_le_two (h : CubicTreeAction F)
    {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (t : Track (RankTwo.graph F) G)
    (hfinite : ∀ u, t.CentralInvolution u → u ∉ t.fixer)
    {z z' : G} (hz : t.CentralInvolution z) (hz' : t.CentralInvolution z')
    (d : t.CentralInterval z) (d' : t.CentralInterval z')
    (halign : d.centralRight = d'.fixedLeft) (halign' : d.fixedRight = d'.centralLeft) :
    d.rightMargin ≤ 2 := by
  have hright := h.central_commutator_of_large_residual hs hshort hC hA t hz hz' d d' halign
  have hrev (w : G) (hw : t.CentralInvolution w) : t.reverse.CentralInvolution w := by
    refine ⟨hw.1, ?_⟩
    obtain ⟨i, hi⟩ := hw.2
    refine ⟨-i - 1, (Track.centralEdge_reverse_iff t w _).2 ?_⟩
    have he : -(-i - 1) - 1 = i := by omega
    simpa only [he] using hi
  have hleft := h.central_commutator_of_large_residual hs hshort hC hA t.reverse
    (hrev z' hz') (hrev z hz) d'.reverse d.reverse (by
      change -d'.centralLeft = -d.fixedRight
      omega)
  have hl : t.CentralEdge ⁅z', z⁆ (d'.centralLeft - 1) := by
    have hh := (Track.centralEdge_reverse_iff t ⁅z',z⁆ _).1 hleft.2
    change t.CentralEdge ⁅z',z⁆ (- -d'.centralLeft - 1) at hh
    simpa only [neg_neg] using hh
  have hl' : t.CentralEdge ⁅z,z'⁆ (d'.centralLeft - 1) := by
    have hh : t.CentralEdge (⁅z',z⁆⁻¹) (d'.centralLeft - 1) :=
      ⟨(t.edgeStabilizer _).inv_mem hl.1, fun a ha => (hl.2 a ha).inv_left⟩
    simpa only [commutatorElement_inv] using hh
  have hu : t.CentralInvolution ⁅z,z'⁆ := ⟨hright.1, d.centralRight, hright.2⟩
  obtain ⟨du⟩ := h.exists_centralInterval_of_not_mem_fixer t _ hu (hfinite _ hu)
  have hb := h.centralInterval_length_le_two hs hshort t hu du
  have hrmem := (h.centralEdge_iff_in_centralInterval hs hshort t hu du _).1 hright.2
  have hlmem := (h.centralEdge_iff_in_centralInterval hs hshort t hu du _).1 hl'
  have hcast := d.rightMargin_cast
  omega

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
