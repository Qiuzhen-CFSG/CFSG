module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalGroupsStructure
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalGroupsGenerators
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalGroupsAction

/-!
# The literal opposite endpoint group

At an unlabelled vertex `v`, Goldschmidt generates `H` by the stabilizers of
`v` in the radius-four label groups at its three neighbours. The radius-three
label group at `v` lies in each generator and is normal in `H`. Conjugation
by the original vertex stabilizer permutes the three generating subgroups,
so `H` itself is normal there. All inclusions use the original tree action.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980),
the definition of `H` and the preceding paragraph on printed p.406.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
open Subgroup SimpleGraph Theory.GroupAction.CubicTree Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

/-- The three subgroups used in the source definition of the opposite endpoint. -/
def oppositeGenerator (d : CanonicalLabelSetup F s) (v a : RankTwo.Vertex F) :
    Subgroup G :=
  d.labelBall a 4 ⊓ RankTwo.stabilizer F v

/-- Goldschmidt's actual group `H`, before identifying it with an endpoint. -/
def oppositeGroup (d : CanonicalLabelSetup F s) (v : RankTwo.Vertex F) : Subgroup G :=
  ⨆ a : (RankTwo.graph F).neighborSet v, oppositeGenerator d v a.val

theorem oppositeGenerator_le (d : CanonicalLabelSetup F s)
    {v a : RankTwo.Vertex F} (ha : (RankTwo.graph F).Adj v a) :
    oppositeGenerator d v a ≤ oppositeGroup d v :=
  le_iSup (fun a : (RankTwo.graph F).neighborSet v => oppositeGenerator d v a.val) ⟨a, ha⟩

theorem oppositeGroup_le_stabilizer (d : CanonicalLabelSetup F s)
    (v : RankTwo.Vertex F) : oppositeGroup d v ≤ RankTwo.stabilizer F v := by
  exact iSup_le fun _ => inf_le_right

/-- Triangle distance embeds the actual core in every adjacent generator. -/
theorem radiusThree_le_oppositeGenerator (d : CanonicalLabelSetup F s)
    (h : CubicTreeAction F) (hr : d.radius = 3) (hs : 3 ≤ s)
    {v a : RankTwo.Vertex F} (ha : (RankTwo.graph F).Adj v a) :
    d.labelBall v 3 ≤ oppositeGenerator d v a := by
  refine le_inf ?_ (d.labelBall_le_stabilizer v 3 (by omega) hs)
  apply (closure_le _).mpr
  rintro _ ⟨w, ⟨hw, hd⟩, rfl⟩
  apply d.label_mem_labelBall hw
  have hh := h.tree.connected.dist_triangle (u := a) (v := v) (w := w)
  rw [dist_eq_one_iff_adj.mpr ha.symm] at hh
  omega

theorem radiusThree_le_oppositeGroup (d : CanonicalLabelSetup F s)
    (h : CubicTreeAction F) (hr : d.radius = 3) (hs : 3 ≤ s)
    (v : RankTwo.Vertex F) : d.labelBall v 3 ≤ oppositeGroup d v := by
  obtain ⟨f⟩ := h.exists_branchFrame v
  exact (radiusThree_le_oppositeGenerator d h hr hs (f.e 0).property).trans
    (oppositeGenerator_le d (f.e 0).property)

/-- The three factors are transported by the literal original vertex action. -/
theorem oppositeGenerator_map_conj (d : CanonicalLabelSetup F s)
    (v a : RankTwo.Vertex F) (g : G) :
    (oppositeGenerator d v a).map (MulAut.conj g).toMonoidHom =
      oppositeGenerator d (g • v) (g • a) := by
  unfold oppositeGenerator
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, d.labelBall_map_conj]
  change d.labelBall (g • a) 4 ⊓
    (MulAction.stabilizer G v).map (MulAut.conj g).toMonoidHom = _
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]

theorem oppositeGroup_normalized (d : CanonicalLabelSetup F s)
    (h : CubicTreeAction F) (v : RankTwo.Vertex F) :
    RankTwo.stabilizer F v ≤ normalizer (oppositeGroup d v : Set G) := by
  let : Finite (RankTwo.stabilizer F v) := h.finite_stabilizer v
  let : Finite (oppositeGroup d v) := Finite.of_injective
    (Subgroup.inclusion (oppositeGroup_le_stabilizer d v))
    (Subgroup.inclusion_injective _)
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  apply eq_of_le_of_card_ge
  · rw [oppositeGroup, Subgroup.map_iSup]
    apply iSup_le
    intro a
    change (oppositeGenerator d v a.val).map (MulAut.conj g).toMonoidHom ≤
      oppositeGroup d v
    rw [oppositeGenerator_map_conj, show g • v = v from hg]
    apply oppositeGenerator_le
    have ha := (translationGraphIso F g).toHom.map_adj a.property
    change (RankTwo.graph F).Adj (g • v) (g • a.val) at ha
    simpa only [show g • v = v from hg] using ha
  · exact (card_map_of_injective (MulAut.conj g).injective).ge

/-- The generated source group is normal in the actual vertex stabilizer. -/
theorem oppositeGroup_normal (d : CanonicalLabelSetup F s)
    (h : CubicTreeAction F) (v : RankTwo.Vertex F) :
    ((oppositeGroup d v).subgroupOf (RankTwo.stabilizer F v)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (oppositeGroup_le_stabilizer d v)).mpr
    (oppositeGroup_normalized d h v)

/-- The source core is normal in `H`; its normality is inherited from the
original vertex stabilizer, without an endpoint recognition assumption. -/
theorem radiusThree_normal_oppositeGroup (d : CanonicalLabelSetup F s)
    (h : CubicTreeAction F) (hr : d.radius = 3) (hs : 3 ≤ s)
    (v : RankTwo.Vertex F) :
    ((d.labelBall v 3).subgroupOf (oppositeGroup d v)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (radiusThree_le_oppositeGroup d h hr hs v)).mpr
    ((oppositeGroup_le_stabilizer d v).trans (d.labelBall_normalized v 3))

/-- The core in the literal opposite group is the concrete order-thirty-two
M₁₂ two-core already recognized from the six-arc relations. -/
theorem LocalRelations.oppositeGroup_core_equiv_secondCore
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    (v : RankTwo.Vertex F) (hv : v.type ≠ d.side) :
    Nonempty (((d.labelBall v 3).subgroupOf (oppositeGroup d v)) ≃*
      Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.SourceRecognition.SecondCore) := by
  obtain ⟨e⟩ := r.radiusThree_equiv_secondCore hr v hv
  exact ⟨(subgroupOfEquivOfLe (radiusThree_le_oppositeGroup d
    h.action.toCubicTreeAction hr (by have := h.five_le; omega) v)).trans e⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
