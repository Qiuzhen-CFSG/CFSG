module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.Setup
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.Tree
public import Theory.GroupAction.RankTwoCosetGeometry.Valence
public import Theory.GroupAction.RankTwoCosetGeometry.Kernels

/-!
# The original Goldschmidt amalgam acting on its universal cubic tree

The injective pushout maps preserve the entire marked amalgam. Primitivity
therefore kills the common normal core, and index three gives the cubic
valence. Finiteness concerns the vertex stabilizers; the acting universal
completion is not assumed finite. The final constructor applies these facts
to the original subgroups in an F.6 Goldschmidt triple.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), 2.4--2.5
and 3.2, printed pp.380 and 386--387. This constructs the full universal
action; its two-perfect reduction is a separate source argument.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open RankTwoAmalgam

private theorem left_range_map {L D R L' D' R' : Type*}
    [Group L] [Group D] [Group R] [Group L'] [Group D'] [Group R']
    {α : RankTwoAmalgam L D R} {β : RankTwoAmalgam L' D' R'} (e : Iso α β) :
    α.left.range.map e.left.toMonoidHom = β.left.range := by
  ext y
  constructor
  · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
    exact ⟨e.middle b, (e.left_commutes b).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨α.left (e.middle.symm b), ⟨e.middle.symm b, rfl⟩, ?_⟩
    simpa only [MulEquiv.coe_toMonoidHom, e.middle.apply_symm_apply] using
      e.left_commutes (e.middle.symm b)

private theorem right_range_map {L D R L' D' R' : Type*}
    [Group L] [Group D] [Group R] [Group L'] [Group D'] [Group R']
    {α : RankTwoAmalgam L D R} {β : RankTwoAmalgam L' D' R'} (e : Iso α β) :
    α.right.range.map e.right.toMonoidHom = β.right.range := by
  ext y
  constructor
  · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
    exact ⟨e.middle b, (e.right_commutes b).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨α.right (e.middle.symm b), ⟨e.middle.symm b, rfl⟩, ?_⟩
    simpa only [MulEquiv.coe_toMonoidHom, e.middle.apply_symm_apply] using
      e.right_commutes (e.middle.symm b)

/-- Cubic primitivity transports along the compatible three-group marking. -/
theorem PrimitiveCubic.of_iso {L D R L' D' R' : Type*}
    [Group L] [Group D] [Group R] [Group L'] [Group D'] [Group R']
    {α : RankTwoAmalgam L D R} {β : RankTwoAmalgam L' D' R'}
    [Finite L] [Finite R] (h : PrimitiveCubic α) (e : Iso α β) : PrimitiveCubic β := by
  refine ⟨?_, e.faithful h.faithful, ?_, ?_⟩
  · refine ⟨e.left_injective_iff.mp h.sylow.left_injective,
      e.right_injective_iff.mp h.sylow.right_injective, ?_, ?_⟩
    · obtain ⟨P, hP⟩ := h.sylow.left_sylow
      refine ⟨P.mapSurjective (f := e.left.toMonoidHom) e.left.surjective, ?_⟩
      change (P : Subgroup L).map e.left.toMonoidHom = β.left.range
      rw [hP, left_range_map e]
    · obtain ⟨P, hP⟩ := h.sylow.right_sylow
      refine ⟨P.mapSurjective (f := e.right.toMonoidHom) e.right.surjective, ?_⟩
      change (P : Subgroup R).map e.right.toMonoidHom = β.right.range
      rw [hP, right_range_map e]
  · rw [← left_range_map e]
    exact (α.left.range.index_map_equiv e.left).trans h.left_index
  · rw [← right_range_map e]
    exact (α.right.range.index_map_equiv e.right).trans h.right_index

universe u
variable {L D R : Type u} [Group L] [Group D] [Group R]
variable (α : RankTwoAmalgam L D R)

/-- A finite primitive cubic amalgam produces its actual universal tree action. -/
theorem universalCubicTreeAction [Finite L] [Finite R] (h : PrimitiveCubic α) :
    CubicTreeAction (Universal.cosetFamily α) := by
  refine ⟨?_, Universal.generated α, ?_,
    Universal.cosetGraph_isTree α h.sylow.left_injective h.sylow.right_injective⟩
  · intro i
    cases i
    · exact Finite.of_equiv L (MonoidHom.ofInjective
        (Monoid.PushoutI.of_injective
          (Universal.structureMap_injective α h.sylow.left_injective h.sylow.right_injective)
          false)).toEquiv
    · exact Finite.of_equiv R (MonoidHom.ofInjective
        (Monoid.PushoutI.of_injective
          (Universal.structureMap_injective α h.sylow.left_injective h.sylow.right_injective)
          true)).toEquiv
  · exact h.of_iso (Universal.markedIso α h.sylow.left_injective h.sylow.right_injective)

variable {G : Type*} [Group G] {F : Bool → Subgroup G}

/-- The normal core of the edge stabilizer vanishes by intrinsic primitivity. -/
theorem CubicTreeAction.common_core_eq_bot (h : CubicTreeAction F) :
    (F false ⊓ F true).normalCore = ⊥ := by
  let N := (F false ⊓ F true).normalCore
  let E := F false ⊓ F true
  have hNE : N ≤ E := Subgroup.normalCore_le E
  have he (i : Bool) (hi : E ≤ F i) :
      (N.subgroupOf E).map (Subgroup.inclusion hi) = N.subgroupOf (F i) := by
    apply Subgroup.map_injective (F i).subtype_injective
    rw [Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le (hNE.trans hi)]
    change (N.subgroupOf E).map E.subtype = N
    exact Subgroup.map_subgroupOf_eq_of_le hNE
  have hN : N.subgroupOf E = ⊥ := h.primitive.faithful (N.subgroupOf E)
    (by change ((N.subgroupOf E).map (Subgroup.inclusion inf_le_left)).Normal
        rw [he false inf_le_left]
        infer_instance)
    (by change ((N.subgroupOf E).map (Subgroup.inclusion inf_le_right)).Normal
        rw [he true inf_le_right]
        infer_instance)
  have hm := congrArg (Subgroup.map E.subtype) hN
  simpa only [Subgroup.map_subgroupOf_eq_of_le hNE, Subgroup.map_bot] using hm

/-- The action on the constructed cubic tree is faithful. -/
theorem CubicTreeAction.action_injective (h : CubicTreeAction F) :
    Function.Injective (MulAction.toPermHom G (Vertex F)) := by
  rw [← MonoidHom.ker_eq_bot_iff, global_kernel F, h.common_core_eq_bot]

/-- The vertices of either type have exactly three neighbors. -/
theorem CubicTreeAction.card_neighbor_base (h : CubicTreeAction F) (i : Bool) :
    Nat.card ((graph F).neighborSet (base F i)) = 3 := by
  rw [Subgroup.CosetGeometry.RankTwo.card_neighbor_base]
  cases i
  · have he : (inclusionAmalgam (F false) (F true)).left.range =
        (F true).subgroupOf (F false) := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.property.2
      · intro hx
        exact ⟨⟨x, x.property, hx⟩, rfl⟩
    simpa only [he, Bool.not_false] using h.primitive.left_index
  · have he : (inclusionAmalgam (F false) (F true)).right.range =
        (F false).subgroupOf (F true) := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.property.1
      · intro hx
        exact ⟨⟨x, hx, x.property⟩, rfl⟩
    simpa only [he, Bool.not_true] using h.primitive.right_index

/-- Every vertex stabilizer is finite, with no finite completion hypothesis. -/
theorem CubicTreeAction.finite_stabilizer (h : CubicTreeAction F) (v : Vertex F) :
    Finite (stabilizer F v) := by
  let : ∀ i, Finite (F i) := h.finite
  infer_instance

/-- The actual F.6 triple supplies the universal action with its original
endpoint and overlap embeddings. -/
theorem universalCubicTreeAction_of_goldschmidt [Finite G] {A B : Subgroup G}
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥) :
    CubicTreeAction (Universal.cosetFamily (inclusionAmalgam A B)) :=
  universalCubicTreeAction _ (primitiveCubic_of_goldschmidt h hcore)

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
