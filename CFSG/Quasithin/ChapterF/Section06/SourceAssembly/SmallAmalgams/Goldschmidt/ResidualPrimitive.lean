module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.UniversalSetup
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.ResidualTree
public import Theory.GroupTheory.Amalgam.NormalSubamalgam

/-!
# Goldschmidt's two-perfect normal-base reduction

Intersect the two finite vertex groups with the actual ambient two-residual.
The local residuals generate it. The normal supplement argument preserves
faithfulness, while the literal graph isomorphism preserves index three.
The overlap remains a two-group, so these index-three inclusions are Sylow.
Together with the preserved tree this gives the full two-perfect action,
without imposing finiteness on the acting group or adding local hypotheses.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (3.2),
printed pp.386--387.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Subgroup.CosetGeometry
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

/-- The literal local groups inside the ambient two-residual. -/
def residualFamily (F : Bool → Subgroup G) : Bool → Subgroup (pResidual 2 G) :=
  fun i => (F i).subgroupOf (pResidual 2 G)

/-- Local finiteness survives restriction to the actual residual. -/
theorem CubicTreeAction.residual_finite (h : CubicTreeAction F) (i : Bool) :
    Finite (residualFamily F i) := by
  let : Finite (F i) := h.finite i
  exact Finite.of_injective (fun x : residualFamily F i => (⟨x.1.1, x.2⟩ : F i))
    (fun x y he => Subtype.ext (Subtype.ext (congrArg (fun z : F i => (z : G)) he)))

/-- The two intersected vertex groups generate the ambient residual. -/
theorem CubicTreeAction.residual_generated (h : CubicTreeAction F) :
    residualFamily F false ⊔ residualFamily F true = ⊤ := by
  apply Subgroup.map_injective (pResidual 2 G).subtype_injective
  simp only [Subgroup.map_sup, residualFamily, subgroupOf_map_subtype,
    ← MonoidHom.range_eq_map, range_subtype]
  apply le_antisymm (sup_le inf_le_right inf_le_right)
  calc
    pResidual 2 G = (pResidual 2 (F false)).map (F false).subtype ⊔
        (pResidual 2 (F true)).map (F true).subtype := h.residual_source.1
    _ ≤ (F false ⊓ pResidual 2 G) ⊔ (F true ⊓ pResidual 2 G) :=
      sup_le_sup (le_inf (map_subtype_le _) (map_pResidual_le 2 _))
        (le_inf (map_subtype_le _) (map_pResidual_le 2 _))

private theorem residual_index (h : CubicTreeAction F) (i : Bool) :
    ((residualFamily F (!i)).subgroupOf (residualFamily F i)).index = 3 := by
  rw [← RankTwo.card_neighbor_base]
  have he := Nat.card_congr (h.residual_graphIso.mapNeighborSet
    (RankTwo.base (residualFamily F) i))
  exact he.trans (h.card_neighbor_base i)

/-- Intrinsic primitivity, the Sylow embeddings and both cubic indices pass
to the intersected local groups of the actual normal residual. -/
theorem CubicTreeAction.residual_primitive (h : CubicTreeAction F) :
    PrimitiveCubic (inclusionAmalgam (residualFamily F false) (residualFamily F true)) := by
  let A := residualFamily F false
  let B := residualFamily F true
  let α := inclusionAmalgam A B
  have hli : α.left.range.index = 3 := by
    change (Subgroup.inclusion (show A ⊓ B ≤ A from inf_le_left)).range.index = 3
    rw [Subgroup.inclusion_range, inf_subgroupOf_left]
    exact residual_index h false
  have hri : α.right.range.index = 3 := by
    change (Subgroup.inclusion (show A ⊓ B ≤ B from inf_le_right)).range.index = 3
    rw [Subgroup.inclusion_range, inf_subgroupOf_right]
    exact residual_index h true
  obtain ⟨P, hP⟩ := h.primitive.sylow.left_sylow
  have hp : IsPGroup 2 (F false ⊓ F true : Subgroup G) := by
    have hm : (P : Subgroup (F false)).map (F false).subtype = F false ⊓ F true := by
      rw [hP, ← MonoidHom.range_comp]
      exact (F false ⊓ F true).range_subtype
    rw [← hm]
    exact P.isPGroup'.map (F false).subtype
  have hp0 : IsPGroup 2 (A ⊓ B : Subgroup (pResidual 2 G)) := hp.comap_subtype
  have hpl : IsPGroup 2 α.left.range :=
    hp0.of_surjective α.left.rangeRestrict α.left.rangeRestrict_surjective
  have hpr : IsPGroup 2 α.right.range :=
    hp0.of_surjective α.right.rangeRestrict α.right.rangeRestrict_surjective
  refine ⟨⟨Subgroup.inclusion_injective inf_le_left,
    Subgroup.inclusion_injective inf_le_right, ?_, ?_⟩, ?_, hli, hri⟩
  · exact ⟨hpl.toSylow (by rw [hli]; decide), rfl⟩
  · exact ⟨hpr.toSylow (by rw [hri]; decide), rfl⟩
  · apply RankTwoAmalgam.faithful_ofSubgroups_of_completion A (A ⊓ B) B
      inf_le_left inf_le_right h.residual_generated
    intro K hK hKT
    let : K.Normal := hK
    apply normal_subgroup_overlap_eq_bot (pResidual 2 G) (F false ⊓ F true)
      h.residual_source.2.2 ?_ K hKT
    intro L hL hLT
    let : L.Normal := hL
    exact le_bot_iff.mp ((normal_le_normalCore.mpr hLT).trans h.common_core_eq_bot.le)

/-- Goldschmidt's actual two-perfect normal-base reduction, including its
finite primitive cubic local amalgam and the same tree. -/
theorem CubicTreeAction.twoPerfectResidual (h : CubicTreeAction F) :
    TwoPerfectTreeAction (residualFamily F) where
  finite := h.residual_finite
  generated := h.residual_generated
  primitive := h.residual_primitive
  tree := h.residual_tree
  twoPerfect := h.residual_source.2.1

/-- Apply (3.2) to the original F.6 amalgam's universal completion. -/
theorem twoPerfectResidual_of_goldschmidt [Finite G] {A B : Subgroup G}
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥) :
    TwoPerfectTreeAction
      (residualFamily (RankTwoAmalgam.Universal.cosetFamily (inclusionAmalgam A B))) :=
  (universalCubicTreeAction_of_goldschmidt h hcore).twoPerfectResidual

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
