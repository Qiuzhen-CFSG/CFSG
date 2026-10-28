module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.G2.Geometry.Recognition
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.G2.Geometry.Embedding

/-!
# The span of a G₂ block flag

The entire intrinsic U-layer has natural-six or Weyl-seven coordinates over its
original central projection. In either model the supplied component Sylow and
commutator identity recognize V as a doubly singular line. Every actual
normalizer of K acts by a full octonion G₂(2) operator on these same coordinates.
Fixing the point Z confines the conjugates to its three-dimensional pencil;
moving V forces their span to have order eight. It is elementary because it
lies in the original characteristic U-layer, so its two-rank is three.

Source: Aschbacher--Smith, original 14.6.10(5), printed p.1029.
No vanishing of the central fixed subgroup or whole-core reconstruction is
assumed. The existing source consumer supplies precisely FlagData.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.G2SecondParabolic
open ChapterC Atlas.G2 Atlas.G2.Natural
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open Chapter14.Section07.G2Exclusion.MarkedGeometry
open Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.LineMarking
variable {G : Type*} [Group G] [Finite G] {K V Z J : Subgroup G}

omit [Finite G] in
/-- Every conjugate remains in the actual elementary U-layer. -/
theorem FlagData.span_elementary (d : FlagData K V Z J) :
    IsElementaryAbelian 2 (conjugateSpanBy V J) := by
  let : IsElementaryAbelian 2 (blockU K) := d.block.short.elementary
  let : IsElementaryAbelian 2 ((blockU K).map K.subtype) := IsElementaryAbelian.map K.subtype
  have hle : conjugateSpanBy V J ≤ (blockU K).map K.subtype :=
    conjugateSpanBy_le d.plane_le (d.normalizes.trans
      (normalizer_le_normalizer_characteristic_image K (blockU K)))
  exact IsElementaryAbelian.of_injective (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)

/-- The doubly singular pencil computes the literal conjugate span. -/
theorem FlagData.span_card (d : FlagData K V Z J) :
    Nat.card (conjugateSpanBy V J) = 8 := by
  let : IsElementaryAbelian 2 (blockU K) := d.block.short.elementary
  obtain ⟨m⟩ := d.block.natural_model
  let h := d.block.short
  let k := coordinateActor K m
  have hk : Function.Surjective k := coordinateActor_surjective K m
  rcases intrinsic_natural_or_weyl h m with ⟨E,hE,hproj⟩ | ⟨E,hE,hproj⟩
  · let i := coordinateEmbedding K E.symm
    have hi : Function.Injective i := coordinateEmbedding_injective K E.symm
    have hV : V ≤ i.range := by rw [coordinateEmbedding_range]; exact d.plane_le
    have hcomp (x : commutator (Model (ZMod 2))) (w : Space (ZMod 2)) :
        E.symm (action (ZMod 2) x.val w) = intrinsicAction h m x (E.symm w) := by
      apply E.injective
      rw [E.apply_symm_apply, hE, E.apply_symm_apply]
      rfl
    have hact := coordinateEmbedding_component K h m (action (ZMod 2)) E.symm hcomp
    obtain ⟨S,hS⟩ := coordinatePlane_sylow d (action (ZMod 2)) i k hk hact
    obtain ⟨L,hL⟩ := natural_sylow_line (coordinatePlane i V)
      ((coordinatePlane_card i hi V hV).trans d.plane_card) S hS
    apply flag_card_of_line d naturalMap (action (ZMod 2)) naturalMap_equivariant
      i hi hV L hL
    apply coordinateEmbedding_normalizer K d (action (ZMod 2)) E.symm
    intro a
    obtain ⟨g,hg⟩ := natural_coordinates_automorphism m E hproj a
    refine ⟨g,fun w => ?_⟩
    apply E.injective
    rw [E.apply_symm_apply, hg, E.apply_symm_apply]
  · let i := coordinateEmbedding K E
    have hi : Function.Injective i := coordinateEmbedding_injective K E
    have hV : V ≤ i.range := by rw [coordinateEmbedding_range]; exact d.plane_le
    have hcomp (x : commutator (Model (ZMod 2))) (w : TraceZero (ZMod 2)) :
        E (traceZeroAction (ZMod 2) x.val w) = intrinsicAction h m x (E w) := hE x w
    have hact := coordinateEmbedding_component K h m (traceZeroAction (ZMod 2)) E hcomp
    obtain ⟨S,hS⟩ := coordinatePlane_sylow d (traceZeroAction (ZMod 2)) i k hk hact
    obtain ⟨X,hX⟩ := coordinatePlane_commutator d (traceZeroAction (ZMod 2)) i hi hV k hact
    obtain ⟨L,hL⟩ := weyl_line_of_sylow_commutator (coordinatePlane i V)
      ((coordinatePlane_card i hi V hV).trans d.plane_card) S hS X hX
    apply flag_card_of_line d weylMap (traceZeroAction (ZMod 2)) weylMap_equivariant
      i hi hV L hL
    apply coordinateEmbedding_normalizer K d (traceZeroAction (ZMod 2)) E
    intro a
    obtain ⟨g,hg⟩ := weyl_coordinates_automorphism h m E hE hproj a
    exact ⟨g,fun w => (hg w).symm⟩

/-- Prime rank uses the original group convention and is exactly three. -/
theorem FlagData.span_rank (d : FlagData K V Z J) :
    primeRank 2 (conjugateSpanBy V J) = 3 := by
  let : IsElementaryAbelian 2 (conjugateSpanBy V J) := d.span_elementary
  rw [← IsElementaryAbelian.log_card_eq_primeRank, d.span_card]
  decide

/-- The full local conclusion consumed by original 14.6.10(5). -/
theorem flag_span (d : FlagData K V Z J) :
    IsElementaryAbelian 2 (conjugateSpanBy V J) ∧
      Nat.card (conjugateSpanBy V J) = 8 ∧ primeRank 2 (conjugateSpanBy V J) = 3 :=
  ⟨d.span_elementary, d.span_card, d.span_rank⟩

end CFSG.Quasithin.Chapter14.Section06.G2SecondParabolic
