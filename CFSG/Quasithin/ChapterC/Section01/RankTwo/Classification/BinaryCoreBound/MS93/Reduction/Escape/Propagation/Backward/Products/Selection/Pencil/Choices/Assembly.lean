module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.RelativePencil
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.LocalAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.FiniteGeometry

/-!
# Two generating relative normalizers with distinct intersection lines

At the start of the critical pair, the marked natural-module action sends
its endpoint Z-layer to an order-two matrix subgroup whose fixed plane is
the first edge displacement. The binary plane calculation gives two matrix
translates of that plane with generating normalizers and different fixed-plane
intersections. Lift the matrices to actual neighbors, identify their relative
normalizer images, and lift generation through the contained local kernel.
The coordinate intersection identities then distinguish the actual edge lines.

All model and finite-plane premises are discharged here from the supplied
local facts. The generating subgroup is the literal relative normalizer
G_a ∩ N(Q_t), as defined on printed p.881. The favorable backward-span choices
and the product assertions remain with the parent Selection development.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the distinct-line choice in the proof of (4.3.7)(i), printed p.887.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection
open Choices
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

/-- Two actual neighbors have generating source relative normalizers and
meet the first edge plane in different lines. No model or choice premise
remains in this source-facing conclusion. -/
theorem exists_distinct_generating_relativeNormalizer_lines (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (β : Vertex R) (hβ : Before p.a' p.a β 1) :
    ∃ t u, Adjacent R p.a t ∧
      (stabilizer R p.a ⊓ normalizer (Q R t : Set (FreeAmalgam R))) ⊔ Z R p.a' =
        stabilizer R p.a ∧
      Adjacent R p.a u ∧
      (stabilizer R p.a ⊓ normalizer (Q R u : Set (FreeAmalgam R))) ⊔ Z R p.a' =
        stabilizer R p.a ∧
      edgeLine p β t ≠ edgeLine p β u := by
  obtain ⟨model⟩ := localModel_nonempty source modules p.a p.color_a
  have hplane : Nat.card (model.coordinates (edgeDisplacement p.a β)) = 4 := by
    rw [model.coordinates_card _
      (Initial.edge_le_natural source p.a β p.color_a hβ.endpoint_adjacent)]
    exact edge_card p (by omega) initial p.a β p.color_a hβ.endpoint_adjacent
  have hactor : Nat.card (model.actorImage (Z R p.a')) = 2 := by
    rw [model.actorImage_card _ p.end_Z_le_start_stabilizer]
    exact endpoint_actor_index source p modules (Classical.choice (initial p))
  have hfixed : fixedSpace (model.actorImage (Z R p.a')) =
      model.coordinates (edgeDisplacement p.a β) := by
    rw [model.fixedSpace_actorImage _ p.end_Z_le_start_stabilizer,
      endpoint_fixed_plane source p hb modules initial control edge β hβ]
  obtain ⟨g, h, hg, hh, hne⟩ := FiniteGeometry.exists_generating_plane_translates
    _ hplane _ hactor (by rw [hfixed]; exact hplane)
  obtain ⟨t, hat, ht⟩ := model.realizes_plane source p.color_a hβ.endpoint_adjacent g
  obtain ⟨u, hau, hu⟩ := model.realizes_plane source p.color_a hβ.endpoint_adjacent h
  have lift (x : Vertex R) (hax : Adjacent R p.a x)
      (hgen : normalizer (planeFixer (model.coordinates (edgeDisplacement p.a x)) : Set SL) ⊔
        model.actorImage (Z R p.a') = ⊤) :
      (stabilizer R p.a ⊓ normalizer (Q R x : Set (FreeAmalgam R))) ⊔ Z R p.a' =
        stabilizer R p.a := by
    apply model.generation_lifts _ _ inf_le_left p.end_Z_le_start_stabilizer
      ((LocalModel.kernel_le_relativeNormalizer x p.color_a hax).trans le_sup_left)
    rw [model.relativeNormalizer_actorImage hb modules p initial control edge
      FiniteGeometry.planeFixer_card x p.color_a hax]
    exact hgen
  refine ⟨t, u, hat, lift t hat (by rw [ht]; exact hg), hau,
    lift u hau (by rw [hu]; exact hh), ?_⟩
  intro he
  apply hne
  rw [hfixed]
  have hc := congrArg model.coordinates he
  rw [edgeLine_eq_inf_displacements source p hb modules initial control edge β t hβ hat,
    edgeLine_eq_inf_displacements source p hb modules initial control edge β u hβ hau,
    model.coordinates_inf, model.coordinates_inf, ht, hu] at hc
  exact hc

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection
