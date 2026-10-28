module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.ExtensionRecognitionFaithfulness
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.ExtensionRecognitionAlignment
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.ExtensionPointGraph
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.Quadrangle
public import Theory.Combinatorics.GraphAutomorphismTransport

/-!
# Recognition of the doubled binary unitary completion with both parabolics

Diameter at most four makes the actual plane-coset graph SRG(27,10,1,5)
and forces completion order 51840. The native model has the same diameter
through its explicit graph isomorphism with the ordinary unitary graph.
SRG uniqueness compares the two actual graphs. Their faithful actions both
fill the full graph automorphism group, whose order is at most 51840.
This produces an equivariant group isomorphism. An incident-flag transporter
then aligns the images of both literal endpoint subgroups.

The only source premise is the diameter bound, supplied by the order-four
endpoint involutions in ExtensionQuadrangle. No abstract recognition
certificate, endpoint identification or group-order identification is assumed.
Source: Aschbacher--Smith F.4.26 and F.5.5(4), printed pp.288 and302.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.Extension
open Theory.Combinatorics
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
open GreenBook.LieModels.UnitaryFour
local notation "h1" => (Nat.le_refl 1)
local notation "E" => GreenBook.LieModels.UnitaryFour.Extension.ProjectiveExtension 1 h1

/-- The doubled native graph inherits the actual ordinary quadrangle metric. -/
theorem native_diameter_le_four (v w : modelCompletion.Vertex) :
    modelCompletion.graph.dist v w ≤ 4 := by
  have hd := (SourceCompletion.UnitaryTwo.modelCompletion.quadrangle_metric
    BinaryCompletion.projective_card).2.1
  change ∀ v w, (RankTwo.graph SourceCompletion.UnitaryTwo.modelCompletion.family).dist v w ≤ 4 at hd
  rw [ordinary_family_eq] at hd
  have hc := SourceCompletion.UnitaryTwo.modelCompletion.connected
  change (RankTwo.graph SourceCompletion.UnitaryTwo.modelCompletion.family).Connected at hc
  rw [ordinary_family_eq] at hc
  have he : ∀ v w, (RankTwo.graph ExtensionFive.AE).dist v w ≤ 4 := by
    intro v w
    obtain ⟨a, rfl⟩ := ExtensionFive.graphIso.surjective v
    obtain ⟨b, rfl⟩ := ExtensionFive.graphIso.surjective w
    obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist a b
    calc
      _ ≤ (p.map ExtensionFive.graphIso.toHom).length := SimpleGraph.dist_le _
      _ = p.length := SimpleGraph.Walk.length_map _ _
      _ ≤ 4 := hp ▸ hd a b
  change (RankTwo.graph modelCompletion.family).dist v w ≤ 4
  revert v w
  change ∀ (v w : Subgroup.CosetGeometry.Vertex modelCompletion.family),
    (RankTwo.graph modelCompletion.family).dist v w ≤ 4
  rw [model_family_eq]
  exact he

namespace Completion
variable {G : Type*} [Group G] [Finite G] (c : Completion G)

/-- The graph comparison identifies the original faithful actions. -/
theorem exists_equivariant_native_of_diameter (hd : ∀ v w, c.graph.dist v w ≤ 4) :
    ∃ (q : c.pointGraph ≃g modelCompletion.pointGraph)
      (e : G ≃* E), ∀ g x, e g • q x = q (g • x) := by
  obtain ⟨⟨a⟩, _⟩ := c.pointGraph_recognition_of_diameter hd
  obtain ⟨⟨b⟩, hb⟩ := modelCompletion.pointGraph_recognition_of_diameter native_diameter_le_four
  let q := a.symm.trans b
  let ρ := MulAction.toPermHom G c.Point
  let σ := MulAction.toPermHom E modelCompletion.Point
  have hρ : ∀ g x y, c.pointGraph.Adj (ρ g x) (ρ g y) ↔ c.pointGraph.Adj x y :=
    fun g _ _ => c.pointGraphAction.adj_iff g
  have hσ : ∀ g x y, modelCompletion.pointGraph.Adj (σ g x) (σ g y) ↔
      modelCompletion.pointGraph.Adj x y := fun g _ _ => modelCompletion.pointGraphAction.adj_iff g
  let f := (graphAutomorphismEquiv q).toMonoidHom.comp (graphActionHom ρ hρ)
  let k := graphActionHom σ hσ
  have hf : Function.Injective f :=
    (graphAutomorphismEquiv q).injective.comp (graphActionHom_injective ρ hρ c.point_action_injective)
  have hk : Function.Injective k := graphActionHom_injective σ hσ modelCompletion.point_action_injective
  have : Finite (modelCompletion.pointGraph ≃g modelCompletion.pointGraph) :=
    Finite.of_injective (fun a : modelCompletion.pointGraph ≃g modelCompletion.pointGraph => a.toEquiv)
      (fun a b h => by apply RelIso.ext; intro x; exact Equiv.congr_fun h x)
  have hfB : Function.Bijective f := hf.bijective_of_nat_card_le (by
    rw [c.card_eq_of_diameter hd]
    exact hb)
  have hkB : Function.Bijective k := hk.bijective_of_nat_card_le (by
    rw [GreenBook.LieModels.UnitaryFour.Extension.binary_extension_card]
    exact hb)
  let fE := MulEquiv.ofBijective f hfB
  let kE := MulEquiv.ofBijective k hkB
  let e := fE.trans kE.symm
  refine ⟨q, e, ?_⟩
  intro g x
  have hh := congrArg (fun a : modelCompletion.pointGraph ≃g modelCompletion.pointGraph => a (q x))
    (kE.apply_symm_apply (fE g))
  change σ (e g) (q x) = q (ρ g (q.symm (q x))) at hh
  simpa only [RelIso.symm_apply_apply, ρ, σ, MulAction.toPermHom_apply,
    MulAction.toPerm_apply] using hh

/-- Aligning an incident flag preserves both original endpoint ranges. -/
theorem exists_range_preserving_equiv_of_diameter (hd : ∀ v w, c.graph.dist v w ≤ 4) :
    ∃ e : G ≃* E,
      c.left.range.map e.toMonoidHom = modelCompletion.left.range ∧
      c.right.range.map e.toMonoidHom = modelCompletion.right.range := by
  obtain ⟨q, e, he⟩ := c.exists_equivariant_native_of_diameter hd
  exact c.exists_range_aligned modelCompletion q e he

/-- The exact marked doubled-unitary recognition consumed by F.5.5(4). -/
theorem exists_parabolic_preserving_equiv_of_diameter (hd : ∀ v w, c.graph.dist v w ≤ 4) :
    ∃ e : G ≃* E,
      c.left.range.map e.toMonoidHom = GreenBook.LieModels.UnitaryFour.Extension.point 1 h1 ∧
      c.right.range.map e.toMonoidHom = GreenBook.LieModels.UnitaryFour.Extension.plane 1 h1 := by
  obtain ⟨e, hl, hr⟩ := c.exists_range_preserving_equiv_of_diameter hd
  refine ⟨e, ?_, ?_⟩
  · exact hl.trans (Subgroup.range_subtype _)
  · exact hr.trans (Subgroup.range_subtype _)

end Completion
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.Extension
