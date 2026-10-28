module

public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.Faithfulness
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.ExtensionQuadrangle
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourExtension.PlaneAction
public import Theory.Combinatorics.SimpleGraph.QuadrangleCollinearity.Basic

/-!
# Faithful point action of a doubled binary unitary completion

The ordinary projective subgroup acts faithfully on the model's coset graph,
transported through the actual ordinary-to-extended graph isomorphism. An
extended kernel element fixes the base plane and centralizes its ordinary
plane subgroup. The proved faithful plane conjugation action kills it.

The common amalgam cover transfers vertex faithfulness to every original
completion. Girth eight then makes an element fixing all plane cosets fix
every remaining vertex as well. Thus the original point action is faithful,
without assuming the eventual group recognition.

Source: Aschbacher--Smith F.4.26 and F.5.5(4), printed pp.288 and302.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.Extension
open Theory.GroupTheory
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
open GreenBook.LieModels.UnitaryFour
local notation "h1" => (Nat.le_refl 1)
local notation "P" => ProjectiveGroup 1 h1
local notation "E" => GreenBook.LieModels.UnitaryFour.Extension.ProjectiveExtension 1 h1
local notation "inl" => (SemidirectProduct.inl : P →* E)

/-- The ordinary model has the exact family used by the graph transport. -/
theorem ordinary_family_eq : SourceCompletion.UnitaryTwo.modelCompletion.family = ExtensionFive.AP := by
  funext j
  cases j
  · exact RankTwoAmalgam.FaithfulCompletion.ofSubgroups_left_range _ _ _ _ _ _
  · exact RankTwoAmalgam.FaithfulCompletion.ofSubgroups_right_range _ _ _ _ _ _

/-- The extended model has the exact family used by the graph transport. -/
theorem model_family_eq : modelCompletion.family = ExtensionFive.AE := by
  funext j
  cases j
  · exact RankTwoAmalgam.FaithfulCompletion.ofSubgroups_left_range _ _ _ _ _ _
  · exact RankTwoAmalgam.FaithfulCompletion.ofSubgroups_right_range _ _ _ _ _ _

private theorem inl_vertex_action_injective :
    Function.Injective ((MulAction.toPermHom E (Subgroup.CosetGeometry.Vertex ExtensionFive.AE)).comp inl) := by
  have hi : Function.Injective (MulAction.toPermHom P (Subgroup.CosetGeometry.Vertex ExtensionFive.AP)) :=
    ordinary_family_eq ▸ SourceCompletion.UnitaryTwo.native_vertex_action_injective
  intro a b hab
  apply hi
  apply Equiv.Perm.ext
  intro v
  apply ExtensionFive.vertexMap_injective
  change ExtensionFive.vertexMap (a • v) = ExtensionFive.vertexMap (b • v)
  rw [ExtensionFive.vertexMap_smul, ExtensionFive.vertexMap_smul]
  exact Equiv.Perm.ext_iff.mp hab (ExtensionFive.vertexMap v)

/-- The full doubled model acts faithfully on its literal coset vertices. -/
theorem native_vertex_action_injective :
    Function.Injective (MulAction.toPermHom E modelCompletion.Vertex) := by
  have hi : Function.Injective (MulAction.toPermHom E (Subgroup.CosetGeometry.Vertex ExtensionFive.AE)) := by
    let ρ := MulAction.toPermHom E (Subgroup.CosetGeometry.Vertex ExtensionFive.AE)
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm _ bot_le
    intro g hg
    change g = 1
    have hρ : ρ g = 1 := hg
    have hgP : g ∈ GreenBook.LieModels.UnitaryFour.Extension.plane 1 h1 := by
      have hh := Equiv.Perm.ext_iff.mp hρ (RankTwo.base ExtensionFive.AE true)
      change g ∈ stabilizer ExtensionFive.AE (RankTwo.base ExtensionFive.AE true) at hh
      simpa only [stabilizer, RankTwo.base, stabilizer_base, ExtensionFive.AE, ↓reduceIte] using hh
    let gP : GreenBook.LieModels.UnitaryFour.Extension.plane 1 h1 := ⟨g, hgP⟩
    have he : GreenBook.LieModels.UnitaryFour.Extension.binaryPlaneConjugation gP = 1 := by
      apply MulEquiv.ext
      intro y
      apply Subtype.ext
      apply inl_vertex_action_injective
      change ρ (inl (GreenBook.LieModels.UnitaryFour.Extension.binaryPlaneConjugation gP y).val) =
        ρ (inl y.val)
      have hh := congrArg Subtype.val
        (GreenBook.LieModels.UnitaryFour.Extension.binaryPlaneConjugation_conj gP y)
      change inl (GreenBook.LieModels.UnitaryFour.Extension.binaryPlaneConjugation gP y).val =
        g * inl y.val * g⁻¹ at hh
      simp only [hh, map_mul, map_inv, hρ, one_mul, inv_one, mul_one]
    have hgP1 : gP = 1 := GreenBook.LieModels.UnitaryFour.Extension.binaryPlaneConjugation_injective
      (he.trans (map_one _).symm)
    exact congrArg Subtype.val hgP1
  change Function.Injective (MulAction.toPermHom E (Subgroup.CosetGeometry.Vertex modelCompletion.family))
  rw [model_family_eq]
  exact hi

/-- Common-cover transport retains faithfulness for every original completion. -/
theorem Completion.vertex_action_injective {G : Type*} [Group G] (c : Completion G) :
    Function.Injective (MulAction.toPermHom G c.Vertex) := by
  have hgcd : (Nat.card (GreenBook.LieModels.UnitaryFour.Extension.point 1 h1)).gcd
      (Nat.card (GreenBook.LieModels.UnitaryFour.Extension.plane 1 h1)) =
      Nat.card (GreenBook.LieModels.UnitaryFour.Extension.overlap 1 h1) := by
    rw [GreenBook.LieModels.UnitaryFour.Extension.binary_point_card,
      GreenBook.LieModels.UnitaryFour.Extension.binary_plane_card,
      GreenBook.LieModels.UnitaryFour.Extension.binary_overlap_card]
    norm_num
  exact (RankTwoAmalgam.Universal.coverData
    (GreenBook.LieModels.UnitaryFour.Extension.amalgam 1 h1) hgcd c).injective_action_transfer
    (RankTwoAmalgam.Universal.coverData
      (GreenBook.LieModels.UnitaryFour.Extension.amalgam 1 h1) hgcd modelCompletion)
    (RankTwo.base (RankTwoAmalgam.Universal.cosetFamily
      (GreenBook.LieModels.UnitaryFour.Extension.amalgam 1 h1)) false)
    modelCompletion.connected native_vertex_action_injective

namespace Completion
open SimpleGraph.QuadrangleCollinearity
variable {G : Type*} [Group G] [Finite G] (c : Completion G)

/-- The actual plane-coset action is faithful. -/
theorem point_action_injective : Function.Injective (MulAction.toPermHom G c.Point) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm _ bot_le
  intro g hg
  change g = 1
  apply c.vertex_action_injective
  apply Equiv.Perm.ext
  intro v
  change g • v = (1 : G) • v
  rw [one_smul]
  have hfix (x : c.Point) : g • x.val = x.val :=
    congrArg Subtype.val (Equiv.Perm.ext_iff.mp hg x)
  cases hv : v.type
  · obtain ⟨a, ha, _⟩ := c.hasTwoNeighbors v v
    obtain ⟨b, hb, hba⟩ := c.hasTwoNeighbors v a
    have hta : a.type = true := by simpa [hv] using c.adjacency_flip ha
    have htb : b.type = true := by simpa [hv] using c.adjacency_flip hb
    have hga := hfix ⟨a, hta⟩
    have hgb := hfix ⟨b, htb⟩
    exact common_vertex_unique c.cycle_length_ge_eight hba.symm
      (by simpa only [hga] using c.graphAction.map_adj g ha.symm)
      (by simpa only [hgb] using c.graphAction.map_adj g hb.symm) ha.symm hb.symm
  · exact hfix ⟨v, hv⟩

end Completion
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo.Extension
