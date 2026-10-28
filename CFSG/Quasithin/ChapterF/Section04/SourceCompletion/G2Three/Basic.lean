module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.G2
public import Theory.AtlasPort.LinearGroups.G2.LieParabolicCells
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.CoreFaithfulness
public import Theory.GroupAction.RankTwoCosetGeometry

/-!
# Whole overlap and faithful action of ternary G₂ completions

These are the actual two root parabolics over ZMod 3, with their entire Borel
as marked middle. The native singular-point action has trivial kernel, so
transport of normal subgroups through the compatible amalgam maps kills the
marked middle core in every completion.

Maximality of the Borel in the long endpoint leaves only the intended overlap
or containment of the long endpoint in the short one. The two-cell size bound
then identifies the endpoints in the latter case. Generation would make the
whole group an endpoint, acting faithfully on four Borel cosets, contradicting
its order 11664. Thus the whole overlap is the marked middle, and the action
on the typed coset graph is faithful. Ambient finiteness is not required.

This proves the local and kernel inputs to Aschbacher–Smith F.4.6(1), printed
pp.276–277. The involution smallness and geometry comparison needed for F.4.26,
printed p.288, remain separate obligations; no recognition theorem is asserted.
The octonion coordinates retain the ATLAS license in LICENSES/ATLAS.txt.
-/

@[expose] public section

open Subgroup Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
open Subgroup.CosetGeometry
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.G2Three

abbrev Completion (G : Type*) [Group G] :=
  RankTwoAmalgam.FaithfulCompletion (GreenBook.LieModels.G2.amalgam (F := ZMod 3)) (G := G)

def modelCompletion : Completion (Model (ZMod 3)) :=
  RankTwoAmalgam.FaithfulCompletion.ofSubgroups
    parabolic₁ (parabolic₁ ⊓ parabolic₂) parabolic₂ inf_le_left inf_le_right
    parabolics_generate

@[simp] theorem model_left_range : modelCompletion.left.range = parabolic₁ := range_subtype _
@[simp] theorem model_right_range : modelCompletion.right.range = parabolic₂ := range_subtype _
@[simp] theorem model_middle_range : modelCompletion.middle.range = borel := by
  change (parabolic₁ (F := ZMod 3) ⊓ parabolic₂).subtype.range = _
  rw [range_subtype,parabolics_intersection]

theorem model_overlap : modelCompletion.left.range ⊓ modelCompletion.right.range =
    modelCompletion.middle.range := by
  rw [model_left_range,model_right_range,model_middle_range,parabolics_intersection]

theorem model_middle_normalCore : modelCompletion.middle.range.normalCore = ⊥ := by
  rw [model_middle_range]
  exact ParabolicCells.borel_core

namespace Completion
variable {G : Type*} [Group G] (c : Completion G)

def family : Bool → Subgroup G := fun i => bif i then c.right.range else c.left.range
abbrev Vertex := RankTwo.Vertex c.family
abbrev graph := RankTwo.graph c.family
@[simp] theorem family_false : c.family false = c.left.range := rfl
@[simp] theorem family_true : c.family true = c.right.range := rfl

theorem connected : c.graph.Connected := RankTwo.connected c.family c.generated

theorem middle_card : Nat.card c.middle.range = 2916 := by
  rw [RankTwoAmalgam.FaithfulCompletion.middle_card]
  change Nat.card (GreenBook.LieModels.G2.overlap (F := ZMod 3)) = _
  rw [GreenBook.LieModels.G2.overlap_eq_borel,card_borel]
  norm_num [Nat.card_eq_fintype_card]

theorem right_card : Nat.card c.right.range = 11664 := by
  rw [RankTwoAmalgam.FaithfulCompletion.right_card,card_parabolic]
  norm_num [Nat.card_eq_fintype_card]

theorem left_card_le : Nat.card c.left.range ≤ 11664 := by
  rw [RankTwoAmalgam.FaithfulCompletion.left_card]
  have h := ParabolicCells.short_card_le (F := ZMod 3)
  rw [card_borel] at h
  norm_num [Nat.card_eq_fintype_card] at h ⊢
  exact h

theorem middle_normalCore : c.middle.range.normalCore = ⊥ :=
  c.middle_normalCore_eq_bot_of_model modelCompletion model_middle_normalCore

theorem right_mem_middle_iff (r : parabolic₂ (F := ZMod 3)) :
    c.right r ∈ c.middle.range ↔ r.val ∈ borel := by
  constructor
  · rintro ⟨b,hb⟩
    have he : (GreenBook.LieModels.G2.amalgam (F := ZMod 3)).right b = r := by
      apply c.right_injective
      exact (DFunLike.congr_fun c.compatible b).symm.trans hb
    have hb' : b.val ∈ borel := GreenBook.LieModels.G2.overlap_eq_borel.le b.property
    rw [←he]
    change b.val ∈ borel
    exact hb'
  · intro hr
    let b : GreenBook.LieModels.G2.overlap (F := ZMod 3) :=
      ⟨r.val,GreenBook.LieModels.G2.overlap_eq_borel.ge hr⟩
    exact ⟨b,DFunLike.congr_fun c.compatible b⟩

/-- The intersection of endpoint images is the whole marked Borel. -/
theorem overlap : c.left.range ⊓ c.right.range = c.middle.range := by
  let P := parabolic₂ (F := ZMod 3)
  let H : Subgroup (Model (ZMod 3)) := (c.left.range.comap c.right).map P.subtype
  have hB : borel ≤ H := by
    intro b hb
    let r : P := ⟨b,borel_le_parabolic₂ hb⟩
    exact ⟨r,c.middle_le_left ((c.right_mem_middle_iff r).mpr hb),rfl⟩
  have hP : H ≤ parabolic₂ := by
    exact (map_le_range _ _).trans (range_subtype P).le
  rcases ParabolicCells.long_maximal H hB hP with h | h
  · apply le_antisymm _ (le_inf c.middle_le_left c.middle_le_right)
    rintro g ⟨hl,r,hr⟩
    rw [←hr]
    apply (c.right_mem_middle_iff r).mpr
    exact h.le ⟨r,by change c.right r ∈ c.left.range; rwa [hr],rfl⟩
  · have hRL : c.right.range ≤ c.left.range := by
      rintro g ⟨r,rfl⟩
      have hr : r.val ∈ H := h.ge r.property
      obtain ⟨r',hr',he⟩ := hr
      have he' : r'=r := Subtype.ext he
      exact he' ▸ hr'
    let : Finite c.left.range := Finite.of_equiv (parabolic₁ (F := ZMod 3))
      (MonoidHom.ofInjective c.left_injective).toEquiv
    have he : c.right.range = c.left.range := eq_of_le_of_card_ge hRL
      (by rw [c.right_card]; exact c.left_card_le)
    have htop : c.right.range = ⊤ := by simpa only [←he,sup_idem] using c.generated
    have hcG : Nat.card G = 11664 := by simpa only [htop,card_top] using c.right_card
    let : Finite G := Nat.finite_of_card_ne_zero (by rw [hcG]; decide)
    have hi : c.middle.range.index = 4 := by
      have hh := c.middle.range.card_mul_index
      rw [c.middle_card,hcG] at hh
      omega
    have hf : Function.Injective (MulAction.toPermHom G (G ⧸ c.middle.range)) := by
      rw [←MonoidHom.ker_eq_bot_iff,←normalCore_eq_ker]
      exact c.middle_normalCore
    have hb := Nat.card_le_card_of_injective _ hf
    rw [hcG,Nat.card_perm,←index_eq_card,hi] at hb
    norm_num at hb

/-- The literal coset graph has faithful ambient action. -/
theorem vertex_action_injective : Function.Injective (MulAction.toPermHom G c.Vertex) := by
  rw [←MonoidHom.ker_eq_bot_iff,RankTwo.global_kernel]
  change (c.left.range ⊓ c.right.range).normalCore = ⊥
  rw [c.overlap]
  exact c.middle_normalCore

end Completion
end CFSG.Quasithin.ChapterF.SourceCompletion.G2Three
