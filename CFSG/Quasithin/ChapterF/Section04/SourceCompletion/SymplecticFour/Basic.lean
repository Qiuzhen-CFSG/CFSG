module
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.Basic
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.Sylow.Parabolics
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.GroupTheory.Amalgam.GeneratedCompletion

/-!
# Genuine extensions of the symplectic flag amalgam

The carrier and all three marked subgroups live in Aut(Sp₄(F)). The inner
intersections are the actual point, plane and flag stabilizers. The global
inner-times-middle factorization implies the two local factorizations and
generation by the endpoints; neither fact is an extra recognition premise.

In characteristic two, conjugation embeds the matrix group as a normal
subgroup with trivial centralizer. Its induced extension action is exactly
the original automorphism, so diagram preservation has its literal meaning.
The inclusion completion has the whole marked overlap. These constructions
retain an arbitrary outer extension and do not identify other completions.

Source: Aschbacher–Smith F.4.3–4, printed p.274 of `refs/quasithin.pdf`.
The small-completion recognition in F.4.8/F.4.17/F.4.24 remains a separate
mathematical obligation.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterF.SourceCompletion.SymplecticFour
variable (F : Type*) [Field F]

abbrev inner : Subgroup (MulAut (Sp F)) := (MulAut.conj : Sp F →* MulAut (Sp F)).range

/-- F.4.3 for the concrete symplectic group and both marked parabolic types. -/
structure SourceExtension where
  carrier : Subgroup (MulAut (Sp F))
  left : Subgroup (MulAut (Sp F))
  right : Subgroup (MulAut (Sp F))
  left_le : left ≤ carrier
  right_le : right ≤ carrier
  contains_inner : inner F ≤ carrier
  preserves_diagram : ∀ a ∈ carrier, DiagramAutomorphisms.PreservesDiagram a
  left_inner : left ⊓ inner F = pointParabolic.map MulAut.conj
  right_inner : right ⊓ inner F = planeParabolic.map MulAut.conj
  factor : ∀ a ∈ carrier, ∃ g : Sp F, ∃ b ∈ left ⊓ right, a = MulAut.conj g * b

namespace SourceExtension
variable {F} (E : SourceExtension F)
abbrev middle : Subgroup (MulAut (Sp F)) := E.left ⊓ E.right

def amalgam : RankTwoAmalgam E.left E.middle E.right :=
  RankTwoAmalgam.ofSubgroups _ _ _ inf_le_left inf_le_right

variable [CharP F 2]
theorem inner_injective : Function.Injective (MulAut.conj : Sp F →* MulAut (Sp F)) :=
  MulAut.conj_injective_of_center_eq_bot EvenProjective.center_eq_bot

theorem middle_inner : E.middle ⊓ inner F = borel.map MulAut.conj := by
  rw [show E.middle ⊓ inner F = (E.left ⊓ inner F) ⊓ (E.right ⊓ inner F) by
    ext a; simp only [middle, mem_inf]; tauto, E.left_inner, E.right_inner,
    ← Subgroup.map_inf _ _ _ (inner_injective (F := F))]
  rfl

omit [CharP F 2] in
theorem inner_le_join : inner F ≤ E.left ⊔ E.right := by
  have hh := congrArg (fun P : Subgroup (Sp F) => P.map (MulAut.conj : Sp F →* MulAut (Sp F)))
    (parabolics_sup_eq_top (F := F))
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, ← E.left_inner, ← E.right_inner] at hh
  change (MulAut.conj : Sp F →* MulAut (Sp F)).range ≤ _
  rw [← hh]
  exact sup_le_sup inf_le_left inf_le_left

omit [CharP F 2] in
theorem generated : E.left ⊔ E.right = E.carrier := by
  refine le_antisymm (sup_le E.left_le E.right_le) ?_
  intro a ha
  obtain ⟨g, b, hb, rfl⟩ := E.factor a ha
  exact (E.left ⊔ E.right).mul_mem (E.inner_le_join ⟨g, rfl⟩) (Subgroup.mem_sup_left hb.1)

omit [CharP F 2] in
theorem left_factor (a : MulAut (Sp F)) (ha : a ∈ E.left) :
    ∃ g ∈ pointParabolic (F := F), ∃ b ∈ E.middle, a = MulAut.conj g * b := by
  obtain ⟨g,b,hb,he⟩ := E.factor a (E.left_le ha)
  have hi : MulAut.conj g ∈ E.left ⊓ inner F := by
    refine ⟨?_, ⟨g,rfl⟩⟩
    change MulAut.conj g ∈ E.left
    have hh := E.left.mul_mem ha (E.left.inv_mem hb.1)
    simpa only [he,mul_inv_cancel_right] using hh
  rw [E.left_inner] at hi
  obtain ⟨x,hx,hxg⟩ := hi
  exact ⟨x,hx,b,hb,by rw [hxg]; exact he⟩

omit [CharP F 2] in
theorem right_factor (a : MulAut (Sp F)) (ha : a ∈ E.right) :
    ∃ g ∈ planeParabolic (F := F), ∃ b ∈ E.middle, a = MulAut.conj g * b := by
  obtain ⟨g,b,hb,he⟩ := E.factor a (E.right_le ha)
  have hi : MulAut.conj g ∈ E.right ⊓ inner F := by
    refine ⟨?_, ⟨g,rfl⟩⟩
    change MulAut.conj g ∈ E.right
    have hh := E.right.mul_mem ha (E.right.inv_mem hb.2)
    simpa only [he,mul_inv_cancel_right] using hh
  rw [E.right_inner] at hi
  obtain ⟨x,hx,hxg⟩ := hi
  exact ⟨x,hx,b,hb,by rw [hxg]; exact he⟩

omit [CharP F 2] in
def modelCompletion : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := E.carrier) where
  left := inclusion E.left_le
  right := inclusion E.right_le
  compatible := rfl
  left_injective := inclusion_injective _
  right_injective := inclusion_injective _
  middle_injective := fun _ _ he => Subtype.ext (congrArg (fun x : E.carrier => x.val) he)
  generated := by
    apply Subgroup.map_injective E.carrier.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_range, MonoidHom.map_range,
      ← MonoidHom.range_eq_map, range_subtype]
    change E.left.subtype.range ⊔ E.right.subtype.range = E.carrier
    rw [range_subtype,range_subtype,E.generated]

omit [CharP F 2] in
@[simp] theorem model_left_range : E.modelCompletion.left.range = E.left.subgroupOf E.carrier :=
  inclusion_range E.left_le
omit [CharP F 2] in
@[simp] theorem model_right_range : E.modelCompletion.right.range = E.right.subgroupOf E.carrier :=
  inclusion_range E.right_le
omit [CharP F 2] in
@[simp] theorem model_middle_range : E.modelCompletion.middle.range = E.middle.subgroupOf E.carrier := by
  exact inclusion_range (inf_le_left.trans E.left_le)

omit [CharP F 2] in
theorem model_overlap : E.modelCompletion.left.range ⊓ E.modelCompletion.right.range =
    E.modelCompletion.middle.range := by
  rw [E.model_left_range,E.model_right_range,E.model_middle_range]
  exact (Subgroup.comap_inf _ _ _).symm

omit [CharP F 2] in
abbrev innerIn : Subgroup E.carrier := (inner F).subgroupOf E.carrier

omit [CharP F 2] in
instance innerIn_normal : E.innerIn.Normal := inferInstance

/-- The actual center-free inner matrix group, inside the extension. -/
def innerEquiv : Sp F ≃* E.innerIn :=
  (MonoidHom.ofInjective (inner_injective (F := F))).trans
    (subgroupOfEquivOfLe E.contains_inner).symm

omit [CharP F 2] in
theorem inner_sup_middle : E.innerIn ⊔ E.modelCompletion.middle.range = ⊤ := by
  apply top_unique
  intro a _
  obtain ⟨g,b,hb,he⟩ := E.factor a.val a.property
  have hg : (⟨MulAut.conj g,E.contains_inner ⟨g,rfl⟩⟩ : E.carrier) ∈ E.innerIn := ⟨g,rfl⟩
  have hb' : (⟨b,E.left_le hb.1⟩ : E.carrier) ∈ E.modelCompletion.middle.range :=
    ⟨⟨b,hb⟩,rfl⟩
  have hh := (E.innerIn ⊔ E.modelCompletion.middle.range).mul_mem
    (Subgroup.mem_sup_left hg) (Subgroup.mem_sup_right hb')
  convert hh using 1
  exact Subtype.ext he

theorem inner_centralizer : centralizer (E.innerIn : Set E.carrier) = ⊥ := by
  apply bot_unique
  intro a ha
  have hh : a.val ∈ centralizer (inner F : Set (MulAut (Sp F))) := by
    intro g hg
    exact congrArg E.carrier.subtype (ha ⟨g,E.contains_inner hg⟩ hg)
  rw [MulAut.centralizer_innerSubgroup_eq_bot EvenProjective.center_eq_bot] at hh
  exact Subtype.ext (show a.val = 1 from hh)

/-- The action induced from the normal copy is the original automorphism. -/
theorem extensionAction_eq (a : E.carrier) :
    DiagramAutomorphisms.extensionAction E.innerIn E.innerEquiv a = a.val := by
  apply MulEquiv.ext
  intro x
  apply inner_injective (F := F)
  have hh := congrArg (fun y : E.carrier => y.val)
    (DiagramAutomorphisms.extensionAction_apply E.innerIn E.innerEquiv a x)
  change MulAut.conj _ = a.val * MulAut.conj x * a.val⁻¹ at hh
  rw [hh]
  ext y
  simp

theorem extensionAction_preservesDiagram (a : E.carrier) :
    DiagramAutomorphisms.PreservesDiagram
      (DiagramAutomorphisms.extensionAction E.innerIn E.innerEquiv a) := by
  rw [E.extensionAction_eq]
  exact E.preserves_diagram a.val a.property
end SourceExtension
end CFSG.Quasithin.ChapterF.SourceCompletion.SymplecticFour
