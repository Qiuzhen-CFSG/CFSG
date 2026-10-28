module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityNonbinary.Geometry
public import Theory.SpecificGroups.Triality.StandardTwoRank.Derived
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.CoreFaithfulness

/-!
# Faithfulness of full binary triality completion actions

The normal core of the extended overlap pulls back into the core-free native
Borel. It therefore meets the inner group trivially and centralizes
it. The centralizer of the inner group in the actual automorphism carrier is
trivial, so the model overlap core vanishes. Normal-core transport through the
marked amalgam gives the result for every faithful completion. Whole overlap
then identifies this core with the kernel of the polygon action.

No finite-order bound, smallness or group recognition premise is used.
Source: Aschbacher–Smith F.3.3–4 and F.4.3–6, printed pp.270–276.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.TrialityNonbinary
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry.RankTwo

open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
variable {m : ℕ} {hm : 0 < m} (E : SourceExtension m hm)

private theorem model_middle_normalCore :
    (E.completion (native_generate m hm)).middle.range.normalCore = ⊥ := by
  let d := E.completion (native_generate m hm)
  let N := d.middle.range.normalCore
  let f := E.baseHom
  let I := (MulAut.innerSubgroup (BinaryCarrier m hm)).subgroupOf E.carrier
  have hrange : f.range = I := by
    ext a
    constructor
    · rintro ⟨b,rfl⟩
      exact ⟨b,rfl⟩
    · rintro ⟨b,hb⟩
      exact ⟨b,Subtype.ext hb⟩
  have hpre : N.comap f ≤ borel (binaryParameters m hm) := by
    intro g hg
    have hl := d.middle_le_left (d.middle.range.normalCore_le hg)
    have hr := d.middle_le_right (d.middle.range.normalCore_le hg)
    obtain ⟨a,ha⟩ := hl
    obtain ⟨b,hb⟩ := hr
    have he : a.val = MulAut.conj g := congrArg Subtype.val ha
    have hf : b.val = MulAut.conj g := congrArg Subtype.val hb
    rw [← parabolic_inf_binary (binaryParameters m hm) rfl]
    exact ⟨(E.conj_mem_left_iff (conj_injective m hm) g).mp (he ▸ a.property),
      (E.conj_mem_right_iff (conj_injective m hm) g).mp (hf ▸ b.property)⟩
  have hp : N.comap f = ⊥ := TwoRank.Derived.normal_eq_bot_of_le_borel m hm _ hpre
  have hdis : N ⊓ I = ⊥ := by
    apply bot_unique
    rintro a ⟨ha,hi⟩
    rw [←hrange] at hi
    obtain ⟨g,rfl⟩ := hi
    have hg : g ∈ N.comap f := ha
    have hg1 : g = 1 := mem_bot.mp (hp.le hg)
    exact mem_bot.mpr (by rw [hg1,map_one])
  have hcent : centralizer (I : Set E.carrier) = ⊥ := by
    apply bot_unique
    intro a ha
    have hh : a.val ∈ centralizer (MulAut.innerSubgroup (BinaryCarrier m hm) : Set (MulAut (BinaryCarrier m hm))) := by
      rintro _ ⟨g,rfl⟩
      exact congrArg Subtype.val (ha (f g) (hrange ▸ (show f g ∈ f.range from ⟨g,rfl⟩)))
    rw [MulAut.centralizer_innerSubgroup_eq_bot (binaryCarrier_center_eq_bot m hm),mem_bot] at hh
    exact mem_bot.mpr (Subtype.ext hh)
  have hc : ⁅N,I⁆ = ⊥ := bot_unique ((commutator_le_inf _ _).trans hdis.le)
  exact bot_unique ((commutator_eq_bot_iff_le_centralizer.mp hc).trans hcent.le)

variable {M : Type*} [Group M] (c : Completion E M)

/-- The marked overlap core is trivial in every faithful completion. -/
theorem completion_middle_normalCore : c.middle.range.normalCore = ⊥ :=
  c.middle_normalCore_eq_bot_of_model (E.completion (native_generate m hm)) (model_middle_normalCore E)

/-- The whole-overlap coset action is faithful, even before smallness. -/
theorem completion_vertex_action_injective
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range) :
    Function.Injective (MulAction.toPermHom M (Vertex c.cosetFamily)) := by
  rw [← MonoidHom.ker_eq_bot_iff, global_kernel]
  change (c.left.range ⊓ c.right.range).normalCore = ⊥
  rw [hoverlap]
  exact completion_middle_normalCore E c

end CFSG.Quasithin.ChapterF.SourceCompletion.TrialityNonbinary
