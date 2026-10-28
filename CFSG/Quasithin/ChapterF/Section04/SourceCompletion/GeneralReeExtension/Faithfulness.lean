module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeExtension.Geometry
public import Theory.SpecificGroups.ReeF4.SmallCompletion.CoreFree
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.CoreFaithfulness

/-!
# Faithfulness of full general Ree completion actions

The normal core of the extended overlap pulls back into the core-free native
linear parabolic. It therefore meets the inner group trivially and centralizes
it. The centralizer of the inner group in the actual automorphism carrier is
trivial, so the model overlap core vanishes. Normal-core transport through the
marked amalgam gives the result for every faithful completion. Whole overlap
then identifies this core with the kernel of the polygon action.

No finite-order bound, smallness or group recognition premise is used.
Source: Aschbacher–Smith F.3.3–4 and F.4.3–6, printed pp.270–276.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeExtension
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry.RankTwo

private theorem native_generate (m : ℕ) :
    ReeF4.Parabolics.parabolic m .linear ⊔ ReeF4.Parabolics.parabolic m .suzuki = ⊤ := by
  rw [sup_comm]
  exact GreenBook.LieModels.ReeFour.parabolics_generate m

variable {m : ℕ} (E : SourceExtension m)

private theorem model_middle_normalCore (hm : 0 < m) :
    (E.completion (native_generate m)).middle.range.normalCore = ⊥ := by
  let d := E.completion (native_generate m)
  let N := d.middle.range.normalCore
  let f := E.baseHom
  let I := (MulAut.innerSubgroup (ReeF4.Model m)).subgroupOf E.carrier
  have hrange : f.range = I := by
    ext a
    constructor
    · rintro ⟨b,rfl⟩
      exact ⟨b,rfl⟩
    · rintro ⟨b,hb⟩
      exact ⟨b,Subtype.ext hb⟩
  have hpre : N.comap f ≤ ReeF4.Parabolics.parabolic m .linear := by
    intro g hg
    have hl := d.middle_le_left (d.middle.range.normalCore_le hg)
    obtain ⟨a,ha⟩ := hl
    have he : a.val = MulAut.conj g := congrArg Subtype.val ha
    apply (E.conj_mem_left_iff (ReeF4.SmallCompletion.conj_injective m hm) g).mp
    exact he ▸ a.property
  have hp : N.comap f = ⊥ := bot_unique
    ((normal_le_normalCore.mpr hpre).trans (ReeF4.SmallCompletion.linear_normalCore_eq_bot m hm).le)
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
    have hh : a.val ∈ centralizer (MulAut.innerSubgroup (ReeF4.Model m) : Set (MulAut (ReeF4.Model m))) := by
      rintro _ ⟨g,rfl⟩
      exact congrArg Subtype.val (ha (f g) (hrange ▸ (show f g ∈ f.range from ⟨g,rfl⟩)))
    rw [MulAut.centralizer_innerSubgroup_eq_bot (ReeF4.SmallCompletion.center_eq_bot m hm),mem_bot] at hh
    exact mem_bot.mpr (Subtype.ext hh)
  have hc : ⁅N,I⁆ = ⊥ := bot_unique ((commutator_le_inf _ _).trans hdis.le)
  exact bot_unique ((commutator_eq_bot_iff_le_centralizer.mp hc).trans hcent.le)

variable {M : Type*} [Group M] (c : Completion E M)

/-- The marked overlap core is trivial in every faithful completion. -/
theorem completion_middle_normalCore (hm : 0 < m) : c.middle.range.normalCore = ⊥ :=
  c.middle_normalCore_eq_bot_of_model (E.completion (native_generate m)) (model_middle_normalCore E hm)

/-- The whole-overlap coset action is faithful, even before smallness. -/
theorem completion_vertex_action_injective (hm : 0 < m)
    (hoverlap : c.left.range ⊓ c.right.range = c.middle.range) :
    Function.Injective (MulAction.toPermHom M (Vertex c.cosetFamily)) := by
  rw [← MonoidHom.ker_eq_bot_iff, global_kernel]
  change (c.left.range ⊓ c.right.range).normalCore = ⊥
  rw [hoverlap]
  exact completion_middle_normalCore E c hm

end CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeExtension
