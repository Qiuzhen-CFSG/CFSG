module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.SymplecticFour.Cartan
public import Theory.SpecificGroups.SymplecticFour.Sylow.CoreFree
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.CoreFaithfulness
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.OverlapCover

/-!
# Faithful path actions of symplectic extension completions

A normal subgroup of the extended flag stabilizer pulls back to a normal
subgroup of the native Borel, whose core is trivial. It therefore meets the
normal inner group trivially, hence centralizes it and is trivial. Transport
through the faithful amalgam maps gives trivial middle core in every
completion. With whole overlap this is the kernel of the coset-graph action.

The universal common cover also transports rooted nonbacktracking path
transitivity from the extended model. The native five-path transitivity,
order-to-smallness argument and geometric identification remain to be proved.

Source: Aschbacher–Smith F.3.3–4 and F.4.3–6, printed pp.270–276 of
`refs/quasithin.pdf`. The literal Chapter6/12 applications use these kernel
facts for the original pair of full normalizers.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterF.SourceCompletion.SymplecticFour
variable {F : Type*} [Field F] [CharP F 2] [Finite F]
namespace SourceExtension
variable (E : SourceExtension F)

/-- A normal subgroup inside the extended Borel meets the inner copy
trivially and therefore centralizes it; faithfulness of the extension kills it. -/
theorem model_middle_normalCore : E.modelCompletion.middle.range.normalCore = ⊥ := by
  let N := E.modelCompletion.middle.range.normalCore
  let f : Sp F →* E.carrier := E.innerIn.subtype.comp E.innerEquiv.toMonoidHom
  have hpre : N.comap f ≤ borel := by
    intro g hg
    have hm := E.modelCompletion.middle.range.normalCore_le hg
    rw [E.model_middle_range] at hm
    have hgi : MulAut.conj g ∈ E.middle ⊓ inner F := ⟨hm,⟨g,rfl⟩⟩
    rw [E.middle_inner] at hgi
    obtain ⟨b,hb,he⟩ := hgi
    exact inner_injective (F := F) he ▸ hb
  have hp : N.comap f = ⊥ := by
    apply bot_unique
    exact (normal_le_normalCore.mpr hpre).trans borel_normalCore_eq_bot.le
  have hdis : N ⊓ E.innerIn = ⊥ := by
    apply bot_unique
    rintro a ⟨ha,hi⟩
    obtain ⟨g,hg⟩ := E.innerEquiv.surjective ⟨a,hi⟩
    have hfg : f g = a := congrArg Subtype.val hg
    have hgm : g ∈ N.comap f := by change f g ∈ N; rwa [hfg]
    have hg1 : g = 1 := mem_bot.mp (hp.le hgm)
    exact mem_bot.mpr (by rw [←hfg,hg1,map_one])
  have hc : ⁅N,E.innerIn⁆ = ⊥ := bot_unique ((commutator_le_inf _ _).trans hdis.le)
  exact bot_unique ((commutator_eq_bot_iff_le_centralizer.mp hc).trans E.inner_centralizer.le)
end SourceExtension

namespace Completion
variable {E : SourceExtension F} {M : Type*} [Group M] (c : Completion E M)

theorem middle_normalCore : c.middle.range.normalCore = ⊥ :=
  c.middle_normalCore_eq_bot_of_model E.modelCompletion E.model_middle_normalCore

theorem vertex_action_injective (hoverlap : c.left.range ⊓ c.right.range = c.middle.range) :
    Function.Injective (MulAction.toPermHom M (Subgroup.CosetGeometry.RankTwo.Vertex c.cosetFamily)) := by
  rw [←MonoidHom.ker_eq_bot_iff,Subgroup.CosetGeometry.RankTwo.global_kernel]
  change (c.left.range ⊓ c.right.range).normalCore = ⊥
  rw [hoverlap]
  exact c.middle_normalCore

omit [CharP F 2] [Finite F] in
/-- Rooted path actions transfer from the actual extended model to any
completion with the same whole overlap. Native five-path transitivity is
still a separate theorem to establish. -/
theorem rootPathTransitive_iff (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
    (i : Bool) (k : ℕ) :
    SimpleGraph.PathTransitivePolygon.RootPathTransitive
      (Subgroup.CosetGeometry.RankTwo.graph E.modelCompletion.cosetFamily) E.carrier
      (Subgroup.CosetGeometry.RankTwo.base E.modelCompletion.cosetFamily i) k ↔
    SimpleGraph.PathTransitivePolygon.RootPathTransitive
      (Subgroup.CosetGeometry.RankTwo.graph c.cosetFamily) M
      (Subgroup.CosetGeometry.RankTwo.base c.cosetFamily i) k :=
  RankTwoAmalgam.Universal.rootPathTransitive_iff_of_overlap E.amalgam
    E.modelCompletion c E.model_overlap hoverlap i k
end Completion
end CFSG.Quasithin.ChapterF.SourceCompletion.SymplecticFour
