module

public import Theory.SpecificGroups.ReeTwo.ParabolicConcreteLattice
public import Theory.SpecificGroups.ReeTwo.ParabolicConcreteOrbits
public import Theory.SpecificGroups.ReeTwo.ParabolicConcreteLinear
public import Theory.SpecificGroups.ReeTwo.CoreQuotientCenter

/-!
# The marked centers of the actual Ree and Tits cores

The intrinsic core centers are the source marked involution subgroups.
The Tits-to-Ree embedding preserves every derived coordinate. Its core maps
onto W; a central element of W lies in E and hence centralizes F, so it is
central in W join F = P.

Source: Aschbacher--Smith 14.2.21, printed pp.988--989.
-/

public section

open Subgroup ReeTwo.ParabolicConcrete ReeTwo.Centralizer
open Tits.ExceptionalParabolics
namespace ReeTwo.ParabolicConcrete

private theorem center_map_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (center A).map e.toMonoidHom = center B := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (centerCongr e ⟨a, ha⟩).property
  · intro hb
    exact ⟨e.symm b, (centerCongr e.symm ⟨b,hb⟩).property, e.apply_symm_apply b⟩

theorem ree_center_mark : (center reeQ).map reeQ.subtype =
    zpowers (reeDerivedEmbedding (Multiplicative.ofAdd markedVector)) := by
  rw [← center_map_equiv reeCoreEquiv, map_map,
    ReeTwo.Core.center_eq_zpowers_last_root, MonoidHom.map_zpowers]
  rfl

theorem derived_embedding_compatibility (v : Multiplicative DerivedSpace) :
    FirstQuotient.embedding (titsDerivedEmbedding v) = reeDerivedEmbedding v := by
  exact ReeTwo.ParabolicMarkedComparison.Verified.tits_embedding_commutes (mixedDerivedEmbedding v)

private theorem tits_center_embeds (x : titsQ) (hx : x ∈ center titsQ) :
    FirstQuotient.embedding x ∈ (center reeQ).map reeQ.subtype := by
  let j := FirstQuotient.embedding
  have hxW : j x ∈ reeW := by
    rw [← tits_core_image_eq_W]
    exact mem_map_of_mem _ x.property
  have hcomm (w : FullRee.first) (hw : w ∈ reeW) : w * j x = j x * w := by
    rw [← tits_core_image_eq_W] at hw
    obtain ⟨t, ht, rfl⟩ := hw
    simpa only [Subgroup.coe_mul, map_mul] using
      congrArg (fun a : titsQ => j (a : Tits.ExceptionalParabolics.first))
        (mem_center_iff.mp hx ⟨t, ht⟩)
  have hxE : j x ∈ reeE := by
    have h : (⟨j x, hxW⟩ : reeW) ∈ centralizer (reeE.subgroupOf reeW : Set reeW) := by
      intro y hy
      exact Subtype.ext (hcomm y y.property)
    rw [reeW_centralizer_E] at h
    exact h
  have hjoin : reeW ⊔ reeF ≤ centralizer ({j x} : Set FullRee.first) := by
    apply sup_le
    · intro w hw
      rw [mem_centralizer_singleton_iff]
      exact hcomm w hw
    · intro f hf
      rw [mem_centralizer_singleton_iff]
      exact (hf (j x) hxE).symm
  rw [reeW_sup_F] at hjoin
  refine ⟨⟨j x, reeW_lt_Q.le hxW⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro q
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.mp (hjoin q.property)

theorem tits_center_mark : (center titsQ).map titsQ.subtype =
    zpowers (titsDerivedEmbedding (Multiplicative.ofAdd markedVector)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨x, hx, rfl⟩ := hx
    have h := tits_center_embeds x hx
    rw [ree_center_mark, ← derived_embedding_compatibility,
      ← MonoidHom.map_zpowers] at h
    obtain ⟨y, hy, he⟩ := h
    change (x : Tits.ExceptionalParabolics.first) ∈ _
    rw [← FirstQuotient.embedding_injective he]
    exact hy
  · rw [zpowers_le]
    let x := titsCoreEquiv (ReeTwo.Centralizer.IndexTwo.omegaEquiv
      ReeTwo.Centralizer.mixedCharacter (Or.inr rfl)
      ReeTwo.Centralizer.IndexTwo.omegaLastRoot)
    have hx : x ∈ center titsQ :=
      titsFiveFixed_le_center (titsFiveFixed_eq ▸ mem_zpowers x)
    refine ⟨x, hx, ?_⟩
    apply Subtype.ext
    exact titsFiveFixed_generator_mark.trans titsDerivedEmbedding_mark.symm
end ReeTwo.ParabolicConcrete
