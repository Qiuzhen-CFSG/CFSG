module

public import CFSG.Quasithin.ChapterD.Section03.InternalOddImage
public import Theory.Representation.BinaryOffender.Homogeneous.FaithfulOrbit

/-!
# The literal actor image of the internal orbit module

The action-image two-core hypothesis kills O₂(X) on the original module,
and therefore on the actual orbit span. The nonzero Irr⁺ seed makes the
image of X nontrivial. Killing the intrinsic two-cores changes each
surviving C-component into an ordinary component; the odd-prime branch
uses the equivariant Frattini-quotient map. Thus both original internal
alternatives give precisely the alternatives of D.3.1.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma D.3.3, printed p.193.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.ChapterD.Section03
universe u v w
variable {G : Type u} [Group G] [Finite G]
  {H : Type w} [Group H]

/-- The ordinary component alternative after killing the actor's two-core. -/
theorem component_internal_actor_image
    {T : Sylow 2 G} {X L : Subgroup G} (hL : L.IsCComponent)
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) (hX : X = componentOrbit L (T : Subgroup G))
    (f : G →* H) (hf : Function.Surjective f) (hk : X.pCoreIn 2 ≤ f.ker)
    (hne : X.map f ≠ ⊥) :
    ∃ B : Subgroup H, IsComponent H B ∧
      X.map f = componentOrbit B (T.mapSurjective hf : Subgroup H) := by
  have hLX : L ≤ X := by
    rw [hX]
    exact le_componentOrbit L T
  have hLk : L.pCoreIn 2 ≤ f.ker :=
    (pCoreAmbient_mono_of_isSubnormalIn L X 2 hLX hL.subnormal.subgroupOf).trans hk
  have hLn : L.map f ≠ ⊥ := componentOrbit_map_seed_ne_bot L T f (by rwa [← hX])
  exact ⟨L.map f, hL.isComponent_map_of_twoCore_killed hq f hf hLk hLn,
    by rw [hX, map_componentOrbit]; rfl⟩

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : GroupClass.{u}}
  {T : Sylow 2 G} {X : Subgroup G} {I : Submodule (ZMod 2) V}

/-- The reduced actor action kills its original intrinsic two-core. -/
theorem InternalModuleHypotheses.actorCore_fixes
    (h : InternalModuleHypotheses K ρ T X I) (x : X) (hx : x ∈ pCore 2 X) (v : V) :
    ρ x v = v := by
  let a := actionHom (ρ.comp X.subtype)
  have hm : (pCore 2 X).map a ≤ pCore 2 (actionImage (ρ.comp X.subtype)) :=
    le_sSup ⟨Normal.map inferInstance a
      (Representation.asGroupHom (ρ.comp X.subtype)).rangeRestrict_surjective,
      pCore_isPGroup.map a⟩
  have he : a x = 1 := mem_bot.mp (h.actorCore ▸ hm (mem_map_of_mem a hx))
  exact (actionHom_eq_one_iff (ρ.comp X.subtype) x).mp he v

/-- The two-core is killed by the specified action map on the orbit span. -/
theorem InternalModuleHypotheses.orbitMap_kills_core
    (h : InternalModuleHypotheses K ρ T X I) :
    X.pCoreIn 2 ≤ (invariantActionHom ρ (orbitSpan ρ ⊤ I)
      (orbitSpan_invariant ρ ⊤ I)).ker := by
  rw [invariantActionHom_ker]
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨mem_top _, fun v _ => h.actorCore_fixes x hx v⟩

/-- The image actor is nontrivial because the actual seed has nontrivial action. -/
theorem InternalModuleHypotheses.orbit_actor_ne_bot
    (h : InternalModuleHypotheses K ρ T X I) :
    restrictedSubgroup ρ (orbitSpan ρ ⊤ I) X ≠ ⊥ := by
  intro he
  have hs := (isIrrPlus_faithfulOrbit ρ h.seed).not_le_fixedSpace
    (subspaceImageRepresentation ρ (orbitSpan ρ ⊤ I))
  rw [he, fixedSpace_bot] at hs
  exact hs le_top

end CFSG.Quasithin.ChapterD.Section03
