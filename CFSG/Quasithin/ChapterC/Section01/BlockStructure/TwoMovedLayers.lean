module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.NormalizedTwoGroups
public import Theory.GroupTheory.PCoreSurjective

/-!
# Two moved layers exclude a short group

Suppose a two-subgroup U and K normalize each other. Nontrivial action
on U forces the entire short commutator layer of K into U. A surjective
map killing U, with two-group kernel, must therefore have central two-core.
A noncentral two-core in that image contradicts shortness.

This separates the lower and upper layers in Aschbacher--Smith 15.1.29,
printed pp.1103--1104, using the short-layer dichotomy of C.1.7--11.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

/-- The two noncentral layers obstruct a short group. Movement on the
normal two-subgroup U forces the entire short layer into U; a quotient
killing U would then have central two-core. -/
theorem not_short_of_two_moved_layers (K U : Subgroup G)
    (hU : IsPGroup 2 U) (hKU : K ≤ normalizer (U : Set G))
    (hUK : U ≤ normalizer (K : Set G)) (hmoved : ¬ U ≤ centralizer (K : Set G))
    (f : K →* H) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hkill : ∀ x : K, (x : G) ∈ U → f x = 1)
    (hupper : ¬ pCore 2 H ≤ center H) : ¬ IsShort K := by
  intro hs
  have hBU : (blockU K).map K.subtype ≤ U :=
    (hs.blockU_le_or_centralizes_of_normalizing_twoGroup hU hKU hUK).resolve_right hmoved
  have hb : (blockU K).map f = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro x hx
    exact hkill x (hBU (mem_map_of_mem K.subtype hx))
  apply hupper
  apply commutator_top_right_eq_bot_iff_le_center.mp
  have hcore : (pCore 2 K).map f = pCore 2 H := by
    rw [←f.comap_pCore_of_ker_isPGroup hf hk]
    exact map_comap_eq_self_of_surjective hf _
  rw [blockU,map_commutator,hcore,map_top_of_surjective f hf] at hb
  exact hb
end CFSG.Quasithin.ChapterC
