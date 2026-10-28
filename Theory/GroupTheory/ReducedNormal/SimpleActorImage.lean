module
public import Theory.GroupTheory.ReducedNormal.Defs
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Theory.GroupTheory.Commutator.NormalGeneration

/-!
# The faithful image of a simple quotient actor

A normal actor with simple quotient by its two-core acts on a reduced normal
subgroup either trivially or faithfully modulo that core. Full movement of a
nonzero subgroup excludes the trivial image. The resulting equivalence retains
the original centralizer quotient map.

This is the actor identification used in Aschbacher--Smith 13.7.4(1), p.937.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]
theorem reduced_simple_actor_image
    (U K : Subgroup G) [U.Normal] [K.Normal]
    (hU : IsPReduced 2 U) (hs : IsSimpleGroup (K ⧸ pCore 2 K))
    (hne : U ≠ ⊥) (hm : ⁅U,K⁆ = U) :
    Nonempty ((K ⧸ pCore 2 K) ≃* K.map (QuotientGroup.mk' (centralizer (U : Set G)))) := by
  let q := QuotientGroup.mk' (centralizer (U : Set G))
  let f := q.subgroupMap K
  have hcore : pCore 2 K ≤ f.ker := by
    have hn : ((pCore 2 K).map K.subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal
    have hmap : (pCore 2 K).map K.subtype ≤ pCore 2 G :=
      le_sSup ⟨hn,pCore_isPGroup.map K.subtype⟩
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    intro k hk
    exact le_centralizer_iff.mp hU.le_centralizer_pCore (hmap (mem_map_of_mem _ hk))
  let φ : (K ⧸ pCore 2 K) →* K.map q := QuotientGroup.lift (pCore 2 K) f hcore
  let := hs
  have hsurj : Function.Surjective φ := by
    intro c
    obtain ⟨k,hk⟩ := q.subgroupMap_surjective K c
    exact ⟨QuotientGroup.mk' (pCore 2 K) k,hk⟩
  have hinj : Function.Injective φ := by
    apply φ.ker_eq_bot_iff.mp
    rcases φ.normal_ker.eq_bot_or_eq_top with hb | ht
    · exact hb
    · exfalso
      have hφ : φ = 1 := φ.ker_eq_top_iff.mp ht
      have hkill : K ≤ centralizer (U : Set G) := by
        intro k hk
        have he : φ (QuotientGroup.mk' (pCore 2 K) ⟨k,hk⟩) = 1 := by rw [hφ];rfl
        have he' : q k=1 := congrArg Subtype.val he
        exact (QuotientGroup.eq_one_iff _).mp he'
      apply hne
      rw [←hm,commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr hkill
  exact ⟨MulEquiv.ofBijective φ ⟨hinj,hsurj⟩⟩
end Theory.GroupTheory

