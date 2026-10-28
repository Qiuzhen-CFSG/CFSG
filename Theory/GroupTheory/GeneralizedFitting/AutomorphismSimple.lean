module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# Components of the automorphism group of a centerless simple group

A component of Aut(G) either lies in Inn(G) or centralizes it. The latter
case is impossible because Inn(G) has trivial centralizer. In the former
case, simplicity identifies the nontrivial subnormal subgroup with Inn(G).
Conjugation then gives an actual isomorphism with G.

This is the elementary component calculation used for the Aut(L₃(2))
centralizer in Aschbacher--Smith 16.1.7(g), printed p.1172.
-/

public section
namespace Theory.GroupTheory
open Subgroup
variable {G : Type*} [Group G] [IsSimpleGroup G]

/-- Every component of Aut(G) is the actual subgroup of inner automorphisms. -/
theorem IsComponent.eq_innerSubgroup {K : Subgroup (MulAut G)}
    (hK : IsComponent (MulAut G) K) (hc : center G = ⊥) :
    K = MulAut.innerSubgroup G := by
  let := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  have hKne : K ≠ ⊥ := (nontrivial_iff_ne_bot K).mp inferInstance
  let e : G ≃* MulAut.innerSubgroup G :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hc)
  let : IsSimpleGroup (MulAut.innerSubgroup G) := e.symm.isSimpleGroup
  have hle : K ≤ MulAut.innerSubgroup G := by
    rcases hK.normal_dichotomy (MulAut.innerSubgroup G) with h | h
    · exact h
    · have hb := commutator_eq_bot_iff_le_centralizer.mp h
      rw [MulAut.centralizer_innerSubgroup_eq_bot hc] at hb
      exact (hKne (le_bot_iff.mp hb)).elim
  rcases hK.1.subgroupOf.eq_bot_or_top_of_isSimpleGroup
      (inferInstance : IsSimpleGroup (MulAut.innerSubgroup G)) with hb | ht
  · have h := congrArg (Subgroup.map (MulAut.innerSubgroup G).subtype) hb
    rw [map_subgroupOf_eq_of_le hle, Subgroup.map_bot] at h
    exact (hKne h).elim
  · exact le_antisymm hle (subgroupOf_eq_top.mp ht)

/-- The component is isomorphic to G, via the actual inner action. -/
theorem IsComponent.equiv_simple_of_automorphism {K : Subgroup (MulAut G)}
    (hK : IsComponent (MulAut G) K) (hc : center G = ⊥) : Nonempty (K ≃* G) :=
  ⟨(MulEquiv.subgroupCongr (hK.eq_innerSubgroup hc)).trans
    (MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hc)).symm⟩

end Theory.GroupTheory
