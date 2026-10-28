module
public import Theory.GroupTheory.ReducedNormal.Defs
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Subnormal images on reduced normal subgroups

On a p-reduced normal elementary abelian subgroup V, the faithful
centralizer quotient has trivial p-core. If the image of K is subnormal
in that quotient, its p-core is trivial. The image of O_p(K) lies there,
so O_p(K) centralizes the original V.

Source application: Aschbacher–Smith, proof of 14.7.32, printed p.1058.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {p : ℕ}

/-- Subnormality in the literal action quotient kills the intrinsic core action. -/
theorem IsPReduced.core_centralizes_of_subnormal_image {V : Subgroup G}
    (hV : IsPReduced p V) (K : Subgroup G)
    (hK : letI := hV.normal
      (K.map (QuotientGroup.mk' (centralizer (V : Set G)))).IsSubnormal) :
    K.pCoreIn p ≤ centralizer (V : Set G) := by
  let := hV.normal
  let q := QuotientGroup.mk' (centralizer (V : Set G))
  let f := q.subgroupMap K
  have hc : (pCore p K).map f ≤ pCore p (K.map q) :=
    le_sSup ⟨(inferInstance : (pCore p K).Normal).map f (q.subgroupMap_surjective K),
      pCore_isPGroup.map f⟩
  rintro x ⟨k,hk,rfl⟩
  apply (QuotientGroup.eq_one_iff (k:G)).mp
  have hh := pCoreIn_le_of_subnormal p hK
    (mem_map_of_mem (K.map q).subtype (hc (mem_map_of_mem f hk)))
  rw [hV.quotient_pCore_eq_bot] at hh
  exact mem_bot.mp hh
end Theory.GroupTheory
