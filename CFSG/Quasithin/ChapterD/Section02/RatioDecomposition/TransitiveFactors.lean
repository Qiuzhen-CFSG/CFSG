module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.NoncyclicCoreNormal
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.OrbitSupports
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.FactorCarrierConjugacy
public import Theory.GroupTheory.SylowKernelCore

/-!
# A transitive family of literal ratio factors

In a nonsingleton transitive family no actor is ambient normal, by the
independence of the original direct factors. Canonical embedded prime cores
are conjugate along the same action. The original cover's rank-two theorem
therefore gives exactly two factors and cyclic prime cores whenever a marked
factor involution moves that prime core. No orbit-kernel normality is assumed.

Source: Aschbacher--Smith 15.1.2, printed pp.1084 and 1086.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterD.RatioDecomposition
variable {G H V : Type*} [Group G] [Finite G] [Group H] [Finite H]
  [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : Subgroup G} {U : Submodule (ZMod 2) V}
  (c : FactorData ρ K U) (d : Decomposition c.representation)
namespace FactorData
omit [Finite G] in
theorem transitive_actor_not_normal (π : G →* Equiv.Perm d.Index)
    (hp : ∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g i)).actor)
    (ht : ∀ i j, ∃ g : G, π g i = j) (hmore : 1 < Nat.card d.Index) (i : d.Index) :
    ¬ (c.ambientFactor d i).actor.Normal := by
  intro hn
  let := hn
  let := (Finite.one_lt_card_iff_nontrivial (α := d.Index)).mp hmore
  obtain ⟨j,hji⟩ := exists_ne i
  obtain ⟨g,hg⟩ := ht i j
  have he : (c.ambientFactor d i).actor = (c.ambientFactor d j).actor := by
    rw [← hg,← hp]
    exact (Subgroup.Normal.map_conj_eq (c.ambientFactor d i).actor g).symm
  have hd : Disjoint (c.ambientFactor d i).actor (c.ambientFactor d j).actor := by
    simpa only [ambientFactor,Factor.map_actor,embedding] using
      Subgroup.disjoint_map K.subtype_injective (d.actors_independent.pairwiseDisjoint hji.symm)
  have hz : (c.ambientFactor d i).actor = ⊥ := disjoint_self.mp (he ▸ hd)
  obtain ⟨x,hx⟩ := exists_ne (1 : (d.factor i).Carrier)
  have hmem : (c.ambientFactor d i).embedding.groupMap x ∈ (c.ambientFactor d i).actor := ⟨x,rfl⟩
  rw [hz] at hmem
  let e : (d.factor i).Carrier →* G := K.subtype.comp (d.factor i).embedding.groupMap
  have hmem' : e x = 1 := hmem
  exact hx ((K.subtype_injective.comp (d.factor i).embedding.group_injective)
    (hmem'.trans e.map_one.symm))


theorem transitive_core_bound [K.Normal]
    (π : G →* Equiv.Perm d.Index)
    (hp : ∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g i)).actor)
    (ht : ∀ i j, ∃ g : G, π g i = j) (hmore : 1 < Nat.card d.Index)
    {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (f : H →* G) (hf : Function.Surjective f) (hrank : primeRank p H ≤ 2)
    (i : d.Index) (t : (d.factor i).Carrier) (htwo : orderOf t = 2)
    (hm : t ∉ centralizer (pCore p (d.factor i).Carrier : Set _)) :
    Nat.card d.Index = 2 ∧ ∀ j, IsCyclic (pCore p (d.factor j).Carrier) := by
  let R : d.Index → Subgroup G := fun j =>
    (pCore p (d.factor j).Carrier).map (c.ambientFactor d j).embedding.groupMap
  have he (j : d.Index) : R j = (c.ambientFactor d j).actor.pCoreIn p := by
    exact (pCoreIn_range_of_injective p _ (c.ambientFactor d j).embedding.group_injective).symm
  have hconj (j k : d.Index) : ∃ g : G, (R j).map (MulAut.conj g).toMonoidHom = R k := by
    obtain ⟨g,hg⟩ := ht j k
    refine ⟨g,?_⟩
    rw [he,map_pCoreIn_of_injective p _ _ (MulAut.conj g).injective,hp,hg,←he]
  have hne (j : d.Index) : R j ≠ ⊥ := by
    intro hz
    obtain ⟨g,hg⟩ := hconj j i
    rw [hz,Subgroup.map_bot] at hg
    apply hm
    intro x hx
    have hh : (c.ambientFactor d i).embedding.groupMap x ∈ R i :=
      mem_map_of_mem (c.ambientFactor d i).embedding.groupMap hx
    rw [← hg] at hh
    let e : (d.factor i).Carrier →* G := K.subtype.comp (d.factor i).embedding.groupMap
    have hh' : e x = 1 := hh
    have hx1 : x = 1 := (K.subtype_injective.comp (d.factor i).embedding.group_injective)
      (hh'.trans e.map_one.symm)
    simp [hx1]
  let e : (d.factor i).Carrier →* G := K.subtype.comp (d.factor i).embedding.groupMap
  have hei : Function.Injective e := K.subtype_injective.comp (d.factor i).embedding.group_injective
  have hm' : e t ∉ centralizer (pCore p G : Set G) := by
    intro hh
    apply hm
    intro x hx
    apply hei
    rw [map_mul,map_mul]
    exact hh (e x) (c.factor_core_le_ambient_core d p i (mem_map_of_mem e hx))
  obtain ⟨hc,hcyc⟩ := c.factor_orbit_bound d hodd f hf hrank (pCore p G) pCore_isPGroup
    id Function.injective_id R (fun j => map_le_range _ _)
    (fun j => pCore_isPGroup.map _) hne hconj i (e t) ⟨t,rfl⟩
    ((orderOf_injective e hei t).trans htwo) hm' hmore
  refine ⟨hc,fun j => ?_⟩
  let := hcyc j
  exact isCyclic_of_injective ((c.ambientFactor d j).embedding.groupMap.subgroupMap
    (pCore p (d.factor j).Carrier)) (by
      intro x y h
      apply Subtype.ext
      apply K.subtype_injective.comp (d.factor j).embedding.group_injective
      exact congrArg (fun z : R j => (z : G)) h)
end FactorData
end CFSG.Quasithin.ChapterD.RatioDecomposition
