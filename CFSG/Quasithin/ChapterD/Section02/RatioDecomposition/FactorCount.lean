module
public import Theory.GroupTheory.OddPrimeSectionCentralizers.FactorFamily
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.ConjugateFactors

/-!
# Odd cores in orbits of the literal ratio factors

The factor embeddings preserve disjointness and commutation. A moving
involution in one factor therefore centralizes every other factor, so the
rank-two section theorem bounds a same-prime family by two. If that family
is a nontrivial conjugacy orbit, it has length two and all its cores are cyclic.

Source: Aschbacher--Smith 15.1.2, second paragraph, printed p.1084.
-/

public section
open Subgroup

open Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterD.RatioDecomposition
variable {G H V : Type*} [Group G] [Finite G] [Group H] [Finite H]
  [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : Subgroup G} {U : Submodule (ZMod 2) V}
  (c : FactorData ρ K U) (d : Decomposition c.representation)

omit [Finite G] in
private theorem ambient_actors_disjoint {i j : d.Index} (hij : i ≠ j) :
    Disjoint (c.ambientFactor d i).actor (c.ambientFactor d j).actor := by
  simpa only [FactorData.ambientFactor,Factor.map_actor,FactorData.embedding] using
    Subgroup.disjoint_map K.subtype_injective (d.actors_independent.pairwiseDisjoint hij)

omit [Finite G] in
private theorem ambient_actors_commute {i j : d.Index} (hij : i ≠ j)
    {x y : G} (hx : x ∈ (c.ambientFactor d i).actor)
    (hy : y ∈ (c.ambientFactor d j).actor) : Commute x y := by
  simp only [FactorData.ambientFactor,Factor.map_actor,FactorData.embedding] at hx hy
  obtain ⟨x,hx,rfl⟩ := hx
  obtain ⟨y,hy,rfl⟩ := hy
  exact congrArg K.subtype (d.actors_commute c.faithful hij hx hy).eq

/-- The actual embedded factors retain the rank-two bound on any same-prime
subfamily, and every factor away from the moving involution has cyclic p-core. -/
theorem FactorData.factor_family_bound
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (f : H →* G) (hf : Function.Surjective f) (hrank : primeRank p H ≤ 2)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P)
    {ι : Type*} [Finite ι] (n : ι → d.Index) (hn : Function.Injective n)
    (R : ι → Subgroup G) (hRle : ∀ j, R j ≤ (c.ambientFactor d (n j)).actor)
    (hR : ∀ j, IsPGroup p (R j)) (hne : ∀ j, R j ≠ ⊥)
    (i : ι) (t : G) (htmem : t ∈ (c.ambientFactor d (n i)).actor)
    (ht : orderOf t = 2) (htP : t ∉ centralizer (P : Set G)) :
    Nat.card ι ≤ 2 ∧ ∀ j, j ≠ i → IsCyclic (R j) := by
  have hdis : Pairwise (fun j k => Disjoint (R j) (R k)) := by
    intro j k hjk
    exact (ambient_actors_disjoint c d (fun h => hjk (hn h))).mono (hRle j) (hRle k)
  have hcomm : Pairwise (fun j k => R j ≤ centralizer (R k : Set G)) := by
    intro j k hjk x hx y hy
    exact (ambient_actors_commute c d (fun h => hjk (hn h)) (hRle j hx) (hRle k hy)).symm.eq
  have hfix : ∀ j, j ≠ i → R j ≤ centralizer ({t} : Set G) := by
    intro j hji x hx y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact (ambient_actors_commute c d (fun h => hji (hn h)) (hRle j hx) htmem).symm.eq
  exact ⟨commuting_pFamily_card_le_two hp f hf hrank P hP t ht htP
    R i hR hne hdis hcomm hfix,
    fun j hj => cyclic_pSubgroup_in_involution_centralizer_of_surjective_rank_two
      hp f hf hrank P hP t ht htP (R j) (hR j) (hfix j hj)⟩

/-- A nontrivial orbit of same-prime factors has length two and cyclic cores. -/
theorem FactorData.factor_orbit_bound
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (f : H →* G) (hf : Function.Surjective f) (hrank : primeRank p H ≤ 2)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P)
    {ι : Type*} [Finite ι] (n : ι → d.Index) (hn : Function.Injective n)
    (R : ι → Subgroup G) (hRle : ∀ j, R j ≤ (c.ambientFactor d (n j)).actor)
    (hR : ∀ j, IsPGroup p (R j)) (hne : ∀ j, R j ≠ ⊥)
    (hconj : ∀ j k, ∃ g : G, (R j).map (MulAut.conj g).toMonoidHom = R k)
    (i : ι) (t : G) (htmem : t ∈ (c.ambientFactor d (n i)).actor)
    (ht : orderOf t = 2) (htP : t ∉ centralizer (P : Set G))
    (hmore : 1 < Nat.card ι) :
    Nat.card ι = 2 ∧ ∀ j, IsCyclic (R j) := by
  obtain ⟨hcard,hcyc⟩ := c.factor_family_bound d hp f hf hrank P hP n hn R hRle hR hne i t htmem ht htP
  refine ⟨by omega,?_⟩
  let := (Finite.one_lt_card_iff_nontrivial (α := ι)).mp hmore
  obtain ⟨j,hj⟩ := exists_ne i
  let := hcyc j hj
  intro k
  obtain ⟨g,hg⟩ := hconj j k
  rw [←hg]
  exact isCyclic_of_surjective ((MulAut.conj g).toMonoidHom.subgroupMap (R j))
    (MonoidHom.subgroupMap_surjective _ _)
end CFSG.Quasithin.ChapterD.RatioDecomposition
