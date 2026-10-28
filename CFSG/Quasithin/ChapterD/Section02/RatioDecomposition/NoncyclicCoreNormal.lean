module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.ClassifiedFactors
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.FactorCount

/-!
# Normality of a factor with noncyclic odd core

The odd core of an embedded normal factor lies in the corresponding ambient
prime core. If ambient conjugation moved that factor, its conjugate moving
involution would centralize the original core. The rank-two centralizer
bound for the original covering group would make that core cyclic, a
contradiction. This proves actual ambient normality without counting the
entire conjugacy orbit.

Source: Aschbacher--Smith, 15.1.2, second paragraph, printed p.1084.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterD.RatioDecomposition
variable {G H V : Type*} [Group G] [Finite G] [Group H] [Finite H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : Subgroup G} [K.Normal]
  {U : Submodule (ZMod 2) V} (c : FactorData ρ K U)
  (d : Decomposition c.representation)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem FactorData.factor_core_le_ambient_core (p : ℕ) (i : d.Index) :
    (pCore p (d.factor i).Carrier).map (c.ambientFactor d i).embedding.groupMap ≤ pCore p G := by
  let F := d.factor i
  let : F.actor.Normal := d.actor_normal c.representation c.faithful i
  have hF : F.actor.pCoreIn p ≤ pCore p K := by
    change (pCore p F.actor).map F.actor.subtype ≤ _
    exact le_sSup ⟨inferInstance, pCore_isPGroup.map _⟩
  have hK : (pCore p K).map K.subtype ≤ pCore p G :=
    le_sSup ⟨inferInstance, pCore_isPGroup.map _⟩
  rw [show F.actor = F.embedding.groupMap.range from rfl,
    pCoreIn_range_of_injective p _ F.embedding.group_injective] at hF
  change (pCore p F.Carrier).map (K.subtype.comp F.embedding.groupMap) ≤ pCore p G
  rw [← map_map]
  exact (map_mono hF).trans hK

omit [Finite G] [FiniteDimensional (ZMod 2) V] [K.Normal] in
private theorem actors_commute {i j : d.Index} (hij : i ≠ j)
    {x y : G} (hx : x ∈ (c.ambientFactor d i).actor)
    (hy : y ∈ (c.ambientFactor d j).actor) : Commute x y := by
  simp only [FactorData.ambientFactor, Factor.map_actor, FactorData.embedding] at hx hy
  obtain ⟨x,hx,rfl⟩ := hx
  obtain ⟨y,hy,rfl⟩ := hy
  exact congrArg K.subtype (d.actors_commute c.faithful hij hx hy).eq

theorem FactorData.factor_actor_normal_of_noncyclic_core
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (f : H →* G) (hf : Function.Surjective f) (hrank : primeRank p H ≤ 2)
    (hsyl : ∀ i (A : Subgroup (d.factor i).Carrier),
      A ∈ QhatStar (d.factor i).action ↔ ∃ S : Sylow 2 (d.factor i).Carrier, (S : Subgroup _) = A)
    (i : d.Index) (hncyc : ¬ IsCyclic (pCore p (d.factor i).Carrier))
    (t : (d.factor i).Carrier) (ht : orderOf t = 2)
    (hmove : t ∉ centralizer (pCore p (d.factor i).Carrier : Set _)) :
    (c.ambientFactor d i).actor.Normal := by
  let e : (d.factor i).Carrier →* G := K.subtype.comp (d.factor i).embedding.groupMap
  have hi : Function.Injective e := K.subtype_injective.comp (d.factor i).embedding.group_injective
  let R := (pCore p (d.factor i).Carrier).map e
  have hRle : R ≤ (c.ambientFactor d i).actor := map_le_range _ _
  have hRcore : R ≤ pCore p G := c.factor_core_le_ambient_core d p i
  have hnR : ¬ IsCyclic R := by
    intro hc
    let := hc
    have hi : Function.Injective (e.subgroupMap (pCore p (d.factor i).Carrier)) := by
      intro x y he
      apply Subtype.ext
      apply hi
      exact congrArg (fun z : R => (z : G)) he
    exact hncyc (isCyclic_of_injective (e.subgroupMap (pCore p (d.factor i).Carrier)) hi)
  have ht' : orderOf (e t) = 2 :=
    (orderOf_injective e hi t).trans ht
  have hm : e t ∉ centralizer (pCore p G : Set G) := by
    intro hh
    apply hmove
    intro x hx
    apply hi
    rw [map_mul, map_mul]
    exact hh (e x) (hRcore (mem_map_of_mem _ hx))
  have hfixed (g : G) : c.ambientAction d hsyl g i = i := by
    by_contra hne
    let j := c.ambientAction d hsyl g i
    have hmap := (c.ambientAction_spec d hsyl g i).2.1
    let a := (MulAut.conj g) (e t)
    have ha : a ∈ (c.ambientFactor d j).actor := by
      rw [← hmap]
      exact mem_map_of_mem _ ⟨t,rfl⟩
    have ha2 : orderOf a = 2 := (orderOf_injective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective _).trans ht'
    have ham : a ∉ centralizer (pCore p G : Set G) := by
      intro hh
      have hback := (inferInstance : (centralizer (pCore p G : Set G)).Normal).conj_mem a hh g⁻¹
      apply hm
      simpa only [a, MulAut.conj_apply, mul_assoc, inv_mul_cancel_left, inv_inv,
        inv_mul_cancel_right, inv_mul_cancel, mul_one] using hback
    have hfix : R ≤ centralizer ({a} : Set G) := by
      intro x hx y hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact (actors_commute c d (Ne.symm hne) (hRle hx) ha).symm.eq
    exact hnR (cyclic_pSubgroup_in_involution_centralizer_of_surjective_rank_two hp f hf hrank
      (pCore p G) pCore_isPGroup a ha2 ham R (pCore_isPGroup.map _) hfix)
  apply normalizer_eq_top_iff.mp
  apply top_unique
  intro g _
  apply mem_normalizer_iff_map_conj_eq.mpr
  have he := (c.ambientAction_spec d hsyl g i).2.1
  rwa [hfixed g] at he
end CFSG.Quasithin.ChapterD.RatioDecomposition
