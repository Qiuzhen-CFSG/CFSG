module
public import Theory.GroupTheory.CommutingPerfectRank
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Sylow-normalized components in groups of odd rank at most two

Three distinct conjugates of a component commute and would supply three
commuting copies of a nontrivial perfect group. The odd-prime-rank bound
excludes them. A Sylow two-subgroup normalizing the component excludes the
remaining orbit of length two by the odd index of a Sylow normalizer overgroup.

This is the ordinary-component specialization of Aschbacher–Smith A.3.8(3),
printed p.46, used on the actual two-core quotient in 14.7.67(4), p.1070.
It needs no classification of nonquasisimple C-components.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Odd rank at most two allows at most two conjugate components. -/
theorem IsComponent.normal_or_index_two_of_odd_rank_le_two
    (hrank : ∀ p : ℕ, p.Prime → Odd p → primeRank p G ≤ 2)
    {B : Subgroup G} (hB : IsComponent G B) :
    B.Normal ∨ (normalizer (B : Set G)).index = 2 := by
  classical
  by_cases hn : B.Normal
  · exact Or.inl hn
  have hex : ∃ g : G, B.map (MulAut.conj g).toMonoidHom ≠ B := by
    by_contra! h
    exact hn (normal_iff_map_conj_eq.mpr h)
  obtain ⟨g, hg⟩ := hex
  let C := B.map (MulAut.conj g).toMonoidHom
  have hC : IsComponent G C := hB.map_conj g
  have hBC : B ≠ C := hg.symm
  have hcomm (D E : Subgroup G) (hD : IsComponent G D) (hE : IsComponent G E)
      (hne : D ≠ E) : D ≤ centralizer (E : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hD.commutator_eq_bot_of_ne hE hne)
  have hpair (t : G) :
      B.map (MulAut.conj t).toMonoidHom = B ∨
        B.map (MulAut.conj t).toMonoidHom = C := by
    let D := B.map (MulAut.conj t).toMonoidHom
    by_cases hDB : D = B
    · exact Or.inl hDB
    by_cases hDC : D = C
    · exact Or.inr hDC
    have hD : IsComponent G D := hB.map_conj t
    have h₀₁ := hcomm B C hB hC hBC
    have h₀₂ := hcomm B D hB hD (fun he => hDB he.symm)
    have h₁₂ := hcomm C D hC hD (fun he => hDC he.symm)
    let : IsQuasisimple B := hB.2
    let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
    let : Nontrivial B := (QuotientGroup.mk'_surjective (center B)).nontrivial
    let f₁ : B →* G := (MulAut.conj g).toMonoidHom.comp B.subtype
    let f₂ : B →* G := (MulAut.conj t).toMonoidHom.comp B.subtype
    obtain ⟨p, hp, ho, hr⟩ :=
      CommutingPerfectRank.exists_odd_prime_rank_three_of_commuting_perfect
        B.subtype f₁ f₂ B.subtype_injective
        ((MulAut.conj g).injective.comp B.subtype_injective)
        ((MulAut.conj t).injective.comp B.subtype_injective)
        (fun x y => (h₀₁ x.property (f₁ y)
          (mem_map_of_mem (MulAut.conj g).toMonoidHom y.property)).symm)
        (fun x y => (h₀₂ x.property (f₂ y)
          (mem_map_of_mem (MulAut.conj t).toMonoidHom y.property)).symm)
        (fun x y => (h₁₂ (mem_map_of_mem (MulAut.conj g).toMonoidHom x.property)
          (f₂ y) (mem_map_of_mem (MulAut.conj t).toMonoidHom y.property)).symm)
    have hu := hrank p hp ho
    omega
  have hsub : (Set.range fun g : G => B.map (MulAut.conj g).toMonoidHom) ⊆ {B, C} := by
    rintro _ ⟨t, rfl⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hpair t
  have hi : (normalizer (B : Set G)).index ≤ 2 := by
    rw [← ncard_conjugates_eq_index_normalizer]
    exact (Set.ncard_le_ncard hsub).trans_eq (Set.ncard_pair hBC)
  have hnt : normalizer (B : Set G) ≠ ⊤ :=
    fun h => hn (normalizer_eq_top_iff.mp h)
  have hlo := (normalizer (B : Set G)).one_lt_index_of_ne_top hnt
  exact Or.inr (by omega)


/-- A Sylow-normalized component in a strongly quasithin group is normal. -/
theorem IsComponent.normal_of_sylow_normalizes_of_odd_rank_le_two
    (hrank : ∀ p : ℕ, p.Prime → Odd p → primeRank p G ≤ 2)
    {B : Subgroup G} (hB : IsComponent G B) (S : Sylow 2 G)
    (hS : (S : Subgroup G) ≤ normalizer (B : Set G)) : B.Normal := by
  rcases hB.normal_or_index_two_of_odd_rank_le_two hrank with hn | hi
  · exact hn
  · have hd := index_dvd_of_le hS
    rw [hi] at hd
    exact (S.not_dvd_index hd).elim

end Theory.GroupTheory
