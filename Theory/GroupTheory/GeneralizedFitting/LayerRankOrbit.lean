module

public import Theory.GroupTheory.GeneralizedFitting.SylowNormalizedComponent
public import Theory.GroupTheory.GeneralizedFitting.ComponentLayerStructure
/-!
# Component orbits controlled by the rank of the layer

All conjugates of an ordinary component lie in E(G). Three distinct ones
commute and contain three commuting copies of a nontrivial perfect group,
forcing odd prime rank at least three inside E(G). Thus a rank bound on
the layer alone bounds the orbit by two; no rank hypothesis on G is needed.

Source: Aschbacher–Smith, A.3.8(3), printed p.46; F.6.10, printed p.306.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
/-- Odd rank at most two allows at most two conjugate components. -/
theorem IsComponent.normal_or_index_two_of_layer_odd_rank_le_two
    (hrank : ∀ p : ℕ, p.Prime → Odd p → primeRank p (componentLayer G) ≤ 2)
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
    let E := componentLayer G
    let f₀ : B →* E := inclusion (show B ≤ E from le_sSup hB)
    let f₁ : B →* E := ((MulAut.conj g).toMonoidHom.comp B.subtype).codRestrict E
      (fun b => (le_sSup hC : C ≤ E) (mem_map_of_mem _ b.property))
    let f₂ : B →* E := ((MulAut.conj t).toMonoidHom.comp B.subtype).codRestrict E
      (fun b => (le_sSup hD : D ≤ E) (mem_map_of_mem _ b.property))
    have hf₁ : Function.Injective f₁ := by
      intro x y he
      exact B.subtype_injective ((MulAut.conj g).injective (congrArg Subtype.val he))
    have hf₂ : Function.Injective f₂ := by
      intro x y he
      exact B.subtype_injective ((MulAut.conj t).injective (congrArg Subtype.val he))
    obtain ⟨p, hp, ho, hr⟩ :=
      CommutingPerfectRank.exists_odd_prime_rank_three_of_commuting_perfect
        f₀ f₁ f₂ (inclusion_injective _) hf₁ hf₂
        (fun x y => Subtype.ext ((h₀₁ x.property (f₁ y)
          (mem_map_of_mem (MulAut.conj g).toMonoidHom y.property)).symm))
        (fun x y => Subtype.ext ((h₀₂ x.property (f₂ y)
          (mem_map_of_mem (MulAut.conj t).toMonoidHom y.property)).symm))
        (fun x y => Subtype.ext ((h₁₂ (mem_map_of_mem (MulAut.conj g).toMonoidHom x.property)
          (f₂ y) (mem_map_of_mem (MulAut.conj t).toMonoidHom y.property)).symm))
    change 3 ≤ primeRank p (componentLayer G) at hr
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



end Theory.GroupTheory
