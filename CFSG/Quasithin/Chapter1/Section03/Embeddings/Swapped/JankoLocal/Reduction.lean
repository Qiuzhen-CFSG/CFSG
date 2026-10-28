module

public import Theory.SpecificGroups.Janko1.Model.SolvableLocal

/-!
# Transporting the J₁ solvable-overgroup criterion to a swapped product

An actual isomorphism Q ≃ J₁ transports the local normalizer criterion to Q.
The projections of a Sylow two-subgroup of Q × Q are Sylow, and that subgroup
is their full product. Both projections of a solvable overgroup therefore
normalize the respective Sylow images, which proves normalization in Q × Q.
The subgroup A itself need not split as a product.

The prime-normalizer bounds are explicit premises here. The source assembly
must certify and supply them before obtaining the unconditional normalization
needed on Aschbacher–Smith printed p.510. The projection argument is shared
with the existing `Swapped.BenderNormalizers` proof, reproduced with narrow
imports for this independent J₁ branch.
-/

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.SwappedSylow

private theorem solvable_overgroup_transport {G K : Type*} [Group G] [Finite G] [Group K]
    (e : G ≃* K)
    (hK : ∀ (S : Sylow 2 K) (H : Subgroup K), Group.IsSolvable H →
      (S : Subgroup K) ≤ H → H ≤ normalizer (S : Set K))
    (S : Sylow 2 G) (H : Subgroup G) [Group.IsSolvable H]
    (hSH : (S : Subgroup G) ≤ H) : H ≤ normalizer (S : Set G) := by
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hTH : (T : Subgroup K) ≤ H.map e.toMonoidHom := Subgroup.map_mono hSH
  have hs : Group.IsSolvable (H.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective H)
  have hn := hK T (H.map e.toMonoidHom) hs hTH
  apply (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
  change H.map e.toMonoidHom ≤ (normalizer ((S : Subgroup G) : Set G)).map e.toMonoidHom
  rw [Subgroup.map_normalizer_eq_of_bijective _ e.bijective]
  exact hn

private theorem sylow_eq_prod {G K : Type*} [Group G] [Finite G] [Group K] [Finite K]
    (S : Sylow 2 (G × K)) :
    (S : Subgroup (G × K)) = ((S : Subgroup _).map (MonoidHom.fst G K)).prod
      ((S : Subgroup _).map (MonoidHom.snd G K)) := by
  let S₁ := S.mapSurjective (show Function.Surjective (MonoidHom.fst G K) from
    fun g => ⟨(g, 1), rfl⟩)
  let S₂ := S.mapSurjective (show Function.Surjective (MonoidHom.snd G K) from
    fun k => ⟨(1, k), rfl⟩)
  change (S : Subgroup _) = (S₁ : Subgroup G).prod (S₂ : Subgroup K)
  apply Eq.symm
  apply S.is_maximal'
  · obtain ⟨a, ha⟩ := S₁.isPGroup'.exists_card_eq
    obtain ⟨b, hb⟩ := S₂.isPGroup'.exists_card_eq
    apply IsPGroup.of_card (n := a + b)
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, ha, hb, pow_add]
  · intro x hx
    exact ⟨mem_map_of_mem _ hx, mem_map_of_mem _ hx⟩

private theorem prod_le_normalizer {Q : Type*} [Group Q] [Finite Q]
    (hQ : ∀ (S : Sylow 2 Q) (H : Subgroup Q), Group.IsSolvable H →
      (S : Subgroup Q) ≤ H → H ≤ normalizer (S : Set Q))
    (S : Sylow 2 (Q × Q)) (A : Subgroup (Q × Q))
    [Group.IsSolvable (A ⊔ (S : Subgroup (Q × Q)) : Subgroup (Q × Q))] :
    A ≤ normalizer (S : Set (Q × Q)) := by
  let H := A ⊔ (S : Subgroup (Q × Q))
  have hn (f : (Q × Q) →* Q) (hf : Function.Surjective f) :
      H.map f ≤ normalizer (((S : Subgroup (Q × Q)).map f) : Set Q) := by
    apply hQ (S.mapSurjective hf) (H.map f)
    · exact Group.isSolvable_of_surjective (f.subgroupMap_surjective H)
    · exact Subgroup.map_mono le_sup_right
  have h₁ := hn (MonoidHom.fst Q Q) (fun q => ⟨(q, 1), rfl⟩)
  have h₂ := hn (MonoidHom.snd Q Q) (fun q => ⟨(1, q), rfl⟩)
  apply le_normalizer_iff.mpr
  intro a ha s hs
  have haH : a ∈ H := (show A ≤ H from le_sup_left) ha
  have hsa := (mem_normalizer_iff.mp (h₁ (mem_map_of_mem _ haH)) s.1).mp
    (mem_map_of_mem (MonoidHom.fst Q Q) hs)
  have hsb := (mem_normalizer_iff.mp (h₂ (mem_map_of_mem _ haH)) s.2).mp
    (mem_map_of_mem (MonoidHom.snd Q Q) hs)
  rw [sylow_eq_prod S]
  exact ⟨hsa, hsb⟩


/-- The certified local bounds transport along the supplied actual model
isomorphism. -/
public theorem janko_one_model_solvable_overgroup_le_normalizer_of_prime_bounds
    (hN : ∀ p : ℕ, p.Prime → Odd p → Janko1.LocalStructure.PrimeNormalizerBound p)
    {Q : Type*} [Group Q] [Finite Q] (e : Q ≃* Janko1.Model)
    (S : Sylow 2 Q) (H : Subgroup Q) [Group.IsSolvable H]
    (hSH : (S : Subgroup Q) ≤ H) : H ≤ normalizer (S : Set Q) := by
  apply solvable_overgroup_transport e ?_ S H hSH
  intro T M hs hTM
  let _ := hs
  exact Janko1.LocalStructure.solvable_overgroup_le_normalizer_of_prime_bounds hN T M hTM

/-- The local prime-normalizer bounds imply the product normalization used
in the swapped-component argument, for any solvable join. -/
public theorem janko_one_model_prod_le_normalizer_of_prime_bounds
    (hN : ∀ p : ℕ, p.Prime → Odd p → Janko1.LocalStructure.PrimeNormalizerBound p)
    {Q : Type*} [Group Q] [Finite Q] (e : Q ≃* Janko1.Model)
    (S : Sylow 2 (Q × Q)) (A : Subgroup (Q × Q))
    [Group.IsSolvable (A ⊔ (S : Subgroup (Q × Q)) : Subgroup (Q × Q))] :
    A ≤ normalizer (S : Set (Q × Q)) := by
  apply prod_le_normalizer (fun T H hs hTH => ?_) S A
  let _ := hs
  exact janko_one_model_solvable_overgroup_le_normalizer_of_prime_bounds hN e T H hTH

end CFSG.Quasithin.Chapter1.XiEmbedding.SwappedSylow
