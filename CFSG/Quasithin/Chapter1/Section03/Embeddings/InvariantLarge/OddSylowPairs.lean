module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.RankOne
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import CFSG.Quasithin.Chapter1.Section03.Basic
public import CFSG.Quasithin.ClassificationModels.Families

/-!
# Odd complements permuting with a full Sylow two-subgroup

This records the actual pair, rather than an irreducibility hypothesis on its
action. Coprime kernels preserve the odd complement, while surjections preserve
the full Sylow subgroup and permutability. The rank-one cyclicity theorem then
excludes every Bender model. Chapter13 constructs this pair inside its escaping
component and uses the quotient transport without identifying the two carriers.

Source: Aschbacher–Smith, 1.3.4, pp.510–511; 13.1.12(3), pp.874–875.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge

/-- A genuine odd complement and a full Sylow two-subgroup which permute. -/
@[expose] public def HasOddSylowPair (p : ℕ) (A : Type*) [Group A] : Prop :=
  ∃ (S : Sylow 2 A) (B : Subgroup A), XiOddQuotient p B ∧
    (B : Set A) * (S : Set A) = (S : Set A) * (B : Set A)

namespace HasOddSylowPair
variable {p : ℕ} {A D : Type*} [Group A] [Group D]

/-- The complement forces a square prime divisor of the actual carrier order. -/
theorem prime_square_dvd (h : HasOddSylowPair p A) : p^2 ∣ Nat.card A := by
  obtain ⟨S,B,hB,_⟩ := h
  apply dvd_trans _ B.card_subgroup_dvd_card
  rcases hB with ⟨_,hc⟩ | ⟨_,hc,_⟩
  · rw [hc]
  · rw [hc]; exact pow_dvd_pow p (by decide : 2 ≤ 3)

/-- Transport through the literal surjective map, retaining the complement
because its kernel has order prime to p. -/
theorem map [Finite A] [Fact p.Prime] (h : HasOddSylowPair p A)
    (f : A →* D) (hf : Function.Surjective f)
    (hk : Nat.Coprime p (Nat.card f.ker)) : HasOddSylowPair p D := by
  obtain ⟨S,B,hB,hperm⟩ := h
  have hinj : Function.Injective (f.subgroupMap B) := by
    intro x y he
    exact injective_comp_subtype_of_coprime_ker f hk B hB.isPGroup
      (congrArg Subtype.val he)
  refine ⟨S.mapSurjective hf,B.map f,hB.of_mulEquiv
    (MulEquiv.ofBijective (f.subgroupMap B) ⟨hinj,f.subgroupMap_surjective B⟩),?_⟩
  change (B.map f : Set D) * ((S : Subgroup A).map f : Set D) =
    ((S : Subgroup A).map f : Set D) * (B.map f : Set D)
  simpa only [Set.image_mul, ← coe_map] using congrArg (Set.image f) (show (B : Set A) * ((S : Subgroup A) : Set A) =
      ((S : Subgroup A) : Set A) * (B : Set A) from hperm)

/-- A model equivalence transports both members of the actual pair. -/
theorem of_mulEquiv [Finite A] (h : HasOddSylowPair p A) (e : A ≃* D) : HasOddSylowPair p D := by
  obtain ⟨S,B,hB,hperm⟩ := h
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective,B.map e.toMonoidHom,
    hB.of_mulEquiv (B.equivMapOfInjective e.toMonoidHom e.injective),?_⟩
  change (B.map e.toMonoidHom : Set D) * ((S : Subgroup A).map e.toMonoidHom : Set D) =
    ((S : Subgroup A).map e.toMonoidHom : Set D) * (B.map e.toMonoidHom : Set D)
  simpa only [Set.image_mul, ← coe_map] using congrArg (Set.image e.toMonoidHom) (show (B : Set A) * ((S : Subgroup A) : Set A) =
      ((S : Subgroup A) : Set A) * (B : Set A) from hperm)

/-- Rank-one geometry forces this noncyclic complement to be cyclic. -/
theorem not_bender [Finite A] [Fact p.Prime] [IsSimpleGroup A]
    (h : HasOddSylowPair p A) (hp : 3 < p) (hna : ¬ IsMulCommutative A)
    (hm : ClassificationModels.IsBenderModel A) : False := by
  obtain ⟨S,B,hB,hperm⟩ := h
  have hcyc {n : ℕ} (hn : 1 < n) (hm : EvenActions.RankOne.IsBinaryRankOne A n) : False :=
    hB.not_isCyclic (EvenActions.RankOne.isCyclic_of_permuting hna hn hm (by omega)
      S B hB.isPGroup hperm)
  cases hm with
  | linear n hn hm => exact hcyc hn (Or.inl hm)
  | unitary n hn hm => exact hcyc hn (Or.inr (Or.inl hm))
  | suzuki m hm he => exact hcyc (n := 2*m+1) (by omega) (Or.inr (Or.inr ⟨m,rfl,he⟩))

end HasOddSylowPair
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge
