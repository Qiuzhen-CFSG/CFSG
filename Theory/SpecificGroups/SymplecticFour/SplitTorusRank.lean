module

public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
public import Theory.GroupTheory.PrimeRankElementary
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Odd prime rank in the symplectic split torus

The matrix section of the two Borel determinant characters embeds the product
of two copies of the field's unit group. The roots of unity of prime order
therefore give an elementary abelian subgroup of rank two for every prime
dividing the multiplicative field order.

Source: the split-torus calculation used in Aschbacher–Smith 2.4.7,
printed p.541, and the symplectic local model in F.1.12(I)(2).
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F]

/-- The two independent diagonal coordinates contain an elementary abelian
rank-two subgroup for every prime dividing the multiplicative field order. -/
theorem split_torus_prime_rank {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card F - 1) : 2 ≤ primeRank p (Sp F) := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p
    (by simpa only [Nat.card_units] using hd)
  have hroot : IsPrimitiveRoot u p := hu ▸ IsPrimitiveRoot.orderOf u
  have hc : Nat.card (rootsOfUnity p F) = p := hroot.card_rootsOfUnity'
  have hpow (a : rootsOfUnity p F) : a ^ p = 1 :=
    Subtype.ext ((mem_rootsOfUnity p a.val).mp a.property)
  let f : (rootsOfUnity p F × rootsOfUnity p F) →* Sp F :=
    borel.subtype.comp (EvenBorelTorus.torusSection.comp
      ((rootsOfUnity p F).subtype.prodMap (rootsOfUnity p F).subtype))
  have ht : Function.Injective (EvenBorelTorus.torusSection (F := F)) := by
    intro x y h
    simpa only [EvenBorelTorus.characters_torusSection] using congrArg borelCharacters h
  have hf : Function.Injective f := by
    apply Subtype.val_injective.comp (ht.comp ?_)
    exact fun x y h => Prod.ext (Subtype.ext (congrArg Prod.fst h))
      (Subtype.ext (congrArg Prod.snd h))
  exact primeRank_ge_of_elementary_embedding
    (fun a => Prod.ext (hpow a.1) (hpow a.2))
    (by rw [Nat.card_prod, hc, pow_two]) f hf

end Theory.SpecificGroups.SymplecticFour
