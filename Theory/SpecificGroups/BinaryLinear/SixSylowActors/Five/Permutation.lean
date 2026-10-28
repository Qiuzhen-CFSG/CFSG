module

public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Five.Contracts
public import Theory.SpecificGroups.SymmetricSix.Parabolics

/-!
# A transposition centralizing an embedded A₆ Sylow subgroup

Every injective homomorphism A₆ → S₆ has image the alternating subgroup:
its image has order 360 and hence index two. Transporting the given Sylow
subgroup through this identification and then conjugating reduces to the
standard alternating flag stabilizer.

The two explicit members `(0 1)(2 3)` and `(2 4)(3 5)` of that stabilizer
have a common centralizer of order four containing `(0 1)`. This order
calculation is checked by kernel reduction over the permutations of six
letters. A subgroup of order four centralizing the whole Sylow subgroup
must therefore equal this common centralizer. Conjugation carries its
transposition back into the original supplied subgroup.

This proves the independent permutation contract used in the degree-five
actor calculation for Aschbacher–Smith, E.6.23, printed p.254 (PDF p.265).
The standard Sylow subgroup is supplied by `SymmetricSix.Parabolics`.
-/

namespace BinaryLinear.SixSylowActors.Five

open Theory.SpecificGroups.SymmetricSix
open Subgroup

private def firstGenerator : S6 := Equiv.swap 0 1 * Equiv.swap 2 3
private def secondGenerator : S6 := Equiv.swap 2 4 * Equiv.swap 3 5
private def generatorCentralizer : Subgroup S6 := centralizer {firstGenerator, secondGenerator}
private instance (x : S6) : Decidable (x ∈ generatorCentralizer) :=
  decidable_of_iff (firstGenerator * x = x * firstGenerator ∧ secondGenerator * x = x * secondGenerator) (by
    simp [generatorCentralizer, mem_centralizer_iff])

private theorem firstGenerator_mem : (⟨firstGenerator, by decide⟩ : A6) ∈ a6Borel := by decide
private theorem secondGenerator_mem : (⟨secondGenerator, by decide⟩ : A6) ∈ a6Borel := by decide

section
local instance : Fintype S6 := fintypePerm
set_option maxRecDepth 100000 in
private theorem generatorCentralizer_card : Nat.card generatorCentralizer = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
end
private theorem swap_mem_generatorCentralizer : Equiv.swap (0 : Fin 6) 1 ∈ generatorCentralizer := by decide

private theorem standard_swap_mem (B : Subgroup S6) (hB : Nat.card B = 4)
    (hc : ∀ b ∈ B, ∀ x ∈ a6Borel, Commute b (x : S6)) :
    Equiv.swap (0 : Fin 6) 1 ∈ B := by
  have hBC : B ≤ generatorCentralizer := by
    intro b hb x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact (hc b hb ⟨firstGenerator, by decide⟩ firstGenerator_mem).eq.symm
    · exact (hc b hb ⟨secondGenerator, by decide⟩ secondGenerator_mem).eq.symm
  have he : B = generatorCentralizer := eq_of_le_of_card_ge hBC (by rw [generatorCentralizer_card, hB])
  exact he ▸ swap_mem_generatorCentralizer

private theorem sylow_swap (P : Sylow 2 A6) (B : Subgroup S6)
    (hB : Nat.card B = 4)
    (hc : ∀ b ∈ B, ∀ x ∈ (P : Subgroup A6), Commute b (x : S6)) :
    ∃ b ∈ B, b.IsSwap := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A6 a6BorelSylow P
  let c : S6 ≃* S6 := MulAut.conj (g : S6)
  have hP : a6Borel.map (MulAut.conj g).toMonoidHom = (P : Subgroup A6) := by
    change ((g • a6BorelSylow : Sylow 2 A6) : Subgroup A6) = _
    rw [hg]
  have hBc : Nat.card (B.map c.symm.toMonoidHom) = 4 :=
    (card_map_of_injective c.symm.injective).trans hB
  have hcc : ∀ b ∈ B.map c.symm.toMonoidHom, ∀ x ∈ a6Borel,
      Commute b (x : S6) := by
    rintro _ ⟨b, hb, rfl⟩ x hx
    have hcx : MulAut.conj g x ∈ (P : Subgroup A6) :=
      hP ▸ mem_map.mpr ⟨x, hx, rfl⟩
    have hh := (hc b hb (MulAut.conj g x) hcx).map c.symm
    change Commute (c.symm b) (c.symm (c (x : S6))) at hh
    change Commute (c.symm b) (x : S6)
    simpa only [MulEquiv.symm_apply_apply] using hh
  have ht := standard_swap_mem _ hBc hcc
  have htb : c (Equiv.swap (0 : Fin 6) 1) ∈ B := by
    rcases ht with ⟨b, hb, he⟩
    rw [← he]
    change c (c.symm b) ∈ B
    rwa [c.apply_symm_apply]
  refine ⟨c (Equiv.swap (0 : Fin 6) 1), htb, ?_⟩
  refine ⟨(g : S6) 0, (g : S6) 1, (g : S6).injective.ne (by decide), ?_⟩
  exact (Equiv.swap_apply_apply (g : S6) 0 1).symm

/-- In the supplied permutation embedding, every subgroup of order four
centralizing the supplied Sylow two-subgroup contains a transposition. -/
public theorem permutationSylowSwap : PermutationSylowSwap := by
  intro ι hi Q B hB hc
  have hrCard : Nat.card ι.range = 360 :=
    (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv.symm).trans a6_order
  have hrIndex : ι.range.index = 2 := by
    have hh := ι.range.card_mul_index
    rw [hrCard, s6_order] at hh
    omega
  have hr : ι.range = alternatingGroup (Fin 6) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hrIndex
  let e : A6 ≃* A6 := (MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hr)
  apply sylow_swap (Q.mapSurjective (f := e.toMonoidHom) e.surjective) B hB
  intro b hb x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact hc b hb y hy

end BinaryLinear.SixSylowActors.Five
