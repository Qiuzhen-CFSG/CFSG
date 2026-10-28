module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.SpecificGroups.SL2.SylowNormalizerCard
public import Theory.NumberTheory.BinaryTorusParity
public import Theory.GroupTheory.PrimeOrderLift

/-!
# The field parity detected by a cubic Sylow normalizer

In a natural L₂(2ᵐ) block, an element of order three survives the two-core
quotient. If it normalizes a Sylow two-subgroup, its image lies in the
actual SL₂ Borel of order 2ᵐ(2ᵐ−1). Thus three divides 2ᵐ−1 and m is even.
The original plane-centralizer inspection applies this to its marked cubic
and the Sylow obtained by restricting the original radical.

Source: the rank-one field calculation in Aschbacher--Smith 13.3.12,
printed pp.889--890.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC
variable {J : Type*} [Group J] [Finite J]
theorem IsL2EvenBlock.exponent_even_of_sylowNormalizer_cubic {m : ℕ}
    (h : IsL2EvenBlock J m) (S : Sylow 2 J) (x : J)
    (hx : x ∈ normalizer (S : Set J)) (ho : orderOf x = 3) : Even m := by
  obtain ⟨_,_,F,_,_,hF,_,ρ,⟨d⟩,_⟩ := h
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let f := d.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hf : Function.Surjective f := d.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 J := by
    rw [MonoidHom.ker_comp_of_injective _ _ d.quotientIso.injective,QuotientGroup.ker_mk']
  let P := S.mapSurjective (f := f) hf
  have hn : f x ∈ normalizer (P : Set SL(2,F)) :=
    (S : Subgroup J).le_normalizer_map f (mem_map_of_mem f hx)
  have ho' : orderOf (f x) = 3 := by
    rw [f.orderOf_map_eq_of_coprime_of_isPGroup_ker
      (hk.symm ▸ (pCore_isPGroup (p := 2) (G := J))) x (by rw [ho]; decide),ho]
  have hd : 3 ∣ Nat.card F * (Nat.card F - 1) := by
    rw [←Matrix.SpecialLinearGroup.card_sylow_normalizer_even P]
    exact ho' ▸ orderOf_dvd_natCard (normalizer (P : Set SL(2,F))) hn
  have hc : Nat.Coprime 3 (Nat.card F) := by
    rw [hF]
    exact (by decide : Nat.Coprime 3 2).pow_right m
  exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff m).mp (hF ▸ hc.dvd_mul_left.mp hd)
end CFSG.Quasithin.ChapterC
