module
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.EightPointSolvable
public import Theory.GroupTheory.PPerfectHom

/-!
# Odd-prime exclusion in the Sylow-fixed point stabilizer

A nonzero vector fixed by an A₈ Sylow two-subgroup has stabilizer embedded
in S₄ wreath C₂, of order 1152. A two-perfect group whose two-core quotient
is a p-group for p>3 therefore has trivial image in this stabilizer: every
prime in the image order must be two, and two-perfectness kills that image.

Source: Aschbacher--Smith, 12.6.30(3), printed p.835. This gives a direct
point-action route to the constrained-component exclusion.
-/

public section
open Subgroup
namespace BinaryPermutation.TerminalOrthogonal.Eight

theorem sylow_fixed_stabilizer_card_dvd (Q : Sylow 2 (alternatingGroup (Fin 8)))
    (v : natural (Fin 8)) (hv : v ≠ 0)
    (hfixed : ∀ g ∈ (Q : Subgroup (alternatingGroup (Fin 8))),
      naturalRepresentation (Fin 8) g.val v = v) :
    Nat.card (BinaryNaturalDual.VectorStabilizers.representationStabilizer
      (naturalRepresentation (Fin 8)) v) ∣ 1152 := by
  obtain ⟨r,hr⟩ := alternating_exists_conjugate_stabilizer Q v hv hfixed
  let C := BinaryNaturalDual.VectorStabilizers.representationStabilizer
    (naturalRepresentation (Fin 8)) v
  let f : C →* FourBlockResidual.H :=
    (((MulAut.conj r.val).toMonoidHom).comp C.subtype).codRestrict _
      (fun x => (hr _).mp x.property)
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply (MulAut.conj r.val).injective
    exact congrArg Subtype.val h
  have hc : Nat.card FourBlockResidual.H = 1152 := by
    rw [Nat.card_congr Theory.SpecificGroups.SymmetricEight.FourBlockQuotient.fourStabilizerWreathEquiv.toEquiv,
      RegularWreathProduct.card]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  exact hc ▸ card_dvd_of_injective f hf

/-- A two-perfect group with p-group two-core quotient, for p>3, has no
nontrivial image in a group whose order divides the four-block order. -/
theorem hom_eq_one_of_large_prime_twoCore_quotient
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hA : IsPPerfect 2 A) (hq : IsPGroup p (A ⧸ pCore 2 A))
    (hB : Nat.card B ∣ 1152) (f : A →* B) : f = 1 := by
  obtain ⟨m,hm⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
  obtain ⟨n,hn⟩ := hq.exists_card_eq
  have hc : Nat.card A = p ^ n * 2 ^ m := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 A),hm,hn]
  have htwo : IsPGroup 2 f.range := by
    apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
    intro r hr
    obtain ⟨hrp,hrd,_⟩ := Nat.mem_primeFactors.mp hr
    have hrdA : r ∣ p ^ n * 2 ^ m := hc ▸ hrd.trans (card_range_dvd f)
    have hrdB : r ∣ 2 ^ 7 * 3 ^ 2 := by
      norm_num
      exact hrd.trans (f.range.card_subgroup_dvd_card.trans hB)
    have hr23 : r = 2 ∨ r = 3 := by
      rcases hrp.dvd_mul.mp hrdB with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).mp
          (hrp.dvd_of_dvd_pow h))
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hrp (by decide)).mp
          (hrp.dvd_of_dvd_pow h))
    have hr2 : r = 2 := by
      rcases hr23 with h | rfl
      · exact h
      rcases hrp.dvd_mul.mp hrdA with h | h
      · have he := (Nat.prime_dvd_prime_iff_eq hrp Fact.out).mp (hrp.dvd_of_dvd_pow h)
        omega
      · have he := (Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).mp (hrp.dvd_of_dvd_pow h)
        omega
    simp [hr2, Nat.prime_two]
  have he := hA.hom_eq_one_of_isPGroup htwo f.rangeRestrict
  ext a
  exact congrArg Subtype.val (congrArg (fun g : A →* f.range => g a) he)
end BinaryPermutation.TerminalOrthogonal.Eight
