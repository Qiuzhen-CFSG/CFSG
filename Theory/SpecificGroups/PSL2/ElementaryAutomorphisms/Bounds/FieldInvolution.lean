module

public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.OuterInvolutions
public import Theory.SpecificGroups.PSL2.OuterSolvable.FieldAutomorphisms
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# The explicit binary field involution

Prime Frobenius has order n on GF(2ⁿ). Thus in positive even degree its
half-degree power has order two. Uniqueness of an involution in a finite
cyclic group identifies every nontrivial field involution with this precise
map, x ↦ x^(2^(n/2)). Semilinear involution descent then conjugates every
outer involution of PSL₂ to its entrywise action, assuming only coverage.

The Frobenius-order proof follows the finite-field argument in
`Theory.SpecificGroups.Triality.EvenFieldFixedResidual.Twist`, independently
of the triality model. Source: GLS, Volume 2, Theorem 26.24, Step 5 and the
final contradiction, `refs/KGroup/GLS2/ChapterG.tex`.
-/

namespace Theory.PSL2

/-- The prime Frobenius on GF(2ⁿ) has exact order n. -/
public theorem binary_frobenius_order {n : ℕ} (hn : 0 < n) :
    orderOf (frobeniusEquiv (BinaryField n) 2) = n := by
  let K := BinaryField n
  let f : (K ≃ₐ[ZMod 2] K) →* (K ≃+* K) :=
    { toFun := AlgEquiv.toRingEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun a b h => AlgEquiv.ext fun x =>
    DFunLike.congr_fun h x
  have he : f (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K) =
      frobeniusEquiv K 2 := by
    ext x
    change x ^ Fintype.card (ZMod 2) = x ^ 2
    rw [ZMod.card]
  rw [← he, orderOf_injective f hf,
    FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]
  exact GaloisField.finrank 2 hn.ne'

/-- The distinguished field map; in positive even degree it is the unique involution. -/
@[expose] public noncomputable def binaryHalfFrobenius (n : ℕ) :
    BinaryField n ≃+* BinaryField n :=
  iterateFrobeniusEquiv (BinaryField n) 2 (n / 2)

public theorem binaryHalfFrobenius_apply (n : ℕ) (x : BinaryField n) :
    binaryHalfFrobenius n x = x ^ (2 ^ (n / 2)) := rfl

public theorem binaryHalfFrobenius_order {n : ℕ} (hn : 0 < n) (heven : Even n) :
    orderOf (binaryHalfFrobenius n) = 2 := by
  have horder := binary_frobenius_order hn
  have h := orderOf_pow_orderOf_div (x := frobeniusEquiv (BinaryField n) 2)
    (horder.symm ▸ hn.ne') (horder.symm ▸ even_iff_two_dvd.mp heven)
  simpa only [binaryHalfFrobenius, iterateFrobeniusEquiv_eq_pow, horder] using h

/-- Every binary field involution is precisely the half-degree Frobenius. -/
public theorem binary_field_involution_eq_halfFrobenius {n : ℕ} (hn : 0 < n)
    (σ : BinaryField n ≃+* BinaryField n) (hσ : orderOf σ = 2) :
    Even n ∧ σ = binaryHalfFrobenius n := by
  have hs : σ ^ 2 = 1 := by simpa only [hσ] using pow_orderOf_eq_one σ
  have hne : σ ≠ 1 := by intro h; simp [h] at hσ
  have heven := even_of_binary_field_involution hn σ
    (fun x => DFunLike.congr_fun hs x) hne
  let : IsCyclic (BinaryField n ≃+* BinaryField n) :=
    OuterSolvable.finiteFieldAut_isCyclic
  let : Finite (BinaryField n ≃+* BinaryField n) := Finite.of_injective
    (fun σ : BinaryField n ≃+* BinaryField n => (σ : BinaryField n → BinaryField n))
    DFunLike.coe_injective
  exact ⟨heven, IsCyclic.eq_of_orderOf_eq_two hσ (binaryHalfFrobenius_order hn heven)⟩

/-- Under coverage, every outer involution is inner-conjugate to the unique
order-two field automorphism, with its actual formula on field elements. -/
public theorem outer_involution_halfFrobenius_of_coverage {n : ℕ} (hn : 2 ≤ n)
    (hcoverage : ∀ a : MulAut (BinaryGroup n),
      ∃ (g : BinaryGroup n) (σ : BinaryField n ≃+* BinaryField n),
        a = MulAut.conj g * fieldAut σ)
    (a : MulAut (BinaryGroup n)) (ha : a ^ 2 = 1)
    (houter : a ∉ inner (BinaryField n)) :
    Even n ∧ orderOf (binaryHalfFrobenius n) = 2 ∧
      (∀ x : BinaryField n, binaryHalfFrobenius n x = x ^ (2 ^ (n / 2))) ∧
      ∃ c : BinaryGroup n,
        MulAut.congr (MulAut.conj c) (fieldAut (binaryHalfFrobenius n)) = a := by
  obtain ⟨g, σ, heq⟩ := hcoverage a
  obtain ⟨hσ, c, hc⟩ := outer_conjugate_field_of_semilinear a ha g σ heq houter
  obtain ⟨heven, rfl⟩ := binary_field_involution_eq_halfFrobenius (by omega) σ hσ
  exact ⟨heven, hσ, binaryHalfFrobenius_apply n, c, hc⟩

end Theory.PSL2
