module

public import Theory.Character.ModularBlock.ExactRelativeTrace
public import Theory.Character.ModularBlock.LeftIdealRelativeTrace

/-!
# Cyclic projectivity of a coefficient-vanishing left ideal

Let an involution fix a group-algebra idempotent by conjugation over a local
coefficient ring. If the idempotent's coefficients at the conjugation fixed
points lie in the maximal ideal, its left-ideal representation restricts
projectively to the involution subgroup. Conjugation invariance makes the
idempotent commute with that subgroup. The exact relative-trace correction
supplies a tracing element in the idempotent corner; its two conjugates sum
to the idempotent, so the preceding Higman criterion applies.

The named commutation bridge is public because later transported-range
constructions require the exact dependent representation instance. Ported
from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/LeftIdealHigman.lean` (revision `c3503435`).
-/

public section

noncomputable section

namespace ModularBlock.LeftIdealHigman

universe u v w

attribute [local instance] Fintype.ofFinite

lemma conjugation_eq_group_elements_mul
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (z : G) (a : MonoidAlgebra R G) :
    BrauerKernelRelativeTrace.conjugation R z a =
      MonoidAlgebra.of R G z * a * MonoidAlgebra.of R G z⁻¹ := by
  ext x
  rw [BrauerKernelRelativeTrace.conjugation_apply]
  simp [MonoidAlgebra.coeff_mul_single_apply, MonoidAlgebra.coeff_single_mul_apply,
    mul_assoc]

theorem commute_zpowers_of_conjugation_fixed
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (z : G) (hzne : z ≠ 1) (hz : z * z = 1)
    (f : MonoidAlgebra R G)
    (hfinv : BrauerKernelRelativeTrace.conjugation R z f = f) :
    ∀ s : Subgroup.zpowers z,
      Commute f (MonoidAlgebra.of R G ((Subgroup.zpowers z).subtype s)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzord : orderOf z = 2 := by
    apply orderOf_eq_prime (p := 2)
    · rw [pow_two, hz]
    · exact hzne
  let S : Subgroup G := Subgroup.zpowers z
  have hScard : Nat.card S = 2 := by
    dsimp [S]
    rw [Nat.card_zpowers, hzord]
  let zS : S := ⟨z, Subgroup.mem_zpowers z⟩
  have hzSne : zS ≠ 1 := by
    intro h
    apply hzne
    exact congrArg Subtype.val h
  obtain ⟨q, hq, hunique⟩ := (Nat.card_eq_two_iff' (1 : S)).mp hScard
  have hall (s : S) : s = 1 ∨ s = zS := by
    by_cases hs : s = 1
    · exact Or.inl hs
    · exact Or.inr ((hunique s hs).trans (hunique zS hzSne).symm)
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hconjmul :
      MonoidAlgebra.of R G z * f * MonoidAlgebra.of R G z = f := by
    have h := hfinv
    rw [conjugation_eq_group_elements_mul, hzinv] at h
    exact h
  have hcommz : Commute f (MonoidAlgebra.of R G z) := by
    rw [commute_iff_eq]
    calc
      f * MonoidAlgebra.of R G z =
          (MonoidAlgebra.of R G z * f * MonoidAlgebra.of R G z) *
            MonoidAlgebra.of R G z := by rw [hconjmul]
      _ = MonoidAlgebra.of R G z * f *
          (MonoidAlgebra.of R G z * MonoidAlgebra.of R G z) := by ac_rfl
      _ = MonoidAlgebra.of R G z * f := by
        rw [← map_mul, hz, map_one, mul_one]
  intro s
  change Commute f (MonoidAlgebra.of R G (s : G))
  rcases hall s with rfl | rfl
  · change Commute f (1 : MonoidAlgebra R G)
    exact Commute.one_right f
  · exact hcommz

theorem projective_zpowers_leftIdeal_of_fixed_coeff_mem_maximalIdeal
    {R : Type u} {G : Type v} [CommRing R] [IsLocalRing R]
    [Group G] [Finite G]
    (z : G) (hzne : z ≠ 1) (hz : z * z = 1)
    (f : MonoidAlgebra R G) (hf : IsIdempotentElem f)
    (hfinv : BrauerKernelRelativeTrace.conjugation R z f = f)
    (hfixed : ∀ x : G, z⁻¹ * x * z = x →
      f.coeff x ∈ IsLocalRing.maximalIdeal R) :
    Module.Projective (MonoidAlgebra R (Subgroup.zpowers z))
      (leftIdealRepresentation R f (Subgroup.zpowers z).subtype
        (commute_zpowers_of_conjugation_fixed z hzne hz f hfinv)).asModule := by
  classical
  obtain ⟨c, hcorner, htrace⟩ :=
    ExactRelativeTrace.exists_exact_relativeTrace_of_fixed_coeff_mem_maximalIdeal
      z hz f hf hfinv hfixed
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzord : orderOf z = 2 := by
    apply orderOf_eq_prime (p := 2)
    · rw [pow_two, hz]
    · exact hzne
  let S : Subgroup G := Subgroup.zpowers z
  have hScard : Nat.card S = 2 := by
    dsimp [S]
    rw [Nat.card_zpowers, hzord]
  let zS : S := ⟨z, Subgroup.mem_zpowers z⟩
  have hzSne : zS ≠ 1 := by
    intro h
    apply hzne
    exact congrArg Subtype.val h
  obtain ⟨q, hq, hunique⟩ := (Nat.card_eq_two_iff' (1 : S)).mp hScard
  have hall (s : S) : s = 1 ∨ s = zS := by
    by_cases hs : s = 1
    · exact Or.inl hs
    · exact Or.inr ((hunique s hs).trans (hunique zS hzSne).symm)
  have huniv : (Finset.univ : Finset S) = {1, zS} := by
    ext s
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
    exact hall s
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  let hcomm := commute_zpowers_of_conjugation_fixed z hzne hz f hfinv
  have hsum :
      ∑ s : S,
          MonoidAlgebra.of R G (S.subtype (s⁻¹)) * c *
            MonoidAlgebra.of R G (S.subtype s) = f := by
    rw [huniv, Finset.sum_pair hzSne.symm]
    have htrace' := htrace
    rw [conjugation_eq_group_elements_mul, hzinv] at htrace'
    simpa [S, zS, hzinv, ← MonoidAlgebra.one_def] using htrace'.symm
  exact projective_of_exact_relativeTrace_of_local
    f c hf hcorner S.subtype hcomm hsum


end ModularBlock.LeftIdealHigman

