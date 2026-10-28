module
public import Theory.SpecificGroups.SU3.BorelTorus.Basic

/-!
# Commutator generation by subgroups of the binary unitary torus

A nontrivial first-coordinate scalar has invertible displacement. Commutators
therefore attain every first root coordinate; squares recover the central
coordinate via norm surjectivity. A scalar of weight one acts trivially on
both coordinates, including the cubic scalar kernel in the special cover.
The resulting criterion applies to arbitrary subgroups of the actual special
or projective torus, without identifying them by their orders.

Source: GLS4, Chapter 4, Lemma 3.5(c,d); Huppert II.10.12.
-/

public section
open Subgroup BenderSuzuki.External
open scoped commutatorElement
namespace BenderSuzuki.MatrixGroups.HermitianForm.BinaryFixedTorusGeneration
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- Weight one fixes both Hermitian root coordinates. -/
theorem action_eq_of_weight_one (k : Eˣ)
    (hk : (k : E) * (J.conj (k : E))⁻¹ ^ 2 = 1)
    (z : hermitianUnipotentCoord J) : hermitianTorusAction J k z = z := by
  have hbar : J.conj (k : E) ≠ 0 := (map_ne_zero J.conj).mpr k.ne_zero
  have he : (k : E) = J.conj (k : E) ^ 2 := by
    apply (div_eq_one_iff_eq (pow_ne_zero 2 hbar)).mp
    simpa only [div_eq_mul_inv, inv_pow] using hk
  have hf := congrArg J.conj he
  rw [map_pow, J.conj_involutive] at hf
  have hh : (k : E) ^ 4 = (k : E) := by
    calc
      (k : E) ^ 4 = ((k : E) ^ 2) ^ 2 := by ring
      _ = J.conj (k : E) ^ 2 := by rw [← hf]
      _ = (k : E) := he.symm
  have hc : (k : E) ^ 3 = 1 := by
    apply mul_left_cancel₀ k.ne_zero
    calc
      (k : E) * (k : E) ^ 3 = (k : E) ^ 4 := by ring
      _ = (k : E) := hh
      _ = (k : E) * 1 := (mul_one _).symm
  have hn : (J.conj (k : E)) * (k : E) = 1 := by
    rw [hf]
    calc
      (k : E) ^ 2 * (k : E) = (k : E) ^ 3 := by ring
      _ = 1 := hc
  apply Subtype.ext
  apply Prod.ext
  · change z.val.1 * (k : E) * (J.conj (k : E))⁻¹ ^ 2 = z.val.1
    rw [mul_assoc, hk, mul_one]
  · change z.val.2 * (J.conj (k : E))⁻¹ * (k : E)⁻¹ = z.val.2
    rw [mul_assoc, ← mul_inv, hn, inv_one, mul_one]

variable [Finite E] [CharP E 2] {q : ℕ}

/-- Any noncentralizing subgroup of the literal torus generates the root
group by commutators, for every realization of the two matrix maps. -/
theorem commutator_eq_of_action
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    {H : Type*} [Group H]
    (f : hermitianUnipotentCoord J →* H) (s : Eˣ →* H)
    (hact : ∀ k z, s k * f z * (s k)⁻¹ = f (hermitianTorusAction J k z))
    (B : Subgroup H) (hB : B ≤ s.range)
    (hne : ¬ B ≤ centralizer (f.range : Set H)) : ⁅B, f.range⁆ = f.range := by
  have hnorm : B ≤ normalizer (f.range : Set H) := by
    intro b hb
    obtain ⟨k, rfl⟩ := hB hb
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · rintro ⟨z, rfl⟩
      rw [hact]
      exact ⟨_, rfl⟩
    · intro hx
      obtain ⟨z, hz⟩ := hx
      have he := hact k⁻¹ z
      rw [map_inv, hz] at he
      have he' : x = f (hermitianTorusAction J k⁻¹ z) := by
        simpa only [inv_inv, inv_mul_cancel_left, mul_inv_cancel_right, mul_assoc,
          inv_mul_cancel, mul_one] using he
      exact ⟨_, he'.symm⟩
  apply le_antisymm (le_normalizer_iff_commutator_le_right.mp hnorm)
  have hk : ∃ k : Eˣ, s k ∈ B ∧ (k : E) * (J.conj (k : E))⁻¹ ^ 2 ≠ 1 := by
    by_contra! hh
    apply hne
    intro b hb
    obtain ⟨k, rfl⟩ := hB hb
    apply mem_centralizer_iff.mpr
    rintro _ ⟨z, rfl⟩
    have he := hact k z
    rw [action_eq_of_weight_one J k (hh k hb) z] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  obtain ⟨k, hkB, hk⟩ := hk
  apply EvenInner.range_le_of_first_surjective J hcard hfixed f ⁅B, f.range⁆
  intro a
  let c : E := (k : E) * (J.conj (k : E))⁻¹ ^ 2
  have hc : c - 1 ≠ 0 := sub_ne_zero.mpr hk
  let a₀ := a / (c - 1)
  obtain ⟨b, hb⟩ := huppert_II_10_4_trace_surjective J q hcard hfixed
    (-(a₀ * J.conj a₀)) (by
      rw [map_neg, map_mul, J.conj_involutive, mul_comm])
  let z : hermitianUnipotentCoord J := ⟨(a₀, b), by
    change b + J.conj b + a₀ * J.conj a₀ = 0
    rw [hb, neg_add_cancel]⟩
  have hz' : z.val.1 = a / (c - 1) := rfl
  refine ⟨hermitianTorusAction J k z * z⁻¹, ?_, ?_⟩
  · change (hermitianTorusAction J k z).val.1 + -z.val.1 = a
    rw [hermitianTorusAction_fst, mul_assoc, hz']
    change a / (c - 1) * c + -(a / (c - 1)) = a
    field_simp
    ring
  · have he : f (hermitianTorusAction J k z * z⁻¹) = ⁅s k, f z⁆ := by
      rw [map_mul, map_inv, ← hact, commutatorElement_def]
    rw [he]
    exact commutator_mem_commutator hkB ⟨z, rfl⟩
/-- The criterion for the genuine projective torus. The cubic kernel is
retained by using the projective matrix homomorphism itself. -/
theorem projective_commutator_eq
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hB : B ≤ BorelTorus.projectiveTorus J hJ)
    (hne : ¬ B ≤ centralizer (BorelTorus.projectiveRoot J hJ : Set _)) :
    ⁅B, BorelTorus.projectiveRoot J hJ⁆ = BorelTorus.projectiveRoot J hJ :=
  commutator_eq_of_action J hcard hfixed (hermitianUnipotentPSU J hJ)
    (hermitianTorusPSU J hJ) (EvenInner.projective_torus_action J hJ) B hB hne

/-- The same criterion in the special cover; central scalars are allowed
in B but cannot supply its required nontrivial root action. -/
theorem special_commutator_eq
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (B : Subgroup J.specialSubgroup)
    (hB : B ≤ BorelTorus.specialTorus J hJ)
    (hne : ¬ B ≤ centralizer (BorelTorus.specialRoot J hJ : Set _)) :
    ⁅B, BorelTorus.specialRoot J hJ⁆ = BorelTorus.specialRoot J hJ := by
  apply commutator_eq_of_action J hcard hfixed (hermitianUnipotentSU J hJ)
    (hermitianTorusSU J hJ) _ B hB hne
  intro k z
  apply mul_inv_eq_iff_eq_mul.mpr
  exact Subtype.ext (hermitianTorusGL_mul_unipotent J k z)

end BenderSuzuki.MatrixGroups.HermitianForm.BinaryFixedTorusGeneration
