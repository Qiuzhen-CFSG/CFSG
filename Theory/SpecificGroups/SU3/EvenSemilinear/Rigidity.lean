module

public import Theory.SpecificGroups.SU3.EvenSemilinear.Coordinates

/-!
# Elimination of binary Hermitian central shears

A norm-one torus acts by a nontrivial cube on the first coordinate and fixes
the second. Its commutators with root elements depend only on the first
coordinate. They therefore lie in the fixed subgroup of an automorphism
which fixes first coordinates and commutes with that actor. These commutators
cover all first coordinates; squares and the norm fill the central layer.

The two torus weights satisfy a norm identity, so their first weights already
determine their full action. Hence a torus-intertwining coordinate automorphism
with first coordinate `t * σ(a)` is exactly `(t * σ(a), t * conj(t) * σ(b))`.
This proves the binary shear-elimination step of Steinberg, Theorem 36,
`refs/KGroup/GLS3/Chapter2St1.tex`, for fixed-field order greater than two.
-/

public section

open Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.EvenSemilinear
open OddPrimeSylow.NormalizedOuter.Coverage
variable {E : Type*} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)

/-- A norm-one torus element with nontrivial cube kills all central shears. -/
theorem coordAut_eq_one_of_first_fixed {q : ℕ} (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (φ : MulAut (hermitianUnipotentCoord J))
    (hφ : ∀ z, (φ z).val.1 = z.val.1)
    (k : Eˣ) (hk : J.conj (k : E) = (k : E)⁻¹) (hk3 : (k : E) ^ 3 ≠ 1)
    (hact : ∀ z, φ (hermitianTorusAction J k z) =
      hermitianTorusAction J k (φ z)) : φ = 1 := by
  let N := φ.toMonoidHom.eqLocus (MonoidHom.id (hermitianUnipotentCoord J))
  have hN : (MonoidHom.id (hermitianUnipotentCoord J)).range ≤ N := by
    apply EvenInner.range_le_of_first_surjective J hcard hfixed
    intro a
    obtain ⟨z, hz⟩ := coord_first_surjective J hcard hfixed
      (a / ((k : E) ^ 3 - 1))
    change z.val.1 = _ at hz
    refine ⟨hermitianTorusAction J k z * z⁻¹, ?_, ?_⟩
    · change (hermitianTorusAction J k z).val.1 + -z.val.1 = a
      rw [EvenInner.normOne_action_first J k hk, hz]
      field_simp [sub_ne_zero.mpr hk3]
      ring
    · change φ (hermitianTorusAction J k z * z⁻¹) =
        hermitianTorusAction J k z * z⁻¹
      rw [map_mul, map_inv, hact]
      apply Subtype.ext
      apply Prod.ext
      · change (hermitianTorusAction J k (φ z)).val.1 + -(φ z).val.1 =
          (hermitianTorusAction J k z).val.1 + -z.val.1
        rw [EvenInner.normOne_action_first J k hk,
          EvenInner.normOne_action_first J k hk, hφ]
      · change (hermitianTorusAction J k (φ z)).val.2 + J.conj (φ z).val.2 -
            (hermitianTorusAction J k (φ z)).val.1 * J.conj (-(φ z).val.1) =
          (hermitianTorusAction J k z).val.2 + J.conj z.val.2 -
            (hermitianTorusAction J k z).val.1 * J.conj (-z.val.1)
        rw [EvenInner.normOne_action_second J k hk,
          EvenInner.normOne_action_second J k hk,
          EvenInner.normOne_action_first J k hk,
          EvenInner.normOne_action_first J k hk, hφ]
        have hp := (φ z).property
        rw [hφ] at hp
        linear_combination hp - z.property
  apply MulEquiv.ext
  intro z
  exact hN ⟨z, rfl⟩

/-- Matching first coordinates and one matching nontrivial norm-one torus
intertwiner determine the entire coordinate automorphism. -/
theorem coordAut_ext_of_first {q : ℕ} (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (φ ψ : MulAut (hermitianUnipotentCoord J))
    (hfirst : ∀ z, (φ z).val.1 = (ψ z).val.1)
    (k l : Eˣ) (hk : J.conj (k : E) = (k : E)⁻¹) (hk3 : (k : E) ^ 3 ≠ 1)
    (hφ : ∀ z, φ (hermitianTorusAction J k z) = hermitianTorusAction J l (φ z))
    (hψ : ∀ z, ψ (hermitianTorusAction J k z) = hermitianTorusAction J l (ψ z)) :
    φ = ψ := by
  have h := coordAut_eq_one_of_first_fixed J hcard hfixed (φ.trans ψ.symm) (fun z => by
    have he := coordAut_first_eq J ψ.symm (φ z) (ψ z) (hfirst z)
    simpa using he) k hk hk3 (fun z => by
      apply ψ.injective
      change ψ (ψ.symm (φ (hermitianTorusAction J k z))) =
        ψ (hermitianTorusAction J k (ψ.symm (φ z)))
      rw [ψ.apply_symm_apply, hφ, hψ, ψ.apply_symm_apply])
  apply MulEquiv.ext
  intro z
  have hz := congrArg (fun f : MulAut (hermitianUnipotentCoord J) => ψ (f z)) h
  simpa using hz

omit [Finite E] [CharP E 2] in
private theorem torus_weight_norm (k : Eˣ) :
    ((k : E) * (J.conj (k : E))⁻¹ ^ 2) *
      J.conj ((k : E) * (J.conj (k : E))⁻¹ ^ 2) =
      (J.conj (k : E))⁻¹ * (k : E)⁻¹ := by
  rw [map_mul, map_pow, map_inv₀, J.conj_involutive]
  field_simp

omit [CharP E 2] in
/-- The first weight determines the second weight of a unitary torus actor. -/
theorem torusAction_eq_of_first {q : ℕ} (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (k l : Eˣ)
    (hfirst : ∀ z : hermitianUnipotentCoord J,
      (hermitianTorusAction J k z).val.1 = (hermitianTorusAction J l z).val.1) :
    ∀ z, hermitianTorusAction J k z = hermitianTorusAction J l z := by
  obtain ⟨z, hz⟩ := coord_first_surjective J hcard hfixed 1
  have hw := hfirst z
  simp only [hermitianTorusAction_fst, hz, one_mul] at hw
  have hs := congrArg (fun x : E => x * J.conj x) hw
  rw [torus_weight_norm, torus_weight_norm] at hs
  intro w
  apply Subtype.ext
  apply Prod.ext (hfirst w)
  simp only [hermitianTorusAction_snd, mul_assoc, hs]

omit [CharP E 2] in
private theorem field_conj_commute (σ : E ≃+* E) (a : E) :
    J.conj (σ a) = σ (J.conj a) := by
  let := finiteFieldAut_isCyclic (E := E)
  let := IsCyclic.commGroup (α := E ≃+* E)
  exact congrArg (fun f : E ≃+* E => f a) (Commute.all J.conj σ).eq

omit [CharP E 2] in
/-- The genuine diagonal-field coordinate map intertwines the torus by its
field automorphism. -/
theorem scaledFieldCoordAut_torus (σ : E ≃+* E) (t k : Eˣ)
    (z : hermitianUnipotentCoord J) :
    scaledFieldCoordAut J σ t (hermitianTorusAction J k z) =
      hermitianTorusAction J (Units.map σ.toMonoidHom k) (scaledFieldCoordAut J σ t z) := by
  apply Subtype.ext
  apply Prod.ext
  · simp only [scaledFieldCoordAut_fst, hermitianTorusAction_fst,
      Units.coe_map, show ∀ a : E, σ.toMonoidHom a = σ a from fun _ => rfl,
      map_mul, map_pow, map_inv₀, field_conj_commute]
    ring
  · simp only [scaledFieldCoordAut_snd, hermitianTorusAction_snd,
      Units.coe_map, show ∀ a : E, σ.toMonoidHom a = σ a from fun _ => rfl,
      map_mul, map_inv₀, field_conj_commute]
    ring

/-- An automorphism with a semilinear first coordinate and a torus
intertwining action has the entire expected Heisenberg coordinate formula. -/
theorem coordAut_eq_scaledField_of_first {q : ℕ} (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) (hq : 2 < q)
    (φ : MulAut (hermitianUnipotentCoord J))
    (σ : E ≃+* E) (t : Eˣ)
    (hfirst : ∀ z : hermitianUnipotentCoord J, (φ z).val.1 = (t : E) * σ z.val.1)
    (hact : ∀ k : Eˣ, ∃ l : Eˣ, ∀ z : hermitianUnipotentCoord J,
      φ (hermitianTorusAction J k z) = hermitianTorusAction J l (φ z)) :
    φ = scaledFieldCoordAut J σ t := by
  obtain ⟨k, _, hk3, _, hk⟩ :=
    exists_hermitian_norm_one_torus_cube_ne_one J q hcard hfixed hJ hq
  obtain ⟨l, hl⟩ := hact k
  have hsame : ∀ w : hermitianUnipotentCoord J,
      hermitianTorusAction J l w = hermitianTorusAction J (Units.map σ.toMonoidHom k) w := by
    apply torusAction_eq_of_first J hcard hfixed
    intro w
    obtain ⟨z, rfl⟩ := φ.surjective w
    have hh := congrArg (fun x : hermitianUnipotentCoord J => x.val.1) (hl z).symm
    rw [hfirst, hermitianTorusAction_fst, hfirst] at hh
    simp only [hermitianTorusAction_fst, Units.coe_map,
      show ∀ a : E, σ.toMonoidHom a = σ a from fun _ => rfl,
      hfirst, field_conj_commute, map_mul, map_pow, map_inv₀] at hh ⊢
    linear_combination hh
  apply coordAut_ext_of_first J hcard hfixed φ (scaledFieldCoordAut J σ t)
    (fun z => (hfirst z).trans (scaledFieldCoordAut_fst J σ t z).symm)
    k (Units.map σ.toMonoidHom k) hk hk3
  · intro z
    rw [hl, hsame]
  · exact scaledFieldCoordAut_torus J σ t k

end BenderSuzuki.MatrixGroups.HermitianForm.EvenSemilinear
