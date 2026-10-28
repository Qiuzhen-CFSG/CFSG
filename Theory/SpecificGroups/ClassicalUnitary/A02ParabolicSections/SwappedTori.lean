module

public import Theory.SpecificGroups.ClassicalUnitary.A02ParabolicSections.SwappedTori.TailSwaps
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Swapped elementary three-tori in the actual unitary local subgroups

For a prime dividing `q+1`, the prime roots of unity in the field of order
`q²` are norm-one units. Marking them by the additive prime field gives
three independent axes in the original projective tori. The tail swaps
exchange every pair of axes inside the same local subgroup. The dimension-five
projective torus is faithful when the prime differs from five.

These literal embeddings and swaps discharge the geometric hypothesis in the
central-cover lifting argument for Aschbacher--Smith A.2.18, printed p.40.
-/

public noncomputable section
open BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.A02ParabolicSections.SwappedTori
variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
/-- Mark the prime roots of unity by the additive prime field. -/
theorem roots_marking [Finite F] {q p : ℕ} (σ : F ≃+* F)
    (hcard : Nat.card F = q ^ 2) (hq : 2 ≤ q) (hconj : ∀ x, σ x = x ^ q)
    (hp : p.Prime) (hd : p ∣ q + 1) :
    ∃ _ρ : Multiplicative (ZMod p) ≃* rootsOfUnity p F,
      ∀ u : rootsOfUnity p F, σ (u.val : F) * (u.val : F) = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  have hdu : p ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hcard]
    have heq : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      have hq1 : 1 ≤ q := by omega
      have hq2 : 1 ≤ q ^ 2 := by nlinarith
      nlinarith [Nat.sub_add_cancel hq1, Nat.sub_add_cancel hq2]
    rw [heq]
    exact dvd_mul_of_dvd_left hd _
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p hdu
  have hroot : IsPrimitiveRoot u p := hu ▸ IsPrimitiveRoot.orderOf u
  have hc : Nat.card (rootsOfUnity p F) = p := hroot.card_rootsOfUnity'
  refine ⟨mulEquivOfPrimeCardEq (by simp) hc, ?_⟩
  intro u
  rw [hconj, ← pow_succ]
  obtain ⟨d, hd⟩ := hd
  rw [hd, pow_mul, (mem_rootsOfUnity' p u.val).mp u.property, one_pow]

/-- A coordinatewise marked torus sends a single axis to the same marked axis. -/
theorem marked_swap {A C : Type*} [Group A] [Group C] (ρ : A ≃* C)
    (u : A) (i j : Fin 3) :
    ((MulEquiv.piCongrRight (fun _ : Fin 3 => ρ)) (Pi.mulSingle i u)) ∘ Equiv.swap i j =
      (MulEquiv.piCongrRight (fun _ : Fin 3 => ρ)) (Pi.mulSingle j u) := by
  have h := Pi.mulSingle_comp_equiv (Equiv.swap i j) i u
  simp only [Equiv.symm_swap, Equiv.swap_apply_left] at h
  funext l
  exact congrArg ρ (congrFun h l)

/-- A faithful three-torus with pairwise swaps in the literal root normalizer. -/
theorem six_swapped_embedding [Finite F] (k : ℕ) (J : HermitianForm (6+k) F)
    (hJ : J.form = 1) {q p : ℕ} (hcard : Nat.card F = q ^ 2) (hq : 2 ≤ q)
    (hconj : ∀ x, J.conj x = x ^ q) (hp : p.Prime) (hd : p ∣ q + 1) :
    ∃ e : (Fin 3 → Multiplicative (ZMod p)) →*
        Subgroup.normalizer (Theory.SpecificGroups.UnitaryRootNormalizer.rootSubgroup k J hJ :
          Set (ProjectiveSpecialUnitaryMatrixGroup J)),
      Function.Injective e ∧ ∀ i j, ∃ r,
        r * e (Pi.mulSingle i (Multiplicative.ofAdd 1)) * r⁻¹ =
          e (Pi.mulSingle j (Multiplicative.ofAdd 1)) ∧
        r * e (Pi.mulSingle j (Multiplicative.ofAdd 1)) * r⁻¹ =
          e (Pi.mulSingle i (Multiplicative.ofAdd 1)) := by
  obtain ⟨ρ, hC⟩ := roots_marking J.conj hcard hq hconj hp hd
  let η := MulEquiv.piCongrRight (fun _ : Fin 3 => ρ)
  let e := (Theory.SpecificGroups.UnitaryRootNormalizer.torusNormalizer k J hJ _ hC).comp η.toMonoidHom
  refine ⟨e, (Theory.SpecificGroups.UnitaryRootNormalizer.torusNormalizer_injective k J hJ _ hC).comp η.injective, ?_⟩
  have hm (i j : Fin 3) :
      η.toMonoidHom (Pi.mulSingle i (Multiplicative.ofAdd 1)) ∘ Equiv.swap i j =
        η.toMonoidHom (Pi.mulSingle j (Multiplicative.ofAdd 1)) :=
    marked_swap ρ _ i j
  intro i j
  by_cases hij : i = j
  · subst j
    exact ⟨1, by simp, by simp⟩
  refine ⟨Six.localSwap k J hJ i j hij, ?_, ?_⟩
  · change _ * Theory.SpecificGroups.UnitaryRootNormalizer.torusNormalizer k J hJ _ hC _ * _ = _
    rw [Six.conjugate_torus, hm]
    rfl
  · change _ * Theory.SpecificGroups.UnitaryRootNormalizer.torusNormalizer k J hJ _ hC _ * _ = _
    rw [Six.conjugate_torus, Equiv.swap_comm i j, hm]
    rfl

/-- A faithful three-torus with pairwise swaps in the literal five-dimensional line parabolic. -/
theorem five_swapped_embedding [Finite F] (J : HermitianForm 5 F)
    (hJ : J.form = 1) {q p : ℕ} (hcard : Nat.card F = q ^ 2) (hq : 2 ≤ q)
    (hconj : ∀ x, J.conj x = x ^ q) (hp : p.Prime) (hd : p ∣ q + 1) (hne : p ≠ 5) :
    ∃ e : (Fin 3 → Multiplicative (ZMod p)) →* Theory.SpecificGroups.UnitaryFive.lineParabolic J,
      Function.Injective e ∧ ∀ i j, ∃ r,
        r * e (Pi.mulSingle i (Multiplicative.ofAdd 1)) * r⁻¹ =
          e (Pi.mulSingle j (Multiplicative.ofAdd 1)) ∧
        r * e (Pi.mulSingle j (Multiplicative.ofAdd 1)) * r⁻¹ =
          e (Pi.mulSingle i (Multiplicative.ofAdd 1)) := by
  obtain ⟨ρ, hC⟩ := roots_marking J.conj hcard hq hconj hp hd
  have hcop : p.Coprime 5 := hp.coprime_iff_not_dvd.mpr (by
    intro h
    exact hne ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h))
  have hfive (u : rootsOfUnity p F) (hu : u ^ 5 = 1) : u = 1 := by
    have hpow : u ^ p = 1 := Subtype.ext ((mem_rootsOfUnity p u.val).mp u.property)
    apply orderOf_eq_one_iff.mp
    apply Nat.dvd_one.mp
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpow) (orderOf_dvd_of_pow_eq_one hu)
  let η := MulEquiv.piCongrRight (fun _ : Fin 3 => ρ)
  let e := ((Theory.SpecificGroups.UnitaryFive.torusParabolic J hJ _ hC).comp
    (fiveParameters (rootsOfUnity p F))).comp η.toMonoidHom
  refine ⟨e, ((Theory.SpecificGroups.UnitaryFive.torusParabolic_injective J hJ _ hC hfive).comp
    (fiveParameters_injective _)).comp η.injective, ?_⟩
  have hm (i j : Fin 3) :
      η.toMonoidHom (Pi.mulSingle i (Multiplicative.ofAdd 1)) ∘ Equiv.swap i j =
        η.toMonoidHom (Pi.mulSingle j (Multiplicative.ofAdd 1)) :=
    marked_swap ρ _ i j
  intro i j
  by_cases hij : i = j
  · subst j
    exact ⟨1, by simp, by simp⟩
  refine ⟨Five.localSwap J hJ i j hij, ?_, ?_⟩
  · change _ * Theory.SpecificGroups.UnitaryFive.torusParabolic J hJ _ hC (fiveParameters _ _) * _ = _
    rw [Five.conjugate_torus, hm]
    rfl
  · change _ * Theory.SpecificGroups.UnitaryFive.torusParabolic J hJ _ hC (fiveParameters _ _) * _ = _
    rw [Five.conjugate_torus, Equiv.swap_comm i j, hm]
    rfl

end Theory.SpecificGroups.ClassicalUnitary.A02ParabolicSections.SwappedTori
