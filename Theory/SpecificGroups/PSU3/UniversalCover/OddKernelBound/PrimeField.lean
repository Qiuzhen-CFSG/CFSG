module

public import Theory.SpecificGroups.PSU3.UniversalCover.Projection
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.RootSylow
public import Theory.GroupTheory.PerfectCentralCoverSimultaneousInversion
public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# Defining-prime exclusion for prime-field PSU₃

For every odd prime p, centered Hermitian root coordinates
`(2a, -2a * conj a)` have exponent p. Two noncommuting such roots generate
the root Sylow subgroup of order p³. The sign torus element inverts both
roots and fixes their central commutator. Simultaneous-inversion transfer
therefore excludes p from every finite perfect central-cover kernel.

A proved Hermitian basis equivalence transports the result to the original
form and preserves the actual covering kernel. The final theorem applies
it to the constructed universal projection. This includes p = 3 and p = 5;
it does not assert the defining-prime result for fixed-field order p².

Source: Aschbacher–Smith, I.1.3(2), I.1.4(2), printed pp.407–408
(PDF pp.418–419), and GLS3 §6.1. Root coordinates and their Sylow order
are from Huppert II.10.12. This extends the checked ternary calculation in
`Theory.SpecificGroups.SU3.TernaryPerfectKernels.Roots` to all odd primes.
-/

public section

open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
open scoped commutatorElement
namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound
open OddPrimeSylow.NormalizedOuter.Coverage
variable {F : Type*} [Field F] (J : HermitianForm 3 F)

private def centered (a : F) : hermitianUnipotentCoord J :=
  ⟨(2 * a, -2 * a * J.conj a), by
    dsimp only
    simp only [map_mul, map_neg, map_ofNat]
    rw [J.conj_involutive]
    ring⟩

private theorem centered_pow (a : F) (n : ℕ) :
    centered J a ^ n = centered J ((n : F) * a) := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul]
    apply Subtype.ext
    change ((0 : F), 0) = (2 * (0 : F), -2 * (0 : F) * J.conj 0)
    simp
  | succ n ih =>
    rw [pow_succ, ih]
    apply Subtype.ext
    apply Prod.ext
    · change 2 * ((n : F) * a) + 2 * a = 2 * ((↑(n + 1) : F) * a)
      push_cast
      ring
    · change -2 * ((n : F) * a) * J.conj ((n : F) * a) +
        (-2 * a * J.conj a) - 2 * ((n : F) * a) * J.conj (2 * a) =
        -2 * ((↑(n + 1) : F) * a) * J.conj ((↑(n + 1) : F) * a)
      simp only [map_mul, map_natCast, map_ofNat, Nat.cast_add, Nat.cast_one, map_add, map_one]
      ring

private theorem centered_prime_pow {p : ℕ} [CharP F p] (a : F) :
    centered J a ^ p = 1 := by
  rw [centered_pow, CharP.cast_eq_zero F p, zero_mul]
  apply Subtype.ext
  change (2 * (0 : F), -2 * (0 : F) * J.conj 0) = ((0 : F), 0)
  simp

private theorem centered_inverted (a : F) :
    hermitianTorusAction J (-1) (centered J a) = (centered J a)⁻¹ := by
  apply Subtype.ext
  apply Prod.ext
  · simp only [hermitianTorusAction_fst, Units.val_neg, Units.val_one,
      map_neg, map_one, inv_neg, inv_one, neg_one_sq, mul_one, mul_neg_one]
    rfl
  · simp only [hermitianTorusAction_snd, Units.val_neg, Units.val_one,
      map_neg, map_one, inv_neg, inv_one, mul_neg_one, neg_neg]
    change -2 * a * J.conj a = J.conj (-2 * a * J.conj a)
    simp only [map_mul, map_neg, map_ofNat]
    rw [J.conj_involutive]
    ring

private theorem zero_first_central (z : hermitianUnipotentCoord J) (hz : z.val.1 = 0) :
    z ∈ center (hermitianUnipotentCoord J) := by
  apply mem_center_iff.mpr
  intro w
  apply Subtype.ext
  apply Prod.ext
  · change w.val.1 + z.val.1 = z.val.1 + w.val.1
    exact add_comm _ _
  · change w.val.2 + z.val.2 - w.val.1 * J.conj z.val.1 =
      z.val.2 + w.val.2 - z.val.1 * J.conj w.val.1
    simp [hz, add_comm]

private theorem zero_first_fixed (z : hermitianUnipotentCoord J) (hz : z.val.1 = 0) :
    hermitianTorusAction J (-1) z = z := by
  apply Subtype.ext
  apply Prod.ext
  · simp [hermitianTorusAction_fst, hz]
  · simp [hermitianTorusAction_snd]

private theorem subgroup_eq_top_of_noncommuting
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (hP : Nat.card P = p ^ 3) (H : Subgroup P) (x y : H)
    (hxy : x * y ≠ y * x) : H = ⊤ := by
  have hp := Fact.out (p := p.Prime)
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow hp).mp
    (hP ▸ H.card_subgroup_dvd_card)
  interval_cases k
  · let : IsCyclic H := isCyclic_of_card_dvd_prime (p := p)
      (by rw [he, pow_zero]; exact one_dvd _)
    exact (hxy (IsMulCommutative.is_comm.comm x y)).elim
  · let : IsCyclic H := isCyclic_of_card_dvd_prime (p := p) (by rw [he, pow_one])
    exact (hxy (IsMulCommutative.is_comm.comm x y)).elim
  · let : IsMulCommutative H := IsPGroup.isMulCommutative_of_card_eq_prime_sq he
    exact (hxy (IsMulCommutative.is_comm.comm x y)).elim
  · exact (Subgroup.card_eq_iff_eq_top H).mp (he.trans hP.symm)

/-- The standard root Sylow excludes the defining prime from every perfect cover. -/
theorem not_defining_prime_dvd_kernel_standard [Finite F]
    {p : ℕ} [Fact p.Prime] [CharP F p] (hodd : p ≠ 2)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card F = p ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = p)
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ p ∣ Nat.card f.toMonoidHom.ker := by
  let : Group.IsPerfect E := f.isPerfect
  have hp : p.Prime := Fact.out
  have htwo : (2 : F) ≠ 0 := by
    intro hz
    exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((CharP.cast_eq_zero_iff F p 2).mp hz))
  obtain ⟨a, ha⟩ : ∃ a : F, J.conj a ≠ a := by
    by_contra! hall
    let e : {x : F // J.conj x = x} ≃ F :=
      { toFun := Subtype.val
        invFun := fun x => ⟨x, hall x⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hh := hfixed.symm.trans ((Nat.card_congr e).trans hcard)
    nlinarith [hp.two_le]
  let x := centered J 1
  let y := centered J a
  have hxy : x * y ≠ y * x := by
    intro he
    apply ha
    have hh := congrArg (fun z : hermitianUnipotentCoord J => z.val.2) he
    change -2 * 1 * J.conj 1 + (-2 * a * J.conj a) - 2 * 1 * J.conj (2 * a) =
      -2 * a * J.conj a + (-2 * 1 * J.conj 1) - 2 * a * J.conj (2 * 1) at hh
    simp only [map_mul, map_one, map_ofNat, mul_one] at hh
    apply mul_left_cancel₀ (mul_ne_zero htwo htwo)
    linear_combination -hh
  have hc : Nat.card (hermitianUnipotentCoord J) = p ^ 3 :=
    (Nat.card_congr (MonoidHom.ofInjective (root_injective J hJ)).toEquiv).trans
      (rootGroup_card J hJ p hcard hfixed)
  have hgen : closure ({x, y} : Set (hermitianUnipotentCoord J)) = ⊤ := by
    let C := closure ({x, y} : Set (hermitianUnipotentCoord J))
    let xC : C := ⟨x, subset_closure (by simp)⟩
    let yC : C := ⟨y, subset_closure (by simp)⟩
    exact subgroup_eq_top_of_noncommuting hc C xC yC
      (fun h => hxy (congrArg Subtype.val h))
  have hgen_image : closure ({root J hJ x, root J hJ y} :
      Set (ProjectiveSpecialUnitaryMatrixGroup J)) = rootGroup J hJ := by
    have hh := congrArg (Subgroup.map (root J hJ)) hgen
    simpa only [rootGroup, MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton,
      ← MonoidHom.range_eq_map] using hh
  have hz0 : (⁅x, y⁆ : hermitianUnipotentCoord J).val.1 = 0 := by
    rw [hermitianUnipotent_commutator]
  have hz := zero_first_central J ⁅x,y⁆ hz0
  have hinv (b : F) : hermitianTorusPSU J hJ (-1) * root J hJ (centered J b) *
      (hermitianTorusPSU J hJ (-1))⁻¹ = (root J hJ (centered J b))⁻¹ := by
    rw [hermitianTorusPSU_mul_unipotent, mul_inv_cancel_right,
      centered_inverted, map_inv]
  have hfix : Commute (hermitianTorusPSU J hJ (-1))
      ⁅root J hJ x, root J hJ y⁆ := by
    rw [← map_commutatorElement]
    change hermitianTorusPSU J hJ (-1) * root J hJ ⁅x,y⁆ =
      root J hJ ⁅x,y⁆ * hermitianTorusPSU J hJ (-1)
    rw [hermitianTorusPSU_mul_unipotent, zero_first_fixed J _ hz0]
  exact PerfectCentralCovering.not_dvd_card_kernel_of_simultaneous_inversion
    f.toMonoidHom f.surjective f.ker_le_center
    (hp.coprime_iff_not_dvd.mpr (fun h => hodd
      ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)))
    (rootSylow J hJ hp hcard hfixed)
    (root J hJ x) (root J hJ y) (hermitianTorusPSU J hJ (-1))
    (by simpa only [rootSylow_coe] using hgen_image)
    (by rw [← map_pow, centered_prime_pow, map_one])
    (by rw [← map_pow, centered_prime_pow, map_one])
    (by
      rw [← map_commutatorElement, ← (root J hJ).map_one]
      exact (root_injective J hJ).ne (fun h => hxy
        (commutatorElement_eq_one_iff_mul_comm.mp h)))
    (by
      rw [← map_commutatorElement]
      exact (show Commute x ⁅x,y⁆ from mem_center_iff.mp hz x).map (root J hJ))
    (by
      rw [← map_commutatorElement]
      exact (show Commute y ⁅x,y⁆ from mem_center_iff.mp hz y).map (root J hJ))
    (hinv 1) (hinv a) hfix

/-- The defining-prime exclusion for an arbitrary nondegenerate Hermitian form. -/
theorem not_defining_prime_dvd_kernel [Finite F] {p : ℕ} (hp : p.Prime)
    (hodd : p ≠ 2) (hcard : Nat.card F = p ^ 2)
    (hconj : ∀ x, J.conj x = x ^ p)
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ¬ p ∣ Nat.card f.toMonoidHom.ker := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have hfixed := card_fixed J hcard hconj
  obtain ⟨e⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
    J p hcard hfixed
  let g : PerfectCentralCovering.Cover E
      (ProjectiveSpecialUnitaryMatrixGroup
        (OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J)) := {
    toMonoidHom := e.toMonoidHom.comp f.toMonoidHom
    surjective := e.surjective.comp f.surjective
    isPerfect := f.isPerfect
    ker_le_center := by
      intro x hx
      exact f.ker_le_center (e.injective (hx.trans e.map_one.symm)) }
  have hk : g.toMonoidHom.ker = f.toMonoidHom.ker :=
    MonoidHom.ker_comp_of_injective _ _ e.injective
  rw [← hk]
  exact not_defining_prime_dvd_kernel_standard
    (OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J)
    hodd rfl hcard hfixed g

/-- Application to the literal constructed universal projection at prime q. -/
theorem not_defining_prime_dvd_universal_kernel [Finite F] {p : ℕ} (hp : p.Prime)
    (hodd : p ≠ 2) (hcard : Nat.card F = p ^ 2)
    (hconj : ∀ x, J.conj x = x ^ p) :
    ¬ p ∣ Nat.card (PerfectCentralCovering.universalProjection
      (ProjectiveSpecialUnitaryMatrixGroup J)).ker := by
  have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hodd)
  let := projective_isQuasisimple J hp2 hcard hconj
  exact not_defining_prime_dvd_kernel J hp hodd hcard hconj
    (PerfectCentralCovering.universalCover (ProjectiveSpecialUnitaryMatrixGroup J))

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound
