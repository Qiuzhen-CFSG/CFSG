module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.UnitaryBorel.RootFixer
public import Theory.SpecificGroups.SU3.EvenSemilinear
public import Theory.SpecificGroups.SU3.BorelTorus.Basic

/-!
# The cubic residual determines PSU₃(4) automorphisms

A nonidentity element of the fixed field's multiplicative group gives an
order-three torus element. Its root conjugates also have order three.
Their commutators cover every first root coordinate; squares recover the
central coordinate. Thus fixing the cubic elements of the Borel fixes its
whole root group. The root-and-torus matrix calculation then kills the
semilinear automorphism, using proved semilinear coverage.

Source: Aschbacher--Smith, proof of 15.3.43, printed p.1140.
The fixed field has order four and the matrix field has order sixteen.
-/

public section
open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.UnitaryBorel
open HermitianForm HermitianForm.BorelTorus
variable {E : Type*} [Field E] [Finite E]
variable (J : HermitianForm 3 E)
variable (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

private theorem cubic_unit (hcard : Nat.card E = 4 ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ 4) :
    ∃ k : Eˣ, orderOf k = 3 ∧ J.conj (k : E) = k ∧
      (k : E) ≠ (J.conj (k : E))⁻¹ := by
  have hd : 3 ∣ Nat.card Eˣ := by rw [Nat.card_units, hcard]; decide
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := Eˣ) 3 hd
  have hk3 : k ^ 3 = 1 := hk ▸ pow_orderOf_eq_one k
  have hkc : J.conj (k : E) = k := by
    rw [hconj, show (4 : ℕ) = 3 + 1 from rfl, pow_succ]
    simp only [← Units.val_pow_eq_pow_val, hk3, Units.val_one, one_mul]
  refine ⟨k, hk, hkc, ?_⟩
  rw [hkc]
  intro he
  have hk2 : k ^ 2 = 1 := by
    apply Units.ext
    change (k : E) ^ 2 = 1
    calc
      (k : E) ^ 2 = (k : E)⁻¹ * k := by
        simpa only [pow_two] using congrArg (fun x : E => x * k) he
      _ = 1 := inv_mul_cancel₀ (Units.ne_zero k)
  have hk1 : k = 1 := by
    simpa only [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hk2, one_mul] using hk3
  simp [hk1] at hk

private theorem torus_mem_normalizer (k : Eˣ) :
    hermitianTorusPSU J hJ k ∈ normalizer
      ((hermitianUnipotentPSU J hJ).range : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  let : Finite (ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  apply Subgroup.mem_normalizer_fintype
  rintro _ ⟨z, rfl⟩
  refine ⟨hermitianTorusAction J k z, ?_⟩
  rw [hermitianTorusPSU_mul_unipotent, mul_assoc, mul_inv_cancel, mul_one]

omit [Finite E] in
private theorem cubic_torus_order (k : Eˣ) (hk : orderOf k = 3)
    (hkn : (k : E) ≠ (J.conj (k : E))⁻¹) :
    orderOf (hermitianTorusPSU J hJ k) = 3 := by
  apply orderOf_eq_prime
  · rw [← map_pow, show k ^ 3 = 1 from hk ▸ pow_orderOf_eq_one k, map_one]
  · intro he
    have hn := ((projective_eq_one_iff J hJ k).mp he).1
    change J.conj (k : E) = (k : E)⁻¹ at hn
    exact hkn (by rw [hn, inv_inv])

/-- The literal order-three elements of the root normalizer fix its entire
root group. No premise identifying the actor with the full Borel is used. -/
private theorem fixes_root_of_fixes_cubics [CharP E 2]
    (hcard : Nat.card E = 4 ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 4)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hfix : ∀ b ∈ normalizer ((hermitianUnipotentPSU J hJ).range :
      Set (ProjectiveSpecialUnitaryMatrixGroup J)), orderOf b = 3 → a b = b)
    (k : Eˣ) (hk : orderOf k = 3) (hkc : J.conj (k : E) = k)
    (hkn : (k : E) ≠ (J.conj (k : E))⁻¹) :
    ∀ z, a (hermitianUnipotentPSU J hJ z) = hermitianUnipotentPSU J hJ z := by
  let r := hermitianUnipotentPSU J hJ
  let t := hermitianTorusPSU J hJ k
  let B := normalizer (r.range : Set (ProjectiveSpecialUnitaryMatrixGroup J))
  let N := a.toMonoidHom.eqLocus (MonoidHom.id (ProjectiveSpecialUnitaryMatrixGroup J))
  have ht : t ∈ B := torus_mem_normalizer J hJ k
  have ht3 : orderOf t = 3 := cubic_torus_order J hJ k hk hkn
  have htN : t ∈ N := hfix t ht ht3
  have hw : (k : E) * (J.conj (k : E))⁻¹ ^ 2 = (k : E)⁻¹ := by
    rw [hkc, pow_two, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero k), one_mul]
  have hne : (k : E)⁻¹ ≠ 1 := by
    intro he
    have hk1 : k = 1 := Units.ext ((inv_eq_one.mp he))
    simp [hk1] at hk
  have hr : r.range ≤ N := by
    apply EvenInner.range_le_of_first_surjective J hcard hfixed r N
    intro x
    obtain ⟨z, hz'⟩ := EvenSemilinear.coord_first_surjective J hcard hfixed
      (x / ((k : E)⁻¹ - 1))
    change z.val.1 = x / ((k : E)⁻¹ - 1) at hz'
    refine ⟨hermitianTorusAction J k z * z⁻¹, ?_, ?_⟩
    · change (hermitianTorusAction J k z).val.1 + -z.val.1 = x
      rw [hermitianTorusAction_fst, mul_assoc, hw, hz']
      calc
        x / ((k : E)⁻¹ - 1) * (k : E)⁻¹ + -(x / ((k : E)⁻¹ - 1)) =
            x / ((k : E)⁻¹ - 1) * ((k : E)⁻¹ - 1) := by ring
        _ = x := div_mul_cancel₀ x (sub_ne_zero.mpr hne)
    · have hzB : r z ∈ B := r.range.le_normalizer ⟨z, rfl⟩
      have hcB : r z * t⁻¹ * (r z)⁻¹ ∈ B :=
        B.mul_mem (B.mul_mem hzB (B.inv_mem ht)) (B.inv_mem hzB)
      have hc3 : orderOf (r z * t⁻¹ * (r z)⁻¹) = 3 := by
        change orderOf (MulAut.conj (r z) t⁻¹) = 3
        exact (orderOf_injective (MulAut.conj (r z)).toMonoidHom
          (MulAut.conj (r z)).injective _).trans ((orderOf_inv t).trans ht3)
      have hcN : r z * t⁻¹ * (r z)⁻¹ ∈ N := hfix _ hcB hc3
      have hm := N.mul_mem htN hcN
      have he : t * (r z * t⁻¹ * (r z)⁻¹) =
          r (hermitianTorusAction J k z * z⁻¹) := by
        rw [map_mul, map_inv, ← EvenInner.projective_torus_action J hJ]
        dsimp only [r, t]
        group
      rwa [he] at hm
  exact fun z => hr ⟨z, rfl⟩

/-- In the actual simple PSU₃(4) carrier, the cubic Borel elements have
trivial pointwise automorphism fixer. Semilinear coverage is proved. -/
private theorem eq_one_of_fixes_standard_cubics
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hcard : Nat.card E = 4 ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ 4)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hfix : ∀ b ∈ normalizer ((hermitianUnipotentPSU J hJ).range :
      Set (ProjectiveSpecialUnitaryMatrixGroup J)), orderOf b = 3 → a b = b) : a = 1 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := 4) (by
    simpa only [Nat.card_eq_fintype_card, Nat.reducePow] using hcard)
  have hfixed : Nat.card {x : E // J.conj x = x} = 4 :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 2 (by decide) hcard hconj
  obtain ⟨k, hk, hkc, hkn⟩ := cubic_unit J hcard hconj
  obtain ⟨σ, u, hu⟩ := EvenSemilinear.semilinear_coverage J hJ (n := 2)
    (by decide) hcard hconj a
  exact eq_one_of_fixes_root_and_torus J hJ (n := 2) (by decide) hcard hfixed a σ u hu
    (fixes_root_of_fixes_cubics J hJ hcard hfixed a hfix k hk hkc hkn) k hkn
    (hfix _ (torus_mem_normalizer J hJ k) (cubic_torus_order J hJ k hk hkn))

include hJ in
/-- Sylow conjugacy transports the calculation to the prescribed Sylow
subgroup; its actual normalizer supplies the cubic elements. -/
theorem eq_one_of_fixes_sylowNormalizer_cubics
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hcard : Nat.card E = 4 ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ 4)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hfix : ∀ b ∈ normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J)),
      orderOf b = 3 → a b = b) : a = 1 := by
  let : Finite (ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  have hfixed : Nat.card {x : E // J.conj x = x} = 4 :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 2 (by decide) hcard hconj
  let Q := EvenTwoRank.rootSylow J hJ (n := 2) (by decide) hcard hfixed
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) P Q
  let f := MulAut.conj g
  have hR : (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map f.toMonoidHom =
      (hermitianUnipotentPSU J hJ).range := by
    have hh : (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map f.toMonoidHom = Q :=
      congrArg Sylow.toSubgroup hg
    rw [EvenTwoRank.rootSylow_coe] at hh
    exact hh
  have hB : (normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))).map
      f.toMonoidHom = normalizer ((hermitianUnipotentPSU J hJ).range :
        Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    change (normalizer ((P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :
      Set (ProjectiveSpecialUnitaryMatrixGroup J))).map f.toMonoidHom = _
    rw [Subgroup.map_equiv_normalizer_eq, hR]
  have ha : MulAut.congr f a = 1 := by
    apply eq_one_of_fixes_standard_cubics J hJ hcard hconj
    intro b hb hb3
    rw [← hB] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    have hx3 : orderOf x = 3 :=
      (orderOf_injective f.toMonoidHom f.injective x).symm.trans hb3
    change f (a (f.symm (f x))) = f x
    rw [f.symm_apply_apply, hfix x hx hx3]
  exact (MulAut.congr f).injective (ha.trans (map_one _).symm)

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.UnitaryBorel
