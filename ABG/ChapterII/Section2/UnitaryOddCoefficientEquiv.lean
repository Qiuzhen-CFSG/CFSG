module
public import ABG.ChapterII.Section2.SpecialUnitaryEquivSL2
public import ABG.ChapterII.Section2.UnitaryOddFixedCoordinates
public import Theory.FieldTheory.OddQuadraticRestriction
public import ABG.ChapterII.Section2.UnitarySemilinear

/-!
# Special-unitary coordinates compatible with odd coefficient automorphisms

For odd prime p, nonzero n and an odd-order subgroup A of the full
coefficient automorphism group of GF(p^(2n)), the actual special subgroup
of the original GU₂ is isomorphic to SL₂(GF(p^n)) compatibly with A.
The result supplies an equivalence b from the stored involution's actual
fixed field to GF(p^n), an injective homomorphism r obtained by restriction
through b, and a group equivalence intertwining the given coefficient maps.
The explicit restriction equation ensures that r is the genuine base-field
action. Matrix-conditioned intertwining avoids introducing another SU action
instance. This is the unitary comparison in ABG II.3 Proposition 3, article
p.27, including q=3 and q=9.

The odd fixed quadratic field supplies A-fixed norm−1 and nonzero anti-fixed
coordinates z,t. The existing basis C=[[1,t],[z,−zt]] is therefore A-fixed
and transports the Hermitian form to a scalar alternating form. The proved
special-unitary equivalence over the actual fixed field is specified by
conjugation by C, which commutes with these coefficient maps. Its composition
with entrywise b gives the desired equivalence. The independently proved
quadratic restriction theorem makes r injective: its kernel has order at
most two and divides the odd order of A. All original forms, involutions,
coefficient actions and special subgroups are retained.
-/

open Matrix BenderSuzuki.MatrixGroups

namespace ABG

private theorem naturality
    {F L : Type*} [Field F] [Field L] (J : HermitianForm 2 F)
    (C : GL (Fin 2) F)
    (φ : J.specialSubgroup ≃* SpecialLinearGroup (Fin 2) (FixedBy.subfield F J.conj))
    (hφ : ∀ a, (φ.symm a).val = C * SpecialLinearGroup.toGL
      (SpecialLinearGroup.map (FixedBy.subfield F J.conj).subtype a) * C⁻¹)
    (b : FixedBy.subfield F J.conj ≃+* L)
    (σ : F ≃+* F) (τ : L ≃+* L)
    (hσ : ∀ x : FixedBy.subfield F J.conj, σ x.val = (b.symm (τ (b x))).val)
    (hC : GeneralLinearGroup.coefficientEquiv σ C = C)
    (x y : J.specialSubgroup)
    (hxy : y.val = GeneralLinearGroup.coefficientEquiv σ x.val) :
    (φ.trans (GorensteinWalter.sl2RingEquiv b)) y =
      GorensteinWalter.sl2RingEquiv τ ((φ.trans (GorensteinWalter.sl2RingEquiv b)) x) := by
  let K := FixedBy.subfield F J.conj
  let emb : SpecialLinearGroup (Fin 2) K →* GL (Fin 2) F :=
    SpecialLinearGroup.toGL.comp (SpecialLinearGroup.map K.subtype)
  have hx : x.val = C * emb (φ x) * C⁻¹ := by
    simpa only [emb, MonoidHom.comp_apply, φ.symm_apply_apply] using hφ (φ x)
  have hy : y.val = C * emb (φ y) * C⁻¹ := by
    simpa only [emb, MonoidHom.comp_apply, φ.symm_apply_apply] using hφ (φ y)
  have he : emb (φ y) = GeneralLinearGroup.coefficientEquiv σ (emb (φ x)) := by
    apply (MulAut.conj C).injective
    change C * emb (φ y) * C⁻¹ =
      C * GeneralLinearGroup.coefficientEquiv σ (emb (φ x)) * C⁻¹
    rw [← hy, hxy, hx]
    simp only [map_mul, map_inv, hC]
  apply Subtype.ext
  ext i j
  simp only [MulEquiv.trans_apply, GorensteinWalter.sl2RingEquiv_apply_entry]
  have hij : ((φ y).val i j).val = σ (((φ x).val i j).val) :=
    congrArg (fun g : GL (Fin 2) F => g i j) he
  have hb : (φ y).val i j = b.symm (τ (b ((φ x).val i j))) :=
    Subtype.ext (hij.trans (hσ _))
  rw [hb, b.apply_symm_apply]

/-- Choose an actual SU₂–SL₂ equivalence intertwining an odd coefficient subgroup,
together with its injective true restriction to the original base field. -/
public theorem exists_specialUnitary_equiv_sl2_of_odd_coefficients
    (p n : ℕ) [Fact p.Prime] (hp : Odd p) (hn : n ≠ 0)
    (A : Subgroup (GaloisField p (2 * n) ≃+* GaloisField p (2 * n)))
    (hA : Odd (Nat.card A)) :
    ∃ b : FixedBy.subfield (GaloisField p (2 * n)) (unitaryForm 2 p n hn).conj ≃+*
        GaloisField p n,
      ∃ r : A →* (GaloisField p n ≃+* GaloisField p n),
        ∃ e : (unitaryForm 2 p n hn).specialSubgroup ≃*
          SpecialLinearGroup (Fin 2) (GaloisField p n),
          Function.Injective r ∧
          (∀ (σ : A) (x : FixedBy.subfield (GaloisField p (2 * n))
            (unitaryForm 2 p n hn).conj),
            σ.val x.val = (b.symm (r σ (b x))).val) ∧
          ∀ (σ : A) (x y : (unitaryForm 2 p n hn).specialSubgroup),
            y.val = GeneralLinearGroup.coefficientEquiv σ.val x.val →
            e y = GorensteinWalter.sl2RingEquiv (r σ) (e x) := by
  classical
  obtain ⟨z, t, hz, ht0, ht, hfix⟩ :=
    exists_unitary_coordinates_fixed_by_odd_coefficients p n hp hn A hA
  obtain ⟨_, ⟨b⟩⟩ := unitaryQuadraticCoordinates p n hp hn
  obtain ⟨r, hrinj, hr⟩ :=
    GaloisField.exists_injective_odd_quadratic_restriction p n hn A hA b
  have hp2 : p ≠ 2 := by
    intro h
    obtain ⟨k, hk⟩ := hp
    omega
  have h2 : (2 : GaloisField p (2 * n)) ≠ 0 := by
    exact_mod_cast CharP.cast_ne_zero_of_ne_of_prime
      (GaloisField p (2 * n)) Nat.prime_two hp2
  obtain ⟨C, hCm, hC⟩ := HermitianForm.exists_skew_basis
    (unitaryForm 2 p n hn) rfl h2 z t hz ht0 ht
  let φ := HermitianForm.specialUnitaryEquivFixed (unitaryForm 2 p n hn) C
    (2 * t) (mul_ne_zero h2 ht0) hC
  refine ⟨b, r, φ.trans (GorensteinWalter.sl2RingEquiv b), hrinj, hr, ?_⟩
  intro σ x y hxy
  apply naturality (unitaryForm 2 p n hn) C φ
    (HermitianForm.specialUnitaryEquivFixed_symm_apply_val
      (unitaryForm 2 p n hn) C (2 * t) (mul_ne_zero h2 ht0) hC)
    b σ.val (r σ) (hr σ) _ x y hxy
  ext i j
  change σ.val (C.val i j) = C.val i j
  rw [hCm]
  fin_cases i <;> fin_cases j <;> simp [hfix σ]

end ABG


