module

public import Theory.Character.ModularBlock.LocalColumnNorm
public import Theory.Character.ModularBlock.MixedConjugationTrace
public import Theory.LinearAlgebra.Matrix.PermutationRestriction
public import Theory.Representation.IntegralTwistedPermutationTrace
public import Theory.Character.ModularBlock.BrauerCoefficientExtension
public import Theory.PPrimeCore

/-!
# Matrices for mixed Brauer traces

The operator of left multiplication by `uv` and inverse right multiplication
by `uw` factors into conjugation by `u` and the left-right operator for `v,w`.
In the row-permutation convention these are conjugation by `u⁻¹` and
`x ↦ v⁻¹*x*w`. For `v,w ∈ C_G(u)` the permutations commute, and the second
restricts to the same left-right permutation on the fixed basis `C_G(u)`.
No commutativity of `v` with `w` is required.

The coefficient ring contains primitive roots for all divisors of the group
order and inverts odd integers. These facts supply the integral coefficients
for spectral projectors of the odd-order left-right permutation.

Source: the mixed version of the Brauer--Suzuki trace argument used by Fong,
*Some Sylow subgroups of order 32 and a characterization of U(3,3)*,
J. Algebra 6 (1967), p. 71, equation (6).
-/

public section

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

noncomputable section
namespace ModularBlock.MixedBrauerTrace
open BrauerConjugationTrace MixedConjugationTrace
open PrincipalBlockConstruction BrauerBlockReduction
open CompatibleBrauerBlock
attribute [local instance] Fintype.ofFinite
variable {G R : Type*} [Group G] [Finite G] [CommRing R]

/-- Row permutation for left multiplication by `a` and inverse right multiplication by `b`. -/
@[expose] def leftRightPerm (a b : G) : Equiv.Perm G :=
  (Equiv.mulLeft a⁻¹).trans (Equiv.mulRight b)

omit [Finite G] in
@[simp] theorem leftRightPerm_apply (a b x : G) :
    leftRightPerm a b x = a⁻¹ * x * b := rfl

omit [Finite G] in
/-- Powers of left-right permutations can be computed without commuting the two elements. -/
theorem leftRightPerm_pow (a b : G) (m : ℕ) :
    leftRightPerm a b ^ m = leftRightPerm (a ^ m) (b ^ m) := by
  induction m with
  | zero => ext x; simp [leftRightPerm_apply]
  | succ m ih =>
    ext x
    simp only [pow_succ, Equiv.Perm.mul_apply, ih, leftRightPerm_apply, mul_inv_rev]
    simp only [← mul_assoc, ← inv_pow, ← pow_succ, ← pow_succ']
    rw [mul_assoc, ← pow_succ']

omit [Finite G] in
/-- A common exponent for the two elements is an exponent for their left-right permutation. -/
theorem leftRightPerm_pow_eq_one (a b : G) {m : ℕ}
    (ha : a ^ m = 1) (hb : b ^ m = 1) : leftRightPerm a b ^ m = 1 := by
  rw [leftRightPerm_pow, ha, hb]
  ext x
  simp

/-- The row-permutation matrix computes the projected mixed trace. -/
theorem trace_permMatrix_mul_rightMatrix [DecidableEq G]
    (e : MonoidAlgebra R G) (a b : G) :
    Matrix.trace ((leftRightPerm a b).permMatrix R * rightMatrix e) =
      LinearMap.trace R (MonoidAlgebra R G) (projectedLeftRight e a b) := by
  rw [trace_projectedLeftRight, PEquiv.toMatrix_toPEquiv_mul]
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply, rightMatrix,
    leftRightPerm_apply, id_eq, mul_assoc]

/-- Right multiplication by a central element commutes with every left-right permutation. -/
theorem rightMatrix_commute_leftRight [DecidableEq G]
    (e : MonoidAlgebra R G) (he : e ∈ Set.center (MonoidAlgebra R G))
    (a b : G) : Commute ((leftRightPerm a b).permMatrix R) (rightMatrix e) := by
  rw [Matrix.commute_permMatrix_iff_entries]
  intro i j
  change e.coeff ((a⁻¹ * j * b)⁻¹ * (a⁻¹ * i * b)) = e.coeff (j⁻¹ * i)
  have harg : (a⁻¹ * j * b)⁻¹ * (a⁻¹ * i * b) = b⁻¹ * (j⁻¹ * i) * (b⁻¹)⁻¹ := by group
  rw [harg]
  exact CentralIdempotentSupport.coeff_conj_eq_of_mem_center e he b⁻¹ (j⁻¹ * i)

omit [Finite G] in
/-- Centralizer membership makes conjugation commute with the left-right permutation. -/
theorem conjugationPerm_commute_leftRight (u : G)
    (v w : Subgroup.centralizer ({u} : Set G)) :
    Commute (conjugationPerm u⁻¹) (leftRightPerm (v : G) (w : G)) := by
  have hv : Commute (v : G) u := Subgroup.mem_centralizer_singleton_iff.mp v.property
  have hw : Commute (w : G) u := Subgroup.mem_centralizer_singleton_iff.mp w.property
  change _ * _ = _ * _
  ext x
  simp only [Equiv.Perm.mul_apply, conjugationPerm_apply, leftRightPerm_apply, inv_inv]
  calc
    _ = (u⁻¹ * (v : G)⁻¹) * x * ((w : G) * u) := by group
    _ = ((v : G)⁻¹ * u⁻¹) * x * (u * (w : G)) := by
      rw [hv.inv_inv.eq, hw.eq]
    _ = _ := by group

/-- The mixed permutation factors with the row-permutation order of multiplication. -/
theorem mixed_permMatrix_factor [DecidableEq G] (u : G)
    (v w : Subgroup.centralizer ({u} : Set G)) :
    (leftRightPerm (u * (v : G)) (u * (w : G))).permMatrix R =
      (conjugationPerm u⁻¹).permMatrix R *
        (leftRightPerm (v : G) (w : G)).permMatrix R := by
  rw [← Matrix.permMatrix_mul]
  congr 1
  ext x
  simp only [Equiv.Perm.mul_apply, conjugationPerm_apply, leftRightPerm_apply,
    inv_inv, mul_inv_rev]
  group

omit [Finite G] in
/-- The local left-right permutation is the restriction of the ambient permutation. -/
theorem leftRightPerm_centralizer_apply (u : G)
    (v w x : Subgroup.centralizer ({u} : Set G)) :
    (leftRightPerm v w x : G) = leftRightPerm (v : G) (w : G) (x : G) := rfl

omit [Finite G] in
/-- The least common multiple of the element orders kills the left-right permutation. -/
theorem leftRightPerm_lcm_pow_eq_one (v w : G) :
    leftRightPerm v w ^ (Nat.lcm (orderOf v) (orderOf w)) = 1 := by
  apply leftRightPerm_pow_eq_one
  · exact orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_lcm_left _ _)
  · exact orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_lcm_right _ _)

/-- The localized cyclotomic order contains roots for every divisor of the group order. -/
theorem exists_localization_primitiveRoot (d : PrincipalCongruenceBlockData G)
    (m : ℕ) (hm : m ∣ Nat.card G) :
    ∃ ζ : Localization.AtPrime d.primeIdeal, IsPrimitiveRoot ζ m := by
  let ζ : cyclotomicOrder d.eta :=
    ⟨d.eta ^ (Nat.card G / m), pow_mem_cyclotomicOrder
      (eta_mem_cyclotomicOrder d.eta) _⟩
  refine ⟨algebraMap _ _ ζ, ?_⟩
  apply IsPrimitiveRoot.of_map_of_injective (f := IsotypicLattice.localizationToComplex d)
    _ (IsotypicLattice.localizationToComplex_injective d)
  rw [IsotypicLattice.localizationToComplex_algebraMap]
  exact d.eta_spec.pow Nat.card_pos (Nat.div_mul_cancel hm).symm

/-- Odd denominators are invertible in the localization at the characteristic-two prime. -/
theorem isUnit_natCast_localization (d : PrincipalCongruenceBlockData G)
    (m : ℕ) (hm : Nat.Coprime 2 m) :
    IsUnit (m : Localization.AtPrime d.primeIdeal) := by
  apply Not.imp_symm (BlockPrimitivity.localizationToResidue_eq_zero_iff_not_isUnit d _).mpr
  rw [map_natCast, CharP.cast_eq_zero_iff (principalResidueField d) 2]
  exact Nat.prime_two.coprime_iff_not_dvd.mp hm

/-- Matrix form of the mixed trace at two elements with common two-part. -/
theorem trace_mixed_matrix [DecidableEq G]
    (e : MonoidAlgebra R G) (u : G)
    (v w : Subgroup.centralizer ({u} : Set G)) :
    Matrix.trace ((conjugationPerm u⁻¹).permMatrix R *
      (leftRightPerm (v : G) (w : G)).permMatrix R * rightMatrix e) =
    LinearMap.trace R (MonoidAlgebra R G)
      (projectedLeftRight e (u * (v : G)) (u * (w : G))) := by
  rw [← mixed_permMatrix_factor]
  exact trace_permMatrix_mul_rightMatrix e _ _

omit [Finite G] in
/-- Restriction to the centralizer identifies the ambient and local left-right matrices. -/
theorem leftRightMatrix_centralizer [DecidableEq G] (u : G)
    (v w : Subgroup.centralizer ({u} : Set G)) :
    ((leftRightPerm (v : G) (w : G)).permMatrix R).submatrix
      (fun x : Subgroup.centralizer ({u} : Set G) => (x : G))
      (fun x : Subgroup.centralizer ({u} : Set G) => (x : G)) =
    (leftRightPerm v w).permMatrix R := by
  exact Matrix.submatrix_permMatrix_of_intertwining _ _ _ Subtype.val_injective
    (fun _ => rfl)

omit [Finite G] in
/-- The fixed group basis of inverse conjugation is the element centralizer. -/
@[expose] def fixedCentralizerEquiv (u : G) :
    {x // conjugationPerm u⁻¹ x = x} ≃ Subgroup.centralizer ({u} : Set G) :=
  Equiv.subtypeEquivRight (conjugationPerm_inv_fixed_iff u)

omit [Finite G] in
/-- The fixed-index restriction is the local left-right matrix, reindexed by the centralizer. -/
theorem leftRightMatrix_fixed [DecidableEq G] (u : G)
    (v w : Subgroup.centralizer ({u} : Set G)) :
    ((leftRightPerm (v : G) (w : G)).permMatrix R).submatrix
      (fun x : {x // conjugationPerm u⁻¹ x = x} => x.val) Subtype.val =
    ((leftRightPerm v w).permMatrix R).submatrix
      (fixedCentralizerEquiv u) (fixedCentralizerEquiv u) := by
  rw [← leftRightMatrix_centralizer u v w, Matrix.submatrix_submatrix]
  rfl

/-- Transporting both local matrices to fixed indices preserves their product trace. -/
theorem trace_local_mixed_matrix [DecidableEq G] (u : G)
    (v w : Subgroup.centralizer ({u} : Set G))
    (b : MonoidAlgebra R (Subgroup.centralizer ({u} : Set G))) :
    Matrix.trace (((leftRightPerm v w).permMatrix R).submatrix
      (fixedCentralizerEquiv u) (fixedCentralizerEquiv u) *
      (rightMatrix b).submatrix (fixedCentralizerEquiv u) (fixedCentralizerEquiv u)) =
    LinearMap.trace R (MonoidAlgebra R (Subgroup.centralizer ({u} : Set G)))
      (projectedLeftRight b v w) := by
  classical
  let : Fintype (Subgroup.centralizer ({u} : Set G)) := Fintype.ofFinite _
  rw [Matrix.submatrix_mul_equiv]
  have h : Matrix.trace (((leftRightPerm v w).permMatrix R * rightMatrix b).submatrix
      (fixedCentralizerEquiv u) (fixedCentralizerEquiv u)) =
      Matrix.trace ((leftRightPerm v w).permMatrix R * rightMatrix b) :=
    Fintype.sum_equiv (fixedCentralizerEquiv u) _ _ (fun _ => rfl)
  exact h.trans (trace_permMatrix_mul_rightMatrix b v w)

omit [Finite G] in
/-- The common left-right exponent is odd when both element orders are odd. -/
theorem leftRight_lcm_coprime (v w : G)
    (hv : Nat.Coprime 2 (orderOf v)) (hw : Nat.Coprime 2 (orderOf w)) :
    Nat.Coprime 2 (Nat.lcm (orderOf v) (orderOf w)) :=
  Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul _ _) (hv.mul_right hw)

omit [Finite G] in
/-- The common left-right exponent divides the group order. -/
theorem leftRight_lcm_dvd_card (v w : G) :
    Nat.lcm (orderOf v) (orderOf w) ∣ Nat.card G :=
  Nat.lcm_dvd (orderOf_dvd_natCard v) (orderOf_dvd_natCard w)

 /-- The mixed principal-block trace agrees with the compatible local trace at
 two-elements and arbitrary odd-order centralizer elements. -/
theorem principalBlock_mixed_trace_eq
    (d : PrincipalCongruenceBlockData G) (u : G)
    (hu : ∃ n : ℕ, u ^ (2 ^ n) = 1)
    (v w : Subgroup.centralizer ({u} : Set G))
    (hv : Nat.Coprime 2 (orderOf (v : G)))
    (hw : Nat.Coprime 2 (orderOf (w : G))) :
    LinearMap.trace ℂ (MonoidAlgebra ℂ G)
        (projectedLeftRight (BlockOrthogonality.principalBlockElement d)
          (u * (v : G)) (u * (w : G))) =
      LinearMap.trace ℂ
        (MonoidAlgebra ℂ (Subgroup.centralizer ({u} : Set G)))
        (projectedLeftRight
          (BlockOrthogonality.principalBlockElement (localData d
            (Subgroup.centralizer ({u} : Set G)))) v w) := by
  classical
  let C := Subgroup.centralizer ({u} : Set G)
  letI : Fintype C := Fintype.ofFinite C
  let R := Localization.AtPrime d.primeIdeal
  let k := principalResidueField d
  let e : MonoidAlgebra R G := BlockOrthogonality.localizedPrincipalBlockElement d
  let b : MonoidAlgebra R C := localPrincipalBlockElementInAmbientLocalization d C
  let σ : Equiv.Perm G := conjugationPerm u⁻¹
  let T : Matrix G G R := (leftRightPerm (v : G) (w : G)).permMatrix R
  let P : Matrix G G R := rightMatrix e
  let q := fixedCentralizerEquiv u
  let Tloc : Matrix C C R := (leftRightPerm v w).permMatrix R
  let T₀ : Matrix {x // σ x = x} {x // σ x = x} R :=
    Tloc.submatrix q q
  let B : Matrix {x // σ x = x} {x // σ x = x} R :=
    (rightMatrix b).submatrix q q
  let m := Nat.lcm (orderOf (v : G)) (orderOf (w : G))
  have hmpos : 0 < m := Nat.lcm_pos (orderOf_pos (v : G)) (orderOf_pos (w : G))
  have hmcoprime : Nat.Coprime 2 m := leftRight_lcm_coprime _ _ hv hw
  have hmdvd : m ∣ Nat.card G := leftRight_lcm_dvd_card _ _
  obtain ⟨ζ, hζ⟩ := exists_localization_primitiveRoot d m hmdvd
  let f : R →+* k := localizationToResidue d
  letI : Field k := Ideal.Quotient.field d.primeIdeal
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨algebraMap _ R a, localizationToResidue_algebraMap d a⟩
  have hf (r : R) (hr : f r ≠ 0) : IsUnit r := by
    by_contra hn
    exact hr ((BlockPrimitivity.localizationToResidue_eq_zero_iff_not_isUnit d r).mpr hn)
  letI : NeZero m := ⟨hmpos.ne'⟩
  letI : NeZero ((m : ℕ) : k) := ⟨by
    intro hz
    exact Nat.prime_two.coprime_iff_not_dvd.mp hmcoprime
      ((CharP.cast_eq_zero_iff k 2 m).mp hz)⟩
  have hζk : IsPrimitiveRoot (f ζ) m :=
    BrauerCoefficientExtension.primitive_map f hζ
  have hu' := hu
  obtain ⟨n, hn⟩ := hu
  have hσ : σ ^ (2 ^ n) = 1 := by
    simpa [σ] using conjugationPerm_pow_eq_one u⁻¹ (by simpa [inv_pow] using congrArg Inv.inv hn)
  have hcommσT : Commute σ (leftRightPerm (v : G) (w : G)) :=
    conjugationPerm_commute_leftRight u v w
  have hσT : Commute (σ.permMatrix R) T := by
    exact Matrix.permMatrix_commute hcommσT
  have hσP : Commute (σ.permMatrix R) P :=
    rightMatrix_commute_conjugation e
      (BlockOrthogonality.localizedPrincipalBlockElement_mem_center d) u⁻¹
  have hTP : Commute T P :=
    rightMatrix_commute_leftRight e
      (BlockOrthogonality.localizedPrincipalBlockElement_mem_center d)
      (v : G) (w : G)
  have hTm : T ^ m = 1 := by
    rw [← Matrix.permMatrix_pow]
    rw [show leftRightPerm (v : G) (w : G) ^ m = 1 by
      simpa [m] using leftRightPerm_lcm_pow_eq_one (v : G) (w : G)]
    simp
  have hTlocm : Tloc ^ m = 1 := by
    rw [← Matrix.permMatrix_pow]
    rw [show leftRightPerm v w ^ m = 1 by
      simpa [m] using leftRightPerm_lcm_pow_eq_one (v : C) (w : C)]
    simp
  have hsubpow (a : ℕ) :
      (Tloc.submatrix q q) ^ a = (Tloc ^ a).submatrix q q := by
    have hsub_one : (1 : Matrix C C R).submatrix q q = 1 := by
      ext i j
      change (if q i = q j then 1 else 0) = (if i = j then 1 else 0)
      by_cases hij : i = j
      · subst j; simp only [if_pos rfl]
      · have hqij : q i ≠ q j := fun h => hij (q.injective h)
        simp only [if_neg hij, if_neg hqij]
    induction a with
    | zero =>
      simpa only [pow_zero] using hsub_one.symm
    | succ a ih =>
      rw [pow_succ, pow_succ, ih,
        Matrix.submatrix_mul_equiv (Tloc ^ a) Tloc q q q]
  have hT₀m : T₀ ^ m = 1 := by
    rw [show T₀ = Tloc.submatrix q q by rfl, hsubpow, hTlocm]
    have hsub_one : (1 : Matrix C C R).submatrix q q = 1 := by
      ext i j
      change (if q i = q j then 1 else 0) = (if i = j then 1 else 0)
      by_cases hij : i = j
      · subst j; simp only [if_pos rfl]
      · have hqij : q i ≠ q j := fun h => hij (q.injective h)
        simp only [if_neg hij, if_neg hqij]
    exact hsub_one
  have hT₀B : Commute T₀ B := by
    change (Tloc.submatrix q q) * (rightMatrix b).submatrix q q =
      (rightMatrix b).submatrix q q * (Tloc.submatrix q q)
    rw [Matrix.submatrix_mul_equiv Tloc (rightMatrix b) q q q,
      Matrix.submatrix_mul_equiv (rightMatrix b) Tloc q q q]
    exact congrArg (fun M => M.submatrix q q)
      (rightMatrix_commute_leftRight b
        (localPrincipalBlockElementInAmbientLocalization_mem_center d C) v w).eq
  have hB : IsIdempotentElem B := by
    change (rightMatrix b).submatrix q q * (rightMatrix b).submatrix q q =
      (rightMatrix b).submatrix q q
    rw [Matrix.submatrix_mul_equiv (rightMatrix b) (rightMatrix b) q q q]
    exact congrArg (fun M => M.submatrix q q)
      (rightMatrix_isIdempotent b
        (localPrincipalBlockElementInAmbientLocalization_isIdempotent d C)).eq
  have hT₀map : f.mapMatrix T₀ = (f.mapMatrix T).submatrix Subtype.val Subtype.val := by
    have hT₀eq : T₀ = T.submatrix Subtype.val Subtype.val := by
      dsimp [T₀, Tloc, T, q]
      exact (leftRightMatrix_fixed (R := R) u v w).symm
    rw [hT₀eq]
    ext i j
    change f (T i.val j.val) = f (T i.val j.val)
    rfl
  have hcoeff : ∀ x : C, f (b.coeff x) = f (e.coeff (x : G)) := by
    intro x
    exact LocalColumnNorm.localPrincipalBlock_localization_coeff_reduce d u hu' x
  have hBmap : f.mapMatrix B = (f.mapMatrix P).submatrix Subtype.val Subtype.val := by
    ext i j
    change f (b.coeff ((q j)⁻¹ * q i)) =
      f (e.coeff (((q j : C) : G)⁻¹ * ((q i : C) : G)))
    simpa using hcoeff ((q j)⁻¹ * q i)
  have hmatrix := Matrix.trace_permMatrix_mul_mul_eq_trace_fixed_lift
    f hsurj hf σ hσ P T (rightMatrix_isIdempotent e
      (BlockOrthogonality.localizedPrincipalBlockElement_isIdempotent d))
    hσP hσT hTP B T₀ hB hT₀B hBmap hT₀map
    hmpos hTm hT₀m (isUnit_natCast_localization d m hmcoprime) hζ hζk
  have htraceR :
      LinearMap.trace R (MonoidAlgebra R G)
          (projectedLeftRight e (u * (v : G)) (u * (w : G))) =
        LinearMap.trace R (MonoidAlgebra R C)
          (projectedLeftRight b v w) := by
    calc
      _ = Matrix.trace (σ.permMatrix R * T * P) :=
        (trace_mixed_matrix e u v w).symm
      _ = Matrix.trace (T₀ * B) := hmatrix
      _ = _ := by
        exact trace_local_mixed_matrix u v w b
  have hc := congrArg (IsotypicLattice.localizationToComplex d) htraceR
  rw [trace_projectedLeftRight, trace_projectedLeftRight, map_sum] at hc
  rw [map_sum] at hc
  rw [trace_projectedLeftRight, trace_projectedLeftRight]
  rw [← BlockOrthogonality.mapRingHom_localizedPrincipalBlockElement_eq_principalBlockElement
      d (IsotypicLattice.localizationToComplex d)
      (IsotypicLattice.localizationToComplex_algebraMap d)]
  rw [← CharacterwiseProjection.map_localPrincipalBlockElementInAmbientLocalization d C]
  change (∑ x : G, (IsotypicLattice.localizationToComplex d)
      ((BlockOrthogonality.localizedPrincipalBlockElement d).coeff
        (x⁻¹ * (u * (v : G))⁻¹ * x * (u * (w : G))))) =
    ∑ x : C, (IsotypicLattice.localizationToComplex d)
      ((localPrincipalBlockElementInAmbientLocalization d C).coeff
        (x⁻¹ * v⁻¹ * x * w))
  exact hc

 /-- Odd-core elements satisfy the coprimality hypotheses of the mixed trace
 comparison. -/
theorem principalBlock_mixed_trace_eq_of_pPrimeCore
    (d : PrincipalCongruenceBlockData G) (u : G)
    (hu : ∃ n : ℕ, u ^ (2 ^ n) = 1)
    (v w : pPrimeCore 2 (Subgroup.centralizer ({u} : Set G))) :
    LinearMap.trace ℂ (MonoidAlgebra ℂ G)
        (projectedLeftRight (BlockOrthogonality.principalBlockElement d)
          (u * (v : G)) (u * (w : G))) =
      LinearMap.trace ℂ
        (MonoidAlgebra ℂ (Subgroup.centralizer ({u} : Set G)))
        (projectedLeftRight
          (BlockOrthogonality.principalBlockElement (localData d
            (Subgroup.centralizer ({u} : Set G)))) v w) := by
  let C := Subgroup.centralizer ({u} : Set G)
  apply principalBlock_mixed_trace_eq d u hu (v : C) (w : C)
  · have h := Nat.Coprime.of_dvd_right
      (Subgroup.orderOf_dvd_natCard (pPrimeCore 2 C) v.property)
      (pPrimeCore_coprime_card (p := 2) (G := C))
    simpa only [Subgroup.orderOf_coe] using h
  · have h := Nat.Coprime.of_dvd_right
      (Subgroup.orderOf_dvd_natCard (pPrimeCore 2 C) w.property)
      (pPrimeCore_coprime_card (p := 2) (G := C))
    simpa only [Subgroup.orderOf_coe] using h

end ModularBlock.MixedBrauerTrace
