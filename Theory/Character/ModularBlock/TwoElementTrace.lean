module

public import Theory.Character.ModularBlock.InvolutionRootTrace

/-!
# Principal-block traces on roots of two-elements

For a two-element `y`, the compatible principal selector of `C(y)` acting
on the left and the ambient principal selector acting on the right have
the same mixed trace on cyclic roots of `y` in `C(y)`.

The fixed-index argument of `InvolutionRootTrace` works for arbitrary
two-power order: if `y` is a power of `a`, it is a power of the two-part
of `a`, since powering by the order of the odd part is invertible on
`⟨y⟩`. Quotients of fixed indices therefore centralize `y` itself.
Principal Brauer equality identifies the reduced matrix entries, and the
integral fixed-index trace comparison gives equality before reduction.

Source: Alperin--Brauer--Gorenstein, III.5--6; Fong (1967), pp.73--74.
This extends the existing involution-root proof without changing its API.
-/

public section
noncomputable section
open scoped BigOperators
namespace ModularBlock.TwoElementTrace
open PrincipalBlockConstruction BrauerBlockReduction BlockOrthogonality
open BrauerConjugationTrace MixedBrauerTrace MixedConjugationTrace InvolutionRootTrace
attribute [local instance] Fintype.ofFinite
variable {G R : Type*} [Group G] [Finite G] [CommRing R]

private theorem leftRightPerm_factor [DecidableEq G] (t v s w : G) :
    (leftRightPerm (t * v) (s * w)).permMatrix R =
      (leftRightPerm t s).permMatrix R * (leftRightPerm v w).permMatrix R := by
  rw [← Matrix.permMatrix_mul]
  congr 1
  ext z
  simp only [Equiv.Perm.mul_apply, leftRightPerm_apply, mul_inv_rev]
  group

omit [Finite G] in
private theorem leftRightPerm_commute (t v s w : G) (ht : Commute t v) (hs : Commute s w) :
    Commute (leftRightPerm t s) (leftRightPerm v w) := by
  change _ * _ = _ * _
  ext z
  simp only [Equiv.Perm.mul_apply, leftRightPerm_apply]
  calc
    _ = (t⁻¹ * v⁻¹) * z * (w * s) := by group
    _ = (v⁻¹ * t⁻¹) * z * (s * w) := by rw [ht.inv_inv.eq, hs.eq]
    _ = _ := by group

private theorem twoElement_mem_zpowers_twoPart (x a t v : G)
    (hx : ∃ n : ℕ, x ^ (2 ^ n) = 1) (hxa : x ∈ Subgroup.zpowers a)
    (hv : ¬ 2 ∣ orderOf v) (htv : Commute t v) (ha : t * v = a) :
    x ∈ Subgroup.zpowers t := by
  obtain ⟨j, hj⟩ := (show ∃ j : ℕ, a ^ j = x from
    mem_powers_iff_mem_zpowers.mpr hxa)
  have hc : (orderOf v).Coprime (orderOf x) := by
    obtain ⟨n, hn⟩ := hx
    exact ((Nat.prime_two.coprime_iff_not_dvd.mpr hv).symm.pow_right n).of_dvd_right
      (orderOf_dvd_of_pow_eq_one hn)
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime (x := x) hc
  have hm : x ^ orderOf v ∈ Subgroup.zpowers t := by
    rw [← hj, ← pow_mul, Nat.mul_comm j _, pow_mul, ← ha,
      htv.mul_pow, pow_orderOf_eq_one, mul_one]
    exact pow_mem (pow_mem (Subgroup.mem_zpowers t) _) _
  rw [← hk]
  exact pow_mem hm k

omit [Finite G] in
private theorem subtypeMap_commute (H : Subgroup G) (b : MonoidAlgebra R H)
    (hb : b ∈ Set.center (MonoidAlgebra R H)) (a : H) :
    Commute (MonoidAlgebra.of R G (a : G))
      (MonoidAlgebra.mapDomainRingHom R H.subtype b) := by
  have h : Commute (MonoidAlgebra.of R H a) b :=
    Semigroup.mem_center_iff.mp hb _
  simpa [MonoidAlgebra.of_apply] using
    h.map (MonoidAlgebra.mapDomainRingHom R H.subtype)

omit [Finite G] in
private theorem fixed_quotient_mem_centralizer (t s p q : G)
    (hp : leftRightPerm t s p = p) (hq : leftRightPerm t s q = q) :
    p * q⁻¹ ∈ Subgroup.centralizer ({t} : Set G) := by
  have he (r : G) (hr : leftRightPerm t s r = r) : t * r = r * s := by
    have h := congrArg (fun z => t * z) hr
    simpa only [leftRightPerm_apply, ← mul_assoc, mul_inv_cancel, one_mul] using h.symm
  have hq' : t = q * s * q⁻¹ := by rw [← he q hq]; group
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  calc
    (p * q⁻¹) * t = (p * q⁻¹) * (q * s * q⁻¹) := by rw [← hq']
    _ = (p * s) * q⁻¹ := by group
    _ = t * (p * q⁻¹) := by rw [← he p hp, mul_assoc]

private theorem fixed_reduction_eq [DecidableEq G]
    (d : PrincipalCongruenceBlockData G) (x t s : G)
    (hx : ∃ n : ℕ, x ^ (2 ^ n) = 1) (hxt : x ∈ Subgroup.zpowers t) :
    ((localizationToResidue d).mapMatrix
      (leftMatrix (NagaoComplement.centralizerSubtypeMap x
        (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization d
          (Subgroup.centralizer ({x} : Set G)))))).submatrix
      (fun p : {p // leftRightPerm t s p = p} => p.val)
      (fun p : {p // leftRightPerm t s p = p} => p.val) =
    ((localizationToResidue d).mapMatrix (rightMatrix (localizedPrincipalBlockElement d))).submatrix
      (fun p : {p // leftRightPerm t s p = p} => p.val)
      (fun p : {p // leftRightPerm t s p = p} => p.val) := by
  ext p q
  have ht : Commute (p.val * q.val⁻¹) t :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (fixed_quotient_mem_centralizer t s p.val q.val p.property q.property)
  have hcx : p.val * q.val⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxt
    exact Subgroup.mem_centralizer_singleton_iff.mpr (ht.zpow_right j).eq
  let r : Subgroup.centralizer ({x} : Set G) := ⟨p.val * q.val⁻¹, hcx⟩
  have hcoeff : (NagaoComplement.centralizerSubtypeMap x
        (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization d
          (Subgroup.centralizer ({x} : Set G)))).coeff (r : G) =
      (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization d
          (Subgroup.centralizer ({x} : Set G))).coeff r := by
    exact Finsupp.mapDomain_apply Subtype.val_injective _ r
  change localizationToResidue d ((NagaoComplement.centralizerSubtypeMap x
    (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization d
      (Subgroup.centralizer ({x} : Set G)))).coeff (p.val * q.val⁻¹)) =
    localizationToResidue d ((localizedPrincipalBlockElement d).coeff (q.val⁻¹ * p.val))
  rw [show p.val * q.val⁻¹ = (r : G) from rfl, hcoeff,
    LocalColumnNorm.localPrincipalBlock_localization_coeff_reduce d x hx r]
  congr 1
  have hc := CentralIdempotentSupport.coeff_conj_eq_of_mem_center
    (localizedPrincipalBlockElement d) (localizedPrincipalBlockElement_mem_center d)
    q.val (q.val⁻¹ * p.val)
  simpa only [r, mul_assoc, mul_inv_cancel_left] using hc

/-- Integral local-left and ambient-right principal-block traces agree on cyclic roots of a two-element,
for every prescribed modular place. -/
theorem integral_root_trace
    (d : PrincipalCongruenceBlockData G) (x : G) (hx : ∃ n : ℕ, x ^ (2 ^ n) = 1)
    (a : Subgroup.centralizer ({x} : Set G)) (hxa : x ∈ Subgroup.zpowers (a : G))
    (g : G) :
    let R := Localization.AtPrime d.primeIdeal
    let E := localizedPrincipalBlockElement d
    let B := NagaoComplement.centralizerSubtypeMap x
      (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization d
        (Subgroup.centralizer ({x} : Set G)))
    LinearMap.trace R (MonoidAlgebra R G)
      ((LinearMap.mulLeft R (MonoidAlgebra.of R G (a : G) * B)).comp
        (LinearMap.mulRight R (MonoidAlgebra.of R G g⁻¹))) =
    LinearMap.trace R (MonoidAlgebra R G) (projectedLeftRight E (a : G) g) := by
  classical
  let R := Localization.AtPrime d.primeIdeal
  let : Field (principalResidueField d) := Ideal.Quotient.field d.primeIdeal
  let C := Subgroup.centralizer ({x} : Set G)
  let b := CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization d C
  let B := NagaoComplement.centralizerSubtypeMap x b
  let E := localizedPrincipalBlockElement d
  obtain ⟨t, v, ⟨nt, ht⟩, hv, htv, ha⟩ := exists_commuting_prime_parts 2 Nat.prime_two a
  obtain ⟨s, w, ⟨ns, hs⟩, hw, hsw, hg⟩ := exists_commuting_prime_parts 2 Nat.prime_two g
  have htvG : Commute (t : G) (v : G) := htv.map C.subtype
  have haG : (t : G) * (v : G) = (a : G) := congrArg Subtype.val ha
  have hvG : ¬ 2 ∣ orderOf (v : G) := by simpa only [Subgroup.orderOf_coe] using hv
  have hxt := twoElement_mem_zpowers_twoPart x (a : G) (t : G) (v : G)
    hx hxa hvG htvG haG
  let σ := leftRightPerm (t : G) s
  let τ := leftRightPerm (v : G) w
  have hσ : σ ^ (2 ^ (nt + ns)) = 1 := by
    apply leftRightPerm_pow_eq_one
    · have htG : (t : G) ^ (2 ^ nt) = 1 := congrArg Subtype.val ht
      rw [pow_add, pow_mul, htG, one_pow]
    · rw [Nat.add_comm nt ns, pow_add, pow_mul, hs, one_pow]
  have hτ : (τ.permMatrix R) ^ Nat.lcm (orderOf (v : G)) (orderOf w) = 1 := by
    rw [← Matrix.permMatrix_pow, leftRightPerm_lcm_pow_eq_one, Matrix.permMatrix_one]
  have hsurj : Function.Surjective (localizationToResidue d) := by
    intro z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨algebraMap _ R r, localizationToResidue_algebraMap d r⟩
  have hf (r : R) (hr : localizationToResidue d r ≠ 0) : IsUnit r := by
    by_contra hn
    exact hr ((BlockPrimitivity.localizationToResidue_eq_zero_iff_not_isUnit d r).mpr hn)
  have hB : IsIdempotentElem B :=
    (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization_isIdempotent d C).map
      (NagaoComplement.centralizerSubtypeMap x)
  have hc (z : C) : Commute (MonoidAlgebra.of R G (z : G)) B :=
    subtypeMap_commute C b
      (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization_mem_center d C) z
  have hE := localizedPrincipalBlockElement_mem_center d
  have hodd := leftRight_lcm_coprime (v : G) w
    (Nat.prime_two.coprime_iff_not_dvd.mpr hvG)
    (Nat.prime_two.coprime_iff_not_dvd.mpr hw)
  obtain ⟨ζ, hζ⟩ := exists_localization_primitiveRoot d _ (leftRight_lcm_dvd_card (v : G) w)
  have hn : Nat.lcm (orderOf (v : G)) (orderOf w) ≠ 0 :=
    (Nat.lcm_pos (orderOf_pos _) (orderOf_pos _)).ne'
  have hfix := fixed_reduction_eq d x (t : G) s hx hxt
  have htrace := Matrix.trace_permMatrix_mul_mul_eq_of_fixed_reduction_eq
    (localizationToResidue d) hsurj hf σ hσ (τ.permMatrix R)
    (leftMatrix B) (rightMatrix E) (leftMatrix_isIdempotent B hB)
    (rightMatrix_isIdempotent E (localizedPrincipalBlockElement_isIdempotent d))
    (leftMatrix_commute_rightMatrix B E)
    (leftMatrix_commute_leftRight B (t : G) s (hc t))
    (rightMatrix_commute_leftRight E hE (t : G) s)
    (leftMatrix_commute_leftRight B (v : G) w (hc v))
    (rightMatrix_commute_leftRight E hE (v : G) w)
    (Matrix.permMatrix_commute (leftRightPerm_commute _ _ _ _ htvG hsw))
    hfix hn hτ (isUnit_natCast_localization d _ hodd) ζ hζ
  change Matrix.trace ((leftRightPerm (t : G) s).permMatrix R *
      (leftRightPerm (v : G) w).permMatrix R * leftMatrix B) =
    Matrix.trace ((leftRightPerm (t : G) s).permMatrix R *
      (leftRightPerm (v : G) w).permMatrix R * rightMatrix E) at htrace
  rw [← leftRightPerm_factor, haG, hg, trace_permMatrix_mul_leftMatrix,
    MixedBrauerTrace.trace_permMatrix_mul_rightMatrix] at htrace
  exact htrace

/-- Complex coefficient extension identifies the local-left and ambient-right principal-block
traces on cyclic roots of a two-element. -/
theorem complex_root_trace
    (d : PrincipalCongruenceBlockData G) (x : G) (hx : ∃ n : ℕ, x ^ (2 ^ n) = 1)
    (a : Subgroup.centralizer ({x} : Set G)) (hxa : x ∈ Subgroup.zpowers (a : G))
    (g : G) :
    let C := Subgroup.centralizer ({x} : Set G)
    let B := MonoidAlgebra.mapDomainRingHom ℂ C.subtype
      (principalBlockElement (CompatibleBrauerBlock.localData d C))
    LinearMap.trace ℂ (MonoidAlgebra ℂ G)
      ((LinearMap.mulLeft ℂ (MonoidAlgebra.of ℂ G (a : G) * B)).comp
        (LinearMap.mulRight ℂ (MonoidAlgebra.of ℂ G g⁻¹))) =
    LinearMap.trace ℂ (MonoidAlgebra ℂ G)
      (projectedLeftRight (principalBlockElement d) (a : G) g) := by
  have h := congrArg (IsotypicLattice.localizationToComplex d)
    (integral_root_trace d x hx a hxa g)
  dsimp only at h ⊢
  rw [trace_mulLeft_comp_mulRight, trace_projectedLeftRight, map_sum, map_sum] at h
  change LinearMap.trace ℂ (MonoidAlgebra ℂ G)
      ((LinearMap.mulLeft ℂ (MonoidAlgebra.of ℂ G (a : G) *
        NagaoComplement.centralizerSubtypeMap x
          (principalBlockElement (CompatibleBrauerBlock.localData d
            (Subgroup.centralizer ({x} : Set G)))))).comp
        (LinearMap.mulRight ℂ (MonoidAlgebra.of ℂ G g⁻¹))) = _
  rw [← CharacterwiseProjection.map_localPrincipalBlockElementInAmbientLocalization d,
    ← NagaoComplement.mapRingHom_centralizerSubtypeMap,
    ← mapRingHom_localizedPrincipalBlockElement_eq_principalBlockElement d
      (IsotypicLattice.localizationToComplex d) (IsotypicLattice.localizationToComplex_algebraMap d),
    trace_mulLeft_comp_mulRight, trace_projectedLeftRight]
  simpa only [MonoidAlgebra.coeff_mapRingHom] using h

end ModularBlock.TwoElementTrace
