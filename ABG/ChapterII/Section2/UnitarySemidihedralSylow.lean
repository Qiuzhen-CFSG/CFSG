module
public import ABG.ChapterII.Section2.UnitaryHyperbolicTorus
public import ABG.ChapterII.Section2.UnitaryLevelCard
public import ABG.ChapterII.Section2.UnitaryDeterminantNorm
public import ABG.ChapterII.Section1.SemidihedralGenerators
public import ABG.ChapterII.Section2.QuasiFrameTransport

/-!
# The actual semidihedral Sylow in the unitary sign level

Let q=p^d for odd p, and suppose q-1 has exact two-part 2^n with n≥2.
The original subgroup SU2Level 1 has a semidihedral Sylow two-subgroup of
order 2^(n+2). Its center, mapped by the actual subgroup inclusions, lies
in the center of the original GU2. The smallest case is q=5.

Choose a unit of order 2^(n+1) in GF(q²) and use the proved hyperbolic
torus and its external reflection. The inverse-q action becomes exponent
2^n-1 because q-1=2^n times an odd integer. The primitive-root power theorem
identifies its half-power with -1, whose torus image is the actual scalar -I.
The shared generator theorem supplies the subgroup's semidihedral shape,
order, and center. Its determinants have two-power order dividing q+1;
since four divides q-1, they have order at most two. Thus the subgroup
lies in SU2Level 1. Restriction along the actual inclusion preserves its
shape and center, and the exact unitary level cardinality gives odd index,
proving that it is Sylow.

Source: Alperin–Brauer–Gorenstein II.2 Lemma 1(i),(ii), article p.17,
used in II.3 Proposition 3's matrix model comparison. The parameter n
controls the rotation order; the unrestricted wreathed-or-semidihedral
choice remains a separate assembly. No abstract unitary recognition or
assumed Sylow shape enters this construction.
-/

namespace ABG
open Matrix.GeneralLinearGroup

private theorem unitary_semidihedral_generators
    (p d : ℕ) [Fact p.Prime] (hp : Odd p) (hd : d ≠ 0)
    (n : ℕ) (hdiv : 2 ^ n ∣ p ^ d - 1)
    (hodd : Odd ((p ^ d - 1) / 2 ^ n)) :
    ∃ a w : GU2 p d hd,
      orderOf a = 2 ^ (n + 1) ∧ w ^ 2 = 1 ∧ w ∉ Subgroup.zpowers a ∧
      w * a * w⁻¹ = a ^ (2 ^ n - 1) ∧
      (a ^ (2 ^ n)).val = scalar (Fin 2) (-1 : (GaloisField p (2 * d))ˣ) := by
  let E := GaloisField p (2 * d)
  let q := p ^ d
  have hq : Odd q := hp.pow
  have hqpos : 1 ≤ q := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have hc : Nat.card E = q ^ 2 := by
    rw [GaloisField.card p (2 * d) (Nat.mul_ne_zero (by decide) hd),
      ← pow_mul, Nat.mul_comm d 2]
  have hdivE : 2 ^ (n + 1) ∣ Nat.card E - 1 := by
    rw [hc, show q ^ 2 - 1 = (q - 1) * (q + 1) by
      simpa only [one_pow, mul_comm] using Nat.sq_sub_sq q 1, pow_succ]
    exact Nat.mul_dvd_mul hdiv
      (even_iff_two_dvd.mp (Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr hq)))
  obtain ⟨ρ, w, hi, hw, hout, hconj, hscalar⟩ := exists_unitary_hyperbolic_torus p d hp hd
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Eˣ)
  have hdu : 2 ^ (n + 1) ∣ orderOf u := by rw [hu, Nat.card_units]; exact hdivE
  let ζ := u ^ (orderOf u / 2 ^ (n + 1))
  have hζ : orderOf ζ = 2 ^ (n + 1) :=
    orderOf_pow_orderOf_div (orderOf_pos u).ne' hdu
  have hhalf : ζ ^ (2 ^ n) = -1 := by
    have hprim : IsPrimitiveRoot (ζ : E) (2 ^ (n + 1)) := by
      rw [← hζ, ← orderOf_units]
      exact IsPrimitiveRoot.orderOf _
    exact Units.ext ((IsPrimitiveRoot.pow (by positivity) hprim (pow_succ 2 n)).eq_neg_one_of_two_right)
  have hinv : (ζ ^ q)⁻¹ = ζ ^ (2 ^ n - 1) := by
    obtain ⟨k, hk⟩ := hodd
    have hrep : q - 1 = 2 ^ n * (2 * k + 1) := by
      rw [← hk]
      exact (Nat.mul_div_cancel' hdiv).symm
    have hexp : q + (2 ^ n - 1) = 2 ^ (n + 1) * (k + 1) := by
      rw [pow_succ]
      have hpow : 0 < 2 ^ n := by positivity
      nlinarith only [hrep, Nat.sub_add_cancel hqpos,
        Nat.sub_add_cancel (show 1 ≤ 2 ^ n by omega)]
    apply inv_injective
    rw [inv_inv]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_add, hexp, pow_mul, ← hζ, pow_orderOf_eq_one, one_pow]
  refine ⟨ρ ζ, w, (orderOf_injective ρ hi ζ).trans hζ, hw, ?_, ?_, ?_⟩
  · intro h
    exact hout ((Subgroup.zpowers_le.mpr (show ρ ζ ∈ ρ.range from ⟨ζ, rfl⟩)) h)
  · rw [hconj, ← map_pow]
    exact congrArg ρ hinv
  · rw [← map_pow, hhalf]
    apply hscalar
    exact Even.neg_one_pow (Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr hq))

private theorem unitary_two_subgroup_le_sign_level
    (p d : ℕ) [Fact p.Prime] (hd : d ≠ 0) (h4 : 4 ∣ p ^ d - 1)
    (T : Subgroup (GU2 p d hd)) (hT : IsPGroup 2 T) :
    T ≤ SU2Level p d hd 1 := by
  intro a ha
  rw [mem_SU2Level_iff_orderOf_dvd, pow_one]
  obtain ⟨k, hk⟩ := hT.exists_orderOf_dvd_pow (⟨a, ha⟩ : T)
  let detU := (det : GL (Fin 2) (GaloisField p (2 * d)) →*
    (GaloisField p (2 * d))ˣ).comp (unitaryForm 2 p d hd).unitarySubgroup.subtype
  have hod : orderOf (det a.val) ∣ 2 ^ k :=
    (orderOf_map_dvd detU a).trans (by simpa using hk)
  obtain ⟨j, _, heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hod
  rw [heq]
  by_cases hj : j ≤ 1
  · simpa using Nat.pow_dvd_pow 2 hj
  · have h4plus : 4 ∣ p ^ d + 1 :=
      (show 4 ∣ 2 ^ j by simpa using Nat.pow_dvd_pow 2 (by omega : 2 ≤ j)).trans
        (heq ▸ GU2_det_orderOf_dvd p d hd a)
    have hqpos : 0 < p ^ d := pow_pos (Fact.out : p.Prime).pos _
    omega

/-- The genuine unitary determinant-sign level has the prescribed
semidihedral Sylow subgroup with center central in the original GU2. -/
public theorem SU2Level_semidihedral_sylow
    (p d : ℕ) [Fact p.Prime] (hp : Odd p) (hd : d ≠ 0)
    (n : ℕ) (hn : 2 ≤ n) (hdiv : 2 ^ n ∣ p ^ d - 1)
    (hodd : Odd ((p ^ d - 1) / 2 ^ n)) :
    ∃ S : Sylow 2 (SU2Level p d hd 1),
      Nat.card S = 2 ^ (n + 2) ∧ Stellmacher.IsSemidihedralGroup S ∧
      (Subgroup.center S).map ((SU2Level p d hd 1).subtype.comp
        (S : Subgroup _).subtype) ≤ Subgroup.center (GU2 p d hd) := by
  let D := SU2Level p d hd 1
  obtain ⟨a, w, ha, hw, hout, hconj, hscalar⟩ :=
    unitary_semidihedral_generators p d hp hd n hdiv hodd
  let T := Subgroup.zpowers a ⊔ Subgroup.zpowers w
  obtain ⟨hTcard, hTshape, hTcenter⟩ :=
    semidihedral_generated_subgroup_data hn a w ha hw hout hconj
  have hT2 : IsPGroup 2 T := IsPGroup.of_card hTcard
  have h4 : 4 ∣ p ^ d - 1 :=
    (show 4 ∣ 2 ^ n by simpa using Nat.pow_dvd_pow 2 hn).trans hdiv
  have hTD : T ≤ D := unitary_two_subgroup_le_sign_level p d hd h4 T hT2
  let R := T.subgroupOf D
  let e : R ≃* T := Subgroup.subgroupOfEquivOfLe hTD
  have hRc : Nat.card R = 2 ^ (n + 2) := (Nat.card_congr e.toEquiv).trans hTcard
  have hR2 : IsPGroup 2 R := hT2.of_equiv e.symm
  have hqodd : Odd (p ^ d) := hp.pow
  have hplusodd : Odd ((p ^ d + 1) / 2) := by
    obtain ⟨k, hk⟩ := h4
    rw [Nat.odd_iff]
    have hqpos : 0 < p ^ d := pow_pos (Fact.out : p.Prime).pos _
    omega
  have hplus : p ^ d + 1 = 2 * ((p ^ d + 1) / 2) := by
    have := Nat.odd_iff.mp hqodd
    omega
  have hminus : p ^ d - 1 = 2 ^ n * ((p ^ d - 1) / 2 ^ n) :=
    (Nat.mul_div_cancel' hdiv).symm
  let b := p ^ d * ((p ^ d - 1) / 2 ^ n) * ((p ^ d + 1) / 2)
  have hb : Odd b := (hqodd.mul hodd).mul hplusodd
  have hDc : Nat.card D = 2 ^ (n + 2) * b := by
    have hd1 : 2 ^ 1 ∣ p ^ d + 1 := by rw [pow_one]; exact ⟨_, hplus⟩
    have hsq : (p ^ d) ^ 2 - 1 = (p ^ d - 1) * (p ^ d + 1) := by
      simpa only [one_pow, mul_comm] using Nat.sq_sub_sq (p ^ d) 1
    rw [SU2Level_card p d hp hd 1 hd1, hsq, hminus, hplus]
    dsimp [b]
    rw [pow_add]
    ring
  have hindex : R.index = b := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0 < 2) (n + 2))
    rw [← hRc, Subgroup.card_mul_index, hDc, hRc]
  let S : Sylow 2 D := hR2.toSylow (by rw [hindex]; exact hb.not_two_dvd_nat)
  refine ⟨S, hRc, semidihedral_equiv e.symm hTshape, ?_⟩
  change (Subgroup.center R).map (D.subtype.comp R.subtype) ≤ _
  rintro x ⟨c, hc, rfl⟩
  have hcT : e c ∈ Subgroup.center T := by
    apply Subgroup.mem_center_iff.mpr
    intro t
    obtain ⟨b, rfl⟩ := e.surjective t
    change e b * e c = e c * e b
    rw [← e.map_mul, ← e.map_mul]
    exact congrArg e ((Subgroup.mem_center_iff.mp hc) b)
  have hcA : (e c).val ∈ Subgroup.zpowers (a ^ (2 ^ n)) := by
    rw [← hTcenter]
    exact ⟨e c, hcT, rfl⟩
  have hz : Subgroup.zpowers (a ^ (2 ^ n)) ≤ Subgroup.center (GU2 p d hd) := by
    apply Subgroup.zpowers_le.mpr
    apply Subgroup.mem_center_iff.mpr
    intro A
    apply Subtype.ext
    change A.val * (a ^ (2 ^ n)).val = (a ^ (2 ^ n)).val * A.val
    rw [hscalar]
    exact (scalar_commute _ _).symm
  exact hz hcA

end ABG

