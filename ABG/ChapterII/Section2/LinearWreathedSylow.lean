module
public import ABG.ChapterII.Section2.MonomialWreathedModel
public import ABG.ChapterII.Section2.SylowShapeTransport
public import GorensteinWalter.GL2DeterminantCard

/-!
# The actual linear wreathed Sylow subgroup

Let 2^n, with n at least two, be the exact two-part of |F|-1 for a finite
field F. The actual determinant level n contains a Sylow two-subgroup
with the source wreathed presentation of height n. The image of its center
through the subgroup inclusions into GL2 lies in the actual GL2 center.

Choose a generator of the group of 2^n-th roots of unity. The shared
diagonal-and-swap subgroup has order 2^(2n+1), the required presentation
and scalar center. Its generator determinants lie in the specified level.
Writing |F|-1=2^n*d with odd d, the determinant-level cardinal formula
shows its index is |F|*d*(|F|+1)/2, an odd number since |F| is one modulo
four. Hence the actual subgroup is Sylow. Subgroup restriction transports
the presentation and center image without changing the matrix model.

This proves the linear wreathed case of ABG II.2 Lemma1(i),(ii), article
p17, for use in II.3 Proposition3. The determinant-defined ambient group,
the specified height and the actual central image are all retained; no
abstract group recognition or assumed Sylow shape is used.
-/

namespace ABG
open Matrix.GeneralLinearGroup

private theorem odd_linear_index (q n i : ℕ) (hq : 1 < q) (hn : 2 ≤ n)
    (hd : 2 ^ n ∣ q - 1) (hodd : Odd ((q - 1) / 2 ^ n))
    (hc : 2 ^ (2 * n + 1) * i = 2 ^ n * q * (q ^ 2 - 1)) : Odd i := by
  let d := (q - 1) / 2 ^ n
  let a := 2 ^ (n - 2) * d
  have hqm1 : q - 1 = 2 ^ n * d := (Nat.mul_div_cancel' hd).symm
  have hpn : 2 ^ n = 4 * 2 ^ (n - 2) := by
    calc
      2 ^ n = 2 ^ ((n - 2) + 2) := by rw [Nat.sub_add_cancel hn]
      _ = _ := by rw [pow_add]; ring
  have hqeq : q = 4 * a + 1 := by
    calc
      q = (q - 1) + 1 := by omega
      _ = 2 ^ n * d + 1 := by rw [hqm1]
      _ = 4 * a + 1 := by rw [hpn]; dsimp [a]; ring
  have hqp1 : q + 1 = 2 * (2 * a + 1) := by omega
  have hpcount : 2 ^ (2 * n + 1) = 2 * (2 ^ n) ^ 2 := by
    rw [pow_add, pow_one, show 2 * n = n * 2 by omega, pow_mul]
    ring
  have hsq : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    simpa using Nat.sq_sub_sq q 1
  have hfactor : 2 ^ n * q * (q ^ 2 - 1) =
      2 ^ (2 * n + 1) * (q * d * (2 * a + 1)) := by
    rw [hsq, hqm1, hqp1, hpcount]
    ring
  have hi : i = q * d * (2 * a + 1) :=
    Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0 < 2) _) (hc.trans hfactor)
  rw [hi]
  have hqodd : Odd q := ⟨2 * a, by omega⟩
  exact (hqodd.mul hodd).mul ⟨a, by omega⟩

public theorem determinantTwoPower_wreathed_sylow
    (F : Type*) [Field F] [Finite F] (n : ℕ) (hn : 2 ≤ n)
    (hd : 2 ^ n ∣ Nat.card F - 1) (hodd : Odd ((Nat.card F - 1) / 2 ^ n)) :
    ∃ S : Sylow 2 (determinantTwoPower F n),
      IsWreathedOfHeight S n ∧
        (Subgroup.center S).map ((determinantTwoPower F n).subtype.comp (S : Subgroup _).subtype) ≤
          Subgroup.center (GL (Fin 2) F) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A := rootsOfUnity (2 ^ n) F
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := A)
  let ζ : Fˣ := a.val
  have hζorder : orderOf ζ = 2 ^ n := by
    rw [show orderOf ζ = orderOf a from Subgroup.orderOf_coe a, ha]
    exact FiniteField.card_rootsOfUnity_of_dvd F (2 ^ n) hd
  have hζpow : ζ ^ (2 ^ n) = 1 := by
    rw [← hζorder]
    exact pow_orderOf_eq_one ζ
  let W := diagonalSwapSubgroup F ζ
  let D := determinantTwoPower F n
  have hdiagdet (b c : Fˣ) : det (diagonalPair F (b,c)) = b * c := by
    apply Units.ext
    change (diagonalPair F (b,c)).val.det = (b : F) * (c : F)
    simp [diagonalPair_val, Matrix.det_fin_two]
  have hswapdet : det (coordinateSwap F) = (-1 : Fˣ) := by
    apply Units.ext
    change (coordinateSwap F).val.det = (-1 : F)
    simp [coordinateSwap_val, Matrix.det_fin_two]
  have hWD : W ≤ D := by
    change Subgroup.closure {diagonalPair F (ζ,1), diagonalPair F (1,ζ), coordinateSwap F} ≤ D
    rw [Subgroup.closure_le]
    intro B hB
    rcases (by simpa using hB : B = diagonalPair F (ζ,1) ∨
      B = diagonalPair F (1,ζ) ∨ B = coordinateSwap F) with rfl | rfl | rfl
    · change det (diagonalPair F (ζ,1)) ^ (2 ^ n) = 1
      rw [hdiagdet, mul_one]
      exact hζpow
    · change det (diagonalPair F (1,ζ)) ^ (2 ^ n) = 1
      rw [hdiagdet, one_mul]
      exact hζpow
    · change det (coordinateSwap F) ^ (2 ^ n) = 1
      rw [hswapdet]
      exact (show Even (2 ^ n) from Nat.even_pow.mpr ⟨by decide, by omega⟩).neg_one_pow
  let P := W.subgroupOf D
  let e : P ≃* W := Subgroup.subgroupOfEquivOfLe hWD
  have hcardP : Nat.card P = 2 ^ (2 * n + 1) := by
    rw [Nat.card_congr e.toEquiv, diagonalSwapSubgroup_card, hζorder]
    simp only [← pow_mul, pow_add, pow_one, Nat.mul_comm]
  have hPgroup : IsPGroup 2 P := IsPGroup.of_card hcardP
  have hPindex : Odd P.index := by
    apply odd_linear_index (Nat.card F) n P.index Finite.one_lt_card hn hd hodd
    have hh := P.card_mul_index
    rw [hcardP, determinantTwoPower_card F n hd] at hh
    exact hh
  let S := hPgroup.toSylow hPindex.not_two_dvd_nat
  let eS : S ≃* W := e
  obtain ⟨hW, hWcenter⟩ := diagonalSwap_wreathed_model F ζ n hn hζorder
  refine ⟨S, wreathed_equiv eS.symm hW, ?_⟩
  rintro B ⟨x, hx, rfl⟩
  have hex : eS x ∈ Subgroup.center W := by
    have hx' : ∀ y : S, y * x = x * y := Subgroup.mem_center_iff.mp hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨y, rfl⟩ := eS.surjective y
    simpa only [map_mul] using congrArg eS (hx' y)
  exact hWcenter (Subgroup.mem_map.mpr ⟨eS x, hex, rfl⟩)

end ABG

