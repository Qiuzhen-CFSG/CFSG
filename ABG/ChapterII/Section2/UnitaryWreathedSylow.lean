module
public import ABG.ChapterII.Section2.MonomialWreathedModel
public import ABG.ChapterII.Section2.UnitaryLevelCard
public import ABG.ChapterII.Section2.UnitaryDiagonalSwap
public import ABG.ChapterII.Section2.SylowShapeTransport

/-!
# The actual unitary wreathed Sylow model

Let q=p^f with p odd and f nonzero, and let 2^r be the exact two-part of
q+1, with r at least two. The original determinant level SU2Level r has
a Sylow two subgroup of wreathed height r. Its center, mapped by the
actual subgroup inclusions, is central in the original GU2. This includes
the smallest unitary wreathed case q=3, r=2.

Choose a root of exact order 2^r in the quadratic field. The shared
actual diagonal-and-swap subgroup has the required wreathed presentation
and scalar center. Its proved Hermitian and determinant equations place
it in the unitary level. Restrict along the original inclusions to
transport the presentation and center. Its order is 2^(2r+1), while the
unitary level order is this power times q((q-1)/2)((q+1)/2^r), an odd
integer because q+1 is divisible by four and has exact two-part 2^r.
Thus the restricted two-subgroup is Sylow.

Source: ABG II.2 Lemma 1(i),(ii), article page 17, used for the actual
unitary matrix model in II.3 Proposition 3. This is the unitary wreathed
branch only; no abstract Sylow or ambient group recognition is assumed.
-/

namespace ABG
open Matrix.GeneralLinearGroup

private theorem sylow_from_unitary_root
    (p f : ℕ) [Fact p.Prime] (hp : Odd p) (hf : f ≠ 0)
    (r : ℕ) (hr : 2 ≤ r) (hd : 2 ^ r ∣ p ^ f + 1)
    (hodd : Odd ((p ^ f + 1) / 2 ^ r))
    (ζ : (GaloisField p (2 * f))ˣ) (horder : orderOf ζ = 2 ^ r) :
    ∃ S : Sylow 2 (SU2Level p f hf r), IsWreathedOfHeight S r ∧
      (Subgroup.center S).map ((SU2Level p f hf r).subtype.comp
        (S : Subgroup (SU2Level p f hf r)).subtype) ≤ Subgroup.center (GU2 p f hf) := by
  let F := GaloisField p (2 * f)
  let U := (unitaryForm 2 p f hf).unitarySubgroup
  let D := SU2Level p f hf r
  let W := diagonalSwapSubgroup F ζ
  have hWle := diagonalSwapSubgroup_le_unitaryDeterminant p f hf r (by omega) hd ζ
    (by rw [← horder]; exact pow_orderOf_eq_one ζ)
  have hWU : W ≤ U := hWle.trans inf_le_left
  let WU := W.subgroupOf U
  have hWD : WU ≤ D := by
    intro A hA
    exact (hWle hA).2
  let P := WU.subgroupOf D
  let e : P ≃* W := (Subgroup.subgroupOfEquivOfLe hWD).trans
    (Subgroup.subgroupOfEquivOfLe hWU)
  obtain ⟨hwreath, hcenter⟩ := diagonalSwap_wreathed_model F ζ r hr horder
  have hPc : Nat.card P = 2 ^ (2 * r + 1) :=
    (Nat.card_congr e.toEquiv).trans hwreath.2.1
  have hqodd : Odd (p ^ f) := hp.pow
  have hq1 : 1 ≤ p ^ f := by have := Nat.odd_iff.mp hqodd; omega
  have h4 : 4 ∣ p ^ f + 1 := by
    have h := (pow_dvd_pow 2 hr).trans hd
    simpa using h
  have hminusodd : Odd ((p ^ f - 1) / 2) := by
    obtain ⟨k, hk⟩ := h4
    rw [Nat.odd_iff]
    omega
  have hminus : p ^ f - 1 = 2 * ((p ^ f - 1) / 2) := by
    have h := Nat.odd_iff.mp hqodd
    omega
  have hplus : p ^ f + 1 = 2 ^ r * ((p ^ f + 1) / 2 ^ r) :=
    (Nat.mul_div_cancel' hd).symm
  have hsq : (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) := by
    simpa only [one_pow, mul_comm] using Nat.sq_sub_sq (p ^ f) 1
  let b := p ^ f * ((p ^ f - 1) / 2) * ((p ^ f + 1) / 2 ^ r)
  have hb : Odd b := (hqodd.mul hminusodd).mul hodd
  have hDc : Nat.card D = 2 ^ (2 * r + 1) * b := by
    rw [SU2Level_card p f hp hf r hd, hsq, hminus, hplus]
    dsimp [b]
    rw [show 2 * r + 1 = r * 2 + 1 by omega, pow_add, pow_mul]
    ring
  have hindex : P.index = b := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0 < 2) (2 * r + 1))
    rw [← hPc, Subgroup.card_mul_index, hDc, hPc]
  let S : Sylow 2 D := (IsPGroup.of_card hPc).toSylow (by
    rw [hindex]
    exact hb.not_two_dvd_nat)
  let eS : S ≃* W := e
  refine ⟨S, wreathed_equiv eS.symm hwreath, ?_⟩
  rintro x ⟨c, hc, rfl⟩
  have hcW : eS c ∈ Subgroup.center W := by
    apply Subgroup.mem_center_iff.mpr
    intro w
    obtain ⟨a, rfl⟩ := eS.surjective w
    simpa only [map_mul] using congrArg eS ((Subgroup.mem_center_iff.mp hc) a)
  have hcGL := hcenter (show (eS c).val ∈ (Subgroup.center W).map W.subtype from
    ⟨eS c, hcW, rfl⟩)
  apply Subgroup.mem_center_iff.mpr
  intro A
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp hcGL A.val

public theorem SU2Level_wreathed_sylow
    (p f : ℕ) [Fact p.Prime] (hp : Odd p) (hf : f ≠ 0)
    (r : ℕ) (hr : 2 ≤ r) (hd : 2 ^ r ∣ p ^ f + 1)
    (hodd : Odd ((p ^ f + 1) / 2 ^ r)) :
    ∃ S : Sylow 2 (SU2Level p f hf r), IsWreathedOfHeight S r ∧
      (Subgroup.center S).map ((SU2Level p f hf r).subtype.comp
        (S : Subgroup (SU2Level p f hf r)).subtype) ≤ Subgroup.center (GU2 p f hf) := by
  let F := GaloisField p (2 * f)
  have hcard : Nat.card F = (p ^ f) ^ 2 := by
    rw [GaloisField.card p (2 * f) (Nat.mul_ne_zero (by decide) hf),
      ← pow_mul, Nat.mul_comm f 2]
  have hdivq : p ^ f + 1 ∣ Nat.card F - 1 := by
    rw [hcard]
    exact ⟨p ^ f - 1, by simpa only [one_pow] using Nat.sq_sub_sq (p ^ f) 1⟩
  let A := rootsOfUnity (2 ^ r) F
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := A)
  have horder : orderOf a.val = 2 ^ r := by
    rw [Subgroup.orderOf_coe, ha]
    exact FiniteField.card_rootsOfUnity_of_dvd F (2 ^ r) (hd.trans hdivq)
  exact sylow_from_unitary_root p f hp hf r hr hd hodd a.val horder

end ABG

