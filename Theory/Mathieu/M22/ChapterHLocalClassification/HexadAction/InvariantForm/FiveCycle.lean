module

public import Theory.Mathieu.M22.ChapterHLocalClassification.HexadAction.InvariantForm.MatrixCertificate
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

/-!
# Normalizing order-five elements of GL₄(2)

The group order has five-part exactly five, so Sylow conjugacy sends each
order-five element to a nontrivial power of the cyclotomic companion matrix.
The explicit Frobenius matrix conjugates that companion to its square,
and hence makes all four nontrivial powers conjugate.

This supplies the change of basis for the invariant-form construction in
Aschbacher--Smith H.14.3(3), printed p.397.
-/

open scoped Pointwise
open Matrix Subgroup
namespace BinaryFourSymmetricForm
public abbrev GL4 := Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)
def D : Mat := !![1,0,1,0; 0,0,1,1; 0,1,1,0; 0,0,1,0]
@[expose] public def five : GL4 := ⟨C, C^4, by decide +kernel, by decide +kernel⟩
def frobenius : GL4 := ⟨D, D^3, by decide +kernel, by decide +kernel⟩
lemma five_order : orderOf five = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply Units.ext
    change C ^ 5 = 1
    decide +kernel
  · intro h
    have := congrArg (fun x : GL4 => x.val 0 0) h
    change (0 : ZMod 2) = 1 at this
    exact zero_ne_one this
lemma five_pow : five ^ 5 = 1 := by
  rw [← five_order]
  exact pow_orderOf_eq_one five
lemma frobenius_conj : frobenius * five * frobenius⁻¹ = five ^ 2 := by
  apply Units.ext
  change D * C * D ^ 3 = C ^ 2
  decide +kernel
lemma gl_card : Nat.card GL4 = 20160 := by
  rw [Matrix.card_GL_field]
  decide +kernel
private def fiveSylow (x : GL4) (hx : orderOf x = 5) : Sylow 5 GL4 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hc : Nat.card (zpowers x) = 5 := (Nat.card_zpowers x).trans hx
  refine ⟨zpowers x, IsPGroup.of_card (n := 1) hc, ?_⟩
  intro Q hQ hle
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hn1 : n ≤ 1 := by
    by_contra h
    have hd : 25 ∣ 20160 := (Nat.pow_dvd_pow 5 (by omega : 2 ≤ n)).trans
      (hn ▸ gl_card ▸ Q.card_subgroup_dvd_card)
    norm_num at hd
  exact (eq_of_le_of_card_ge hle (by
    rw [hc, hn]
    exact Nat.pow_le_pow_right (by decide) hn1)).symm
public theorem normalize_five (x : GL4) (hx : orderOf x = 5) :
    ∃ e : GL4, e * x * e⁻¹ = five := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨e, he⟩ := MulAction.exists_smul_eq GL4 (fiveSylow x hx) (fiveSylow five five_order)
  have hm : e * x * e⁻¹ ∈ zpowers five := by
    have hmem := Subgroup.smul_mem_pointwise_smul x (MulAut.conj e)
      (fiveSylow x hx : Subgroup GL4) (mem_zpowers x)
    change e * x * e⁻¹ ∈ e • fiveSylow x hx at hmem
    rw [he] at hmem
    exact hmem
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp
    ((isOfFinOrder_of_finite five).mem_zpowers_iff_mem_range_orderOf.mp hm)
  have hk5 : k < 5 := by simpa [five_order] using hk
  have hk0 : k ≠ 0 := by
    intro h
    have he1 : e * x * e⁻¹ = 1 := by simpa only [h, pow_zero] using heq.symm
    have hx1 : x = 1 := (MulAut.conj e).injective (he1.trans (map_one _).symm)
    rw [hx1, orderOf_one] at hx
    norm_num at hx
  have h2 : IsConj five (five ^ 2) := isConj_iff.mpr ⟨frobenius, frobenius_conj⟩
  have h4 : IsConj five (five ^ 4) := by
    have h := h2.pow 2
    rw [← pow_mul] at h
    exact h2.trans h
  have h3 : IsConj five (five ^ 3) := by
    have h := h4.pow 2
    rw [← pow_mul, show 4 * 2 = 5 + 3 from rfl, pow_add, five_pow, one_mul] at h
    exact h2.trans h
  have hp : IsConj (five ^ k) five := by
    interval_cases k
    · exact (hk0 rfl).elim
    · simpa using IsConj.refl five
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
  exact isConj_iff.mp ((isConj_iff.mpr ⟨e, heq.symm⟩).trans hp)
end BinaryFourSymmetricForm
