module

public import Stellmacher.Recognition.ConversePSL2Prime
public import GorensteinWalter.LinearThreeEquiv
public import GorensteinWalter.LinearRingEquiv
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Data.Nat.Prime.Basic

/-!
# Minimal simplicity of PSL2 over odd powers of three

For an odd prime f, PSL2 over GaloisField 3 f is minimal simple. Dickson's
nine-case subgroup theorem shows that every proper subgroup is solvable.
The A5 alternative is excluded by 3^(2f) = 4 modulo five. A PSL2 subfield
has degree one, giving the solvable PSL2(3) = A4, or degree f, giving full
ambient order. The PGL2 subfield alternative would make two divide f.
The ordinary cases use the solvability lemmas in ConversePSL2Prime.

Mathlib's rank-two simplicity and the existing PSL2 perfection theorem
supply the remaining minimal-simple hypotheses. This proves the
three-power family in Thompson's converse; the full classification remains
a separate theorem.

Source: Thompson's minimal-simple catalogue and Dickson, Huppert II.8.27,
through Glauberman.DicksonClassification.
-/

namespace Stellmacher.Recognition

open BenderSuzuki.MatrixGroups GorensteinWalter Glauberman.Dickson

private theorem three_pow_two_mul_odd_mod_five
    {f : ℕ} (hf : Odd f) : 3 ^ (2 * f) % 5 = 4 := by
  obtain ⟨k, rfl⟩ := hf
  have hexp : 2 * (2 * k + 1) = 4 * k + 2 := by omega
  rw [hexp, pow_add, pow_mul]
  norm_num [Nat.pow_mod, Nat.mul_mod]

private theorem psl2_three_power_subgroup_isSolvable
    {f : ℕ} (hf : f.Prime) (hfodd : Odd f)
    (H : Subgroup (PSL2MatrixGroup (GaloisField 3 f)))
    (hproper : H ≠ ⊤) : Group.IsSolvable H := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : Fact (Nat.Prime f) := ⟨hf⟩
  have hFcard : Nat.card (GaloisField 3 f) = 3 ^ f :=
    GaloisField.card 3 f hf.ne_zero
  have hodd : IsOddPrimePower (Nat.card (GaloisField 3 f)) :=
    ⟨3, f, by decide, by decide, hf.one_le, hFcard⟩
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification
      (p := 3) (f := f) hFcard H with
      hEl | hCy | hDi | hA4 | hS4 | hA5 | hSemi | hPSL | hPGL
  · let : IsElementaryAbelian 3 H := hEl
    exact Group.isSolvable_of_comm fun a b => IsMulCommutative.is_comm.comm a b
  · obtain ⟨_, _, _, hcyc⟩ := hCy
    let : IsCyclic H := hcyc
    let : CommGroup H := IsCyclic.commGroup
    infer_instance
  · obtain ⟨z, _, _, ⟨e⟩⟩ := hDi
    let : Group.IsSolvable (DihedralGroup z) := GLS3.Chapter5.dihedralGroup_isSolvable z
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · obtain ⟨_, ⟨e⟩⟩ := hA4
    let : Group.IsSolvable (alternatingGroup (Fin 4)) :=
      alternatingGroup_fin_four_isSolvable
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · obtain ⟨_, ⟨e⟩⟩ := hS4
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · obtain ⟨hcond, _⟩ := hA5
    rcases hcond with hp5 | hdiv
    · norm_num at hp5
    · rw [Nat.dvd_iff_mod_eq_zero] at hdiv
      have hpow := three_pow_two_mul_odd_mod_five hfodd
      have hsub := Nat.mod_sub_of_le (a := 3 ^ (2 * f)) (b := 1) (n := 5)
        (by rw [hpow]; norm_num)
      rw [← hsub, hpow] at hdiv
      omega
  · obtain ⟨_, _, _, _, N, C, hNnormal, hNelem, _, hCcyc, _, _, hsup⟩ := hSemi
    let : N.Normal := hNnormal
    let : IsElementaryAbelian 3 N := hNelem
    let : IsCyclic C := hCcyc
    let : CommGroup C := IsCyclic.commGroup
    let : Group.IsSolvable N := Group.isSolvable_of_comm fun a b =>
      IsMulCommutative.is_comm.comm a b
    exact Group.isSolvable_of_normal_sup_eq_top N C hsup
  · obtain ⟨m, hm, hmdiv, ⟨e⟩⟩ := hPSL
    have hm_cases : m = 1 ∨ m = f := (Nat.dvd_prime hf).mp hmdiv
    rcases hm_cases with hm1 | hmf
    · subst m
      let eK : ZMod 3 ≃+* GaloisField 3 1 :=
        letI : Fintype (GaloisField 3 1) := Fintype.ofFinite _
        FiniteField.ringEquivOfCardEq (by
          have hGF : Fintype.card (GaloisField 3 1) = 3 := by
            simpa [Nat.card_eq_fintype_card] using GaloisField.card 3 1 (by simp)
          simp [hGF])
      let eA : PSL2MatrixGroup (GaloisField 3 1) ≃*
          alternatingGroup (Fin 4) :=
        (psl2RingEquiv eK).symm.trans psl2_three_equiv_alternatingGroup
      let : Group.IsSolvable (alternatingGroup (Fin 4)) :=
        alternatingGroup_fin_four_isSolvable
      exact Group.isSolvable_of_isSolvable_injective
        (f := (e.trans eA).toMonoidHom) (e.trans eA).injective
    · have hcardH : Nat.card H = Nat.card (PSL2MatrixGroup (GaloisField 3 f)) := by
        rw [hmf] at e
        exact Nat.card_congr e.toEquiv
      exact (hproper (H.eq_top_of_card_eq hcardH)).elim
  · obtain ⟨m, hm, hmdiv, _⟩ := hPGL
    have h2dvd : 2 ∣ f := dvd_trans (dvd_mul_right 2 m) hmdiv
    exact (hfodd.not_two_dvd_nat h2dvd).elim

/-- Thompson's three-power PSL2 family is minimal simple for odd prime exponent. -/
public theorem isMinimalSimple_psl2_three_power
    {f : ℕ} (hf : f.Prime) (hfodd : Odd f) :
    IsMinimalSimple (PSL2MatrixGroup (GaloisField 3 f)) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : Fact (Nat.Prime f) := ⟨hf⟩
  have hFcard : Nat.card (GaloisField 3 f) = 3 ^ f :=
    GaloisField.card 3 f hf.ne_zero
  have hf3 : 3 ≤ f := by
    have hf2 : 2 ≤ f := hf.two_le
    rcases hfodd with ⟨k, hk⟩
    omega
  have hpow : 27 ≤ 3 ^ f := by
    calc
      27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by omega) hf3
  have hsimple : IsSimpleGroup (PSL2MatrixGroup (GaloisField 3 f)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [hFcard]
      exact (show 4 ≤ 27 by norm_num).trans hpow)
  let : IsSimpleGroup (PSL2MatrixGroup (GaloisField 3 f)) := hsimple
  let : Group.IsPerfect (PSL2MatrixGroup (GaloisField 3 f)) :=
    psl2_isPerfect_of_card_gt_three _ (by
      rw [hFcard]
      exact (show 3 < 27 by norm_num).trans_le hpow)
  refine ⟨hsimple, Group.IsPerfect.not_isSolvable _, ?_⟩
  intro H hH
  exact psl2_three_power_subgroup_isSolvable hf hfodd H (ne_of_lt hH)

end Stellmacher.Recognition
