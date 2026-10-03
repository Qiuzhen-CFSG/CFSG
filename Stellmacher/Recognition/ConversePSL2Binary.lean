module

public import Stellmacher.Recognition.ConversePSL2Prime
public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import GorensteinWalter.PGL2Cardinality
public import Mathlib.GroupTheory.SpecificGroups.ZGroup
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Minimal simplicity of binary PSL2 at prime exponents

For a prime f, PSL2 over GaloisField 2 f is minimal simple. Simplicity and
perfection give the ambient group properties. Dickson's subgroup theorem
gives solvability of every proper subgroup. For odd f, the A5 alternative
fails modulo five; for f = 2, an A5 has full ambient order sixty and cannot
be proper.

A PSL2 subfield has degree one, giving the solvable group of order six, or
degree f, giving the entire group. The PGL2 subfield alternative requires
f = 2 and degree one, also giving order six. Solvability of the order-six
cases follows from the squarefree-order Z-group theorem. The remaining
Dickson cases use elementary, cyclic, dihedral, A4, S4 and extension
solvability.

Source: Thompson's minimal-simple binary family; Dickson, Huppert II.8.27,
and the exact projective order calculation in Huppert II.6.14. The complete
five-family classification is a separate campaign endpoint.
-/

namespace Stellmacher.Recognition

open BenderSuzuki.MatrixGroups BenderSuzuki.External GorensteinWalter Glauberman.Dickson

private theorem binary_psl2_card (f : ℕ) (hf : f ≠ 0) :
    Nat.card (PSL2MatrixGroup (GaloisField 2 f)) =
      2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  have hcard := huppert614_card_psl_mul_center (K := GaloisField 2 f)
  have hcenter := huppert614_card_center_of_neg_one_eq_one (K := GaloisField 2 f)
    (CharTwo.neg_eq 1)
  rw [hcenter, mul_one, GaloisField.card 2 f hf] at hcard
  exact hcard

private theorem binary_pow_two_mul_odd_mod_five
    {f : ℕ} (hf : Odd f) : 2 ^ (2 * f) % 5 = 4 := by
  obtain ⟨k, rfl⟩ := hf
  have hexp : 2 * (2 * k + 1) = 4 * k + 2 := by omega
  rw [hexp, pow_add, pow_mul]
  norm_num [Nat.pow_mod, Nat.mul_mod]

private theorem binary_psl2_subgroup_isSolvable
    {f : ℕ} (hf : f.Prime)
    (H : Subgroup (PSL2MatrixGroup (GaloisField 2 f)))
    (hproper : H ≠ ⊤) : Group.IsSolvable H := by
  have hFcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf.ne_zero
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification
      (p := 2) (f := f) hFcard H with
      hEl | hCy | hDi | hA4 | hS4 | hA5 | hSemi | hPSL | hPGL
  · let : IsElementaryAbelian 2 H := hEl
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
  · obtain ⟨hcond, ⟨e⟩⟩ := hA5
    by_cases hf2 : f = 2
    · have hcardH : Nat.card H = Nat.card (PSL2MatrixGroup (GaloisField 2 f)) := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, binary_psl2_card f hf.ne_zero,
          hf2]
        norm_num [Nat.factorial]
      exact (hproper (H.eq_top_of_card_eq hcardH)).elim
    · have hfodd : Odd f := hf.odd_of_ne_two hf2
      rcases hcond with htwo | hdiv
      · norm_num at htwo
      · rw [Nat.dvd_iff_mod_eq_zero] at hdiv
        have hm := binary_pow_two_mul_odd_mod_five hfodd
        have hsub := Nat.mod_sub_of_le (a := 2 ^ (2 * f)) (b := 1) (n := 5)
          (by rw [hm]; norm_num)
        rw [← hsub, hm] at hdiv
        omega
  · obtain ⟨_, _, _, _, N, C, hNnormal, hNelem, _, hCcyc, _, _, hsup⟩ := hSemi
    let : N.Normal := hNnormal
    let : IsElementaryAbelian 2 N := hNelem
    let : IsCyclic C := hCcyc
    let : CommGroup C := IsCyclic.commGroup
    let : Group.IsSolvable N := Group.isSolvable_of_comm fun a b =>
      IsMulCommutative.is_comm.comm a b
    exact Group.isSolvable_of_normal_sup_eq_top N C hsup
  · obtain ⟨m, hm, hmdiv, ⟨e⟩⟩ := hPSL
    rcases (Nat.dvd_prime hf).mp hmdiv with hm1 | hmf
    · have hcardH : Nat.card H = 6 := by
        rw [Nat.card_congr e.toEquiv, binary_psl2_card m hm, hm1]
        norm_num
      let : IsZGroup H := IsZGroup.of_squarefree (by
        rw [hcardH]
        exact (Nat.squarefree_mul (by decide : Nat.Coprime 2 3)).mpr
          ⟨Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩)
      infer_instance
    · have hcardH : Nat.card H = Nat.card (PSL2MatrixGroup (GaloisField 2 f)) := by
        rw [hmf] at e
        exact Nat.card_congr e.toEquiv
      exact (hproper (H.eq_top_of_card_eq hcardH)).elim
  · obtain ⟨m, hm, hmdiv, ⟨e⟩⟩ := hPGL
    have hm1 : m = 1 := by
      rcases (Nat.dvd_prime hf).mp hmdiv with hprod1 | hprodf
      · omega
      · have h2dvd : 2 ∣ f := dvd_trans (dvd_mul_right 2 m) hmdiv
        have hf2 : f = 2 := by
          rcases hf.eq_two_or_odd' with hf2 | hfodd
          · exact hf2
          · exact (hfodd.not_two_dvd_nat h2dvd).elim
        omega
    have hcardH : Nat.card H = 6 := by
      rw [Nat.card_congr e.toEquiv, pgl2_card_formula,
        GaloisField.card 2 m hm, hm1]
      norm_num
    let : IsZGroup H := IsZGroup.of_squarefree (by
      rw [hcardH]
      exact (Nat.squarefree_mul (by decide : Nat.Coprime 2 3)).mpr
        ⟨Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩)
    infer_instance

/-- Thompson's binary PSL2 family is minimal simple at prime exponents. -/
public theorem isMinimalSimple_psl2_binary {f : ℕ} (hf : f.Prime) :
    IsMinimalSimple (PSL2MatrixGroup (GaloisField 2 f)) := by
  have hFcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf.ne_zero
  have hpow : 4 ≤ 2 ^ f := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by omega) hf.two_le
  have hsimple : IsSimpleGroup (PSL2MatrixGroup (GaloisField 2 f)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hFcard]; exact hpow)
  let : IsSimpleGroup (PSL2MatrixGroup (GaloisField 2 f)) := hsimple
  let : Group.IsPerfect (PSL2MatrixGroup (GaloisField 2 f)) :=
    psl2_isPerfect_of_card_gt_three _ (by rw [hFcard]; omega)
  refine ⟨hsimple, Group.IsPerfect.not_isSolvable _, ?_⟩
  intro H hH
  exact binary_psl2_subgroup_isSolvable hf H (ne_of_lt hH)

end Stellmacher.Recognition
