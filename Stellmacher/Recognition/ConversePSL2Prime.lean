module

public import Theory.GroupTheory.MinimalSimple
public import Theory.GroupTheory.SolvableNormalSup
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.SpecificGroups.DihedralSolvable
public import GorensteinWalter.PSL2Cardinality
public import GorensteinWalter.PSL2PerfectOfCard
public import Glauberman.DicksonClassification
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# Minimal simplicity of prime-field PSL₂

For a prime p > 3 congruent to 2 or 3 modulo five, PSL₂ over a field of order
p is minimal simple. Simplicity is Mathlib's rank-two theorem; perfection
gives nonsolvability. Every proper subgroup is solvable by Dickson's actual
nine-case subgroup classification.

The elementary, cyclic, dihedral, A₄, S₄ and elementary-by-cyclic cases are
solvable. The A₅ arithmetic condition is incompatible with the residue of p.
A nonzero subfield degree dividing one is one, so the PSL₂ subfield case has
the full ambient order and cannot be proper. Twice a nonzero degree cannot
divide one, excluding the PGL₂ subfield case.

This proves the prime-field family in Thompson's five-family converse. The
statement allows any finite field of the given order and specializes to the
concrete ZMod model without an abstract model predicate.

Source: Thompson's minimal-simple catalogue; Dickson's theorem as Huppert
II.8.27, exported by Glauberman.DicksonClassification. The campaign source
audit is in tasks/ms-source-contract.md.
-/

namespace Stellmacher.Recognition

open BenderSuzuki.MatrixGroups GorensteinWalter Glauberman.Dickson

private theorem not_five_dvd_prime_square_sub_one_of_mod
    {p : ℕ} (hp : p % 5 = 2 ∨ p % 5 = 3) :
    ¬ 5 ∣ p ^ 2 - 1 := by
  intro h
  rw [Nat.dvd_iff_mod_eq_zero] at h
  have hm : p ^ 2 % 5 = 4 := by
    rcases hp with hp | hp
    · rw [Nat.pow_mod]
      simp [hp]
    · rw [Nat.pow_mod]
      simp [hp]
  omega

private theorem psl2_prime_subgroup_isSolvable
    {F : Type*} [Field F] [Finite F] {p : ℕ}
    [Fact p.Prime] (hFcard : Nat.card F = p)
    (hpgt : 3 < p) (hpmod : p % 5 = 2 ∨ p % 5 = 3)
    (H : Subgroup (PSL2MatrixGroup F)) (hproper : H ≠ ⊤) :
    Group.IsSolvable H := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hodd : IsOddPrimePower (Nat.card F) := by
    refine ⟨p, 1, Fact.out, hpodd, by simp, ?_⟩
    simp [hFcard]
  have hFcardPow : Nat.card F = p ^ 1 := by simp [hFcard]
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification
      (p := p) (f := 1) hFcardPow H with
      hEl | hCy | hDi | hA4 | hS4 | hA5 | hSemi | hPSL | hPGL
  · let : IsElementaryAbelian p H := hEl
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
    · have hmodzero : p % 5 = 0 := by rw [hp5]
      omega
    · exact (not_five_dvd_prime_square_sub_one_of_mod hpmod hdiv).elim
  · obtain ⟨_, _, _, _, N, C, hNnormal, hNelem, _, hCcyc, _, _, hsup⟩ := hSemi
    let : N.Normal := hNnormal
    let : IsElementaryAbelian p N := hNelem
    let : IsCyclic C := hCcyc
    let : CommGroup C := IsCyclic.commGroup
    let : Group.IsSolvable N := Group.isSolvable_of_comm fun a b =>
      IsMulCommutative.is_comm.comm a b
    exact Group.isSolvable_of_normal_sup_eq_top N C hsup
  · obtain ⟨m, hm, hmdiv, ⟨e⟩⟩ := hPSL
    have hmle : m ≤ 1 := Nat.le_of_dvd (by norm_num) hmdiv
    have hmone : m = 1 := by omega
    subst m
    have hGFcard : Nat.card (GaloisField p 1) = p := by
      simpa using (GaloisField.card p 1 (by simp))
    have hGFodd : IsOddPrimePower (Nat.card (GaloisField p 1)) := by
      refine ⟨p, 1, Fact.out, hpodd, by simp, ?_⟩
      simpa using hGFcard
    have hcardH : Nat.card H = Nat.card (PSL2MatrixGroup F) := by
      calc
        Nat.card H = Nat.card (PSL2MatrixGroup (GaloisField p 1)) :=
          Nat.card_congr e.toEquiv
        _ = p * (p ^ 2 - 1) / 2 := by
          rw [psl2_card_formula (GaloisField p 1) hGFodd, hGFcard]
        _ = Nat.card (PSL2MatrixGroup F) := by
          rw [psl2_card_formula F hodd, hFcard]
    exact (hproper (H.eq_top_of_card_eq hcardH)).elim
  · obtain ⟨m, hm, hmdiv, _⟩ := hPGL
    have hmle : 2 * m ≤ 1 := Nat.le_of_dvd (by norm_num) hmdiv
    omega

/-- Thompson's prime-field PSL₂ family is minimal simple. -/
public theorem isMinimalSimple_psl2_prime
    {F : Type*} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (hFcard : Nat.card F = p) (hpgt : 3 < p)
    (hpmod : p % 5 = 2 ∨ p % 5 = 3) :
    IsMinimalSimple (PSL2MatrixGroup F) := by
  let : Fact p.Prime := ⟨hp⟩
  have hsimple : IsSimpleGroup (PSL2MatrixGroup F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup (PSL2MatrixGroup F) := hsimple
  let : Group.IsPerfect (PSL2MatrixGroup F) :=
    psl2_isPerfect_of_card_gt_three F (by omega)
  refine ⟨hsimple, Group.IsPerfect.not_isSolvable (PSL2MatrixGroup F), ?_⟩
  intro H hH
  exact psl2_prime_subgroup_isSolvable hFcard hpgt hpmod H (ne_of_lt hH)

end Stellmacher.Recognition
