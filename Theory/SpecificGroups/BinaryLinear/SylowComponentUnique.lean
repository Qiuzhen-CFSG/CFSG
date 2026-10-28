module
public import Theory.GroupTheory.CComponent.SylowOvergroupUniqueExtensions
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.NormalSolvable
public import Theory.GroupTheory.TwoThreeSolvable
/-!
# Unique C-components in binary linear Sylow overgroups through dimension five

A Sylow overgroup is an actual partial-flag stabilizer. A nonempty cut puts
it in a subspace parabolic, whose literal two-core quotient is the product
of the linear groups on the subspace and its quotient. Since the dimensions
sum to at most five, one factor has dimension at most two and is solvable.
Induction on dimension leaves at most one nonsolvable component. This uses
the Levi quotient, beyond the generalized-Fitting bound for the parabolic.

Source: Aschbacher--Smith A.3.12(4--5), pp.47--48, and 1.2.8(1), p.506.
The imported simplicity port retains its attribution in LICENSES/ATLAS.txt.
-/

public section
open Subgroup Theory.GroupTheory
namespace BinaryLinear
open OuterCyclic SmallParabolicLevi InvariantNodeActions
private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

private theorem small_solvable (n : ℕ) (hn : n ≤ 2) : Group.IsSolvable (LinearGroup n) := by
  apply isSolvable_of_prime_dvd_card_eq_two_or_three
  intro p hp hd
  have hc : Nat.card (LinearGroup n) = ∏ i : Fin n, (2^n - 2^i.val) := by
    rw [← Nat.card_congr (matrixEquivLinear n).toEquiv, Matrix.card_GL_field]
    simp
  rw [hc] at hd
  interval_cases n
  · norm_num at hd
    exact (hp.ne_one hd).elim
  · norm_num at hd
    exact (hp.ne_one hd).elim
  · norm_num [Fin.prod_univ_two] at hd
    have hh := hp.dvd_mul.mp (show p ∣ 2*3 from hd)
    exact hh.elim
      (fun h => Or.inl ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one))
      (fun h => Or.inr ((Nat.dvd_prime Nat.prime_three).mp h |>.resolve_left hp.ne_one))

/-- Every Sylow overgroup of GLₙ(2), n ≤ 5, has at most one C-component. -/
theorem sylow_overgroup_component_unique_le_five (n : ℕ) (hn : n ≤ 5) :
    SylowOvergroupComponentUnique (LinearGroup n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn2 : n ≤ 2
    · let := small_solvable n hn2
      exact SylowOvergroupComponentUnique.of_isSolvable
    have hn3 : 3 ≤ n := by omega
    let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) :=
      Atlas.psl_simple_high_rank n hn3
    let : IsSimpleGroup (LinearGroup n) := (projectiveEquivLinear (by omega : 0<n)).symm.isSimpleGroup
    let : Group.IsPerfect (LinearGroup n) := linearGroup_isPerfect n hn3
    apply SylowOvergroupComponentUnique.of_proper_overgroups
    intro S P hSP hP B C hB hC
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    obtain ⟨b,cuts,_,hcuts⟩ := SylowFlagOvergroups.exists_flag_of_sylow_le S P hSP
    have hne : cuts.Nonempty := by
      by_contra hh
      have he := Set.not_nonempty_iff_eq_empty.mp hh
      apply hP
      rw [hcuts,he]
      ext g
      simp [mem_cutStabilizer]
    obtain ⟨i,hi⟩ := hne
    let W := cutSpace b i
    have hPW : P ≤ parabolic W := by
      rw [hcuts]
      intro g hg
      exact (mem_cutStabilizer b cuts g).mp hg i hi
    apply SylowOvergroupComponentUnique.eq_of_le_overgroup S hSP hPW ?_ hB hC
    let : Group.IsNilpotent (pCore 2 (parabolic W)) := pCore_isNilpotent
    apply SylowOvergroupComponentUnique.of_quotient (pCore 2 (parabolic W))
    let a : W ≃ₗ[ZMod 2] Space (i.val+1) := LinearEquiv.ofFinrankEq _ _ (by
      rw [Module.finrank_fin_fun]
      exact cutSpace_finrank b i)
    let c : (Space (m+1) ⧸ W) ≃ₗ[ZMod 2] Space (m-i.val) := LinearEquiv.ofFinrankEq _ _ (by
      rw [Module.finrank_fin_fun]
      have hd := W.finrank_quotient_add_finrank
      change Module.finrank (ZMod 2) (Space (m+1) ⧸ W) +
        Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) (Space (m+1)) at hd
      rw [show Module.finrank (ZMod 2) W = i.val+1 from cutSpace_finrank b i,
        Module.finrank_fin_fun] at hd
      omega)
    apply SylowOvergroupComponentUnique.of_equiv (quotientTwoCoreEquivOfCoordinates W a c)
    by_cases hsmall : i.val+1 ≤ 2
    · let := small_solvable (i.val+1) hsmall
      apply SylowOvergroupComponentUnique.prod_left
      exact ih (m-i.val) (by omega) (by omega)
    · let := small_solvable (m-i.val) (by omega)
      apply SylowOvergroupComponentUnique.prod_right
      exact ih (i.val+1) (by have := i.isLt; omega) (by have := i.isLt; omega)
end BinaryLinear
