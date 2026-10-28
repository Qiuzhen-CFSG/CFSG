module

public import Glauberman.DicksonClassification
public import GorensteinWalter.PSL2Cardinality
public import Theory.SpecificGroups.DihedralSolvable
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.GroupTheory.SolvableRadical
public import Theory.SpecificGroups.SL2.OddOrderDivisibility

/-!
# Nonsolvable proper subgroups of prime-field PSL₂

Dickson's classification leaves only A₅ for a nonsolvable proper subgroup
of PSL₂ over an odd prime field. All elementary, cyclic, dihedral and affine
alternatives are solvable; the exceptional A₄ and S₄ alternatives are solvable
as well. There is no proper subfield, and the projective general-linear
alternative requires an even extension degree. At characteristic five the
A₅ subgroup has the full ambient order, so that parameter is excluded.

Source: Huppert II.8.27, through the proved Dickson interface; Aschbacher–Smith
A.3.12(8), printed pp.47–48, the odd-prime containing-group branch.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace Theory.PSL2

/-- A nonsolvable proper subgroup in odd prime degree is A₅, with the
actual Dickson divisibility and the characteristic-five exception removed. -/
theorem prime_nonsolvable_proper_is_alternating_five
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p)
    (H : Subgroup (PSL2MatrixGroup F)) (hne : H ≠ ⊤)
    (hns : ¬ Group.IsSolvable H) :
    p ≠ 5 ∧ 5 ∣ p ^ 2 - 1 ∧ Nonempty (H ≃* alternatingGroup (Fin 5)) := by
  have hcardF : Nat.card F = p ^ 1 := by simpa using hF
  have hoddF : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, Fact.out, ho, by decide, hcardF⟩
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
      hcardF H with hEl | hCyc | hDih | hA4 | hS4 | hA5 | hAff | hPSL | hPGL
  · let := hEl
    exact (hns inferInstance).elim
  · obtain ⟨n, _, _, hc⟩ := hCyc
    let := hc
    exact (hns inferInstance).elim
  · obtain ⟨n, _, _, ⟨e⟩⟩ := hDih
    let := GLS3.Chapter5.dihedralGroup_isSolvable n
    exact (hns (Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom) e.injective)).elim
  · obtain ⟨e⟩ := hA4.2
    let := Equiv.Perm.isSolvable_fin_four
    exact (hns (Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom) e.injective)).elim
  · obtain ⟨e⟩ := hS4.2
    let := Equiv.Perm.isSolvable_fin_four
    exact (hns (Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom) e.injective)).elim
  · have hp5 : p ≠ 5 := by
      intro hp
      obtain ⟨e⟩ := hA5.2
      apply hne
      apply H.eq_top_of_card_eq
      rw [Nat.card_congr e.toEquiv, GorensteinWalter.psl2_card_formula F hoddF,
        hF, hp, nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    refine ⟨hp5, ?_, hA5.2⟩
    simpa using hA5.1.resolve_left hp5
  · obtain ⟨m, t, _, _, N, C, hn, he, _, hc, _, _, hg⟩ := hAff
    let := hn
    let := he
    let := hc
    exact (hns (Group.isSolvable_of_normal_sup_eq_top N C hg)).elim
  · obtain ⟨m, _, hm, ⟨e⟩⟩ := hPSL
    have hm1 : m = 1 := Nat.eq_one_of_dvd_one hm
    subst m
    have hK : Nat.card (GaloisField p 1) = p := by
      simpa using GaloisField.card p 1 (by decide)
    apply (hne (H.eq_top_of_card_eq ?_)).elim
    rw [Nat.card_congr e.toEquiv,
      GorensteinWalter.psl2_card_formula (GaloisField p 1)
        ⟨p, 1, Fact.out, ho, by decide, by simpa using hK⟩,
      GorensteinWalter.psl2_card_formula F hoddF, hK, hF]
  · obtain ⟨m, hm, hd, _⟩ := hPGL
    have := Nat.le_of_dvd (by decide : 0 < 1) hd
    omega

/-- An odd-field PSL₂ whose order is not divisible by eight has field order
three or five modulo eight. This is the full-Sylow numerical sieve. -/
theorem mod_eight_of_not_eight_dvd_card
    {F : Type*} [Field F] [Finite F] (ho : Odd (Nat.card F))
    (hnot : ¬ 8 ∣ Nat.card (PSL2MatrixGroup F)) :
    Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5 := by
  have h := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice ho
  let q := Nat.card F
  have hq : 1 < q := Finite.one_lt_card
  have hs : 1 ≤ q ^ 2 := by nlinarith
  have hmod : q % 8 < 8 := Nat.mod_lt _ (by decide)
  have hoddmod : q % 2 = 1 := Nat.odd_iff.mp ho
  by_contra! he
  have hres : q % 8 = 1 ∨ q % 8 = 7 := by omega
  have hd : 16 ∣ q * (q ^ 2 - 1) := by
    apply Nat.dvd_of_mod_eq_zero
    have hsub : (q ^ 2 - 1) % 16 = (q ^ 2 + 15) % 16 := by omega
    have hm16 : q % 16 < 16 := Nat.mod_lt _ (by decide)
    have hr16 : q % 16 = 1 ∨ q % 16 = 7 ∨ q % 16 = 9 ∨ q % 16 = 15 := by omega
    rcases hr16 with hh | hh | hh | hh <;>
      simp [Nat.mul_mod, hsub, Nat.add_mod, Nat.pow_mod, hh]
  rw [← h] at hd
  obtain ⟨a, ha⟩ := hd
  change Nat.card (PSL2MatrixGroup F) * 2 = 16 * a at ha
  exact hnot ⟨a, by omega⟩

end Theory.PSL2
