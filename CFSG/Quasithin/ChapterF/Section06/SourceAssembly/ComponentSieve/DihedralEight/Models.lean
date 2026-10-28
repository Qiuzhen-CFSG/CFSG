module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.Assembly
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The complete order-eight Sylow sieve without elementarity

A nonsolvable model in the literal Theorem C list with Sylow two-subgroup
of order at most eight is odd PSL2 of degree at most two, A6, A7, PSL2(8),
or J1. The larger carriers have orders divisible by sixteen. The binary
PSL3 endpoint is identified with PSL2(7) through its actual eight-point
action; the binary symplectic commutator is identified with A6.

This is the central quotient sieve for the dihedral-eight branch of
Aschbacher--Smith F.6.18, printed pp.309--310.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve
variable {G : Type*} [Group G] [Finite G]

theorem binary_linear_three_small_parameters
    (P : Sylow 2 G) (hP : Nat.card P ≤ 8) {f : ℕ} (hf : 1 ≤ f)
    (hm : ClassicalGroup.IsPSL G 3 (2 ^ f)) : f = 1 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  have hd := Matrix.ProjectiveSpecialLinearGroup.psl3_cube_dvd_card (F := F)
  rw [hF] at hd
  by_contra hn
  have hf2 : 2 ≤ f := by omega
  apply not_sixteen_dvd_of_sylow_le_eight P hP
  rw [Nat.card_congr e.toEquiv]
  apply dvd_trans _ hd
  rw [← pow_mul]
  exact Nat.pow_dvd_pow 2 (by omega : 4 ≤ f * 3)

omit [Finite G] in
theorem prime_seven_model_of_binary_linear_three
    (hm : ClassicalGroup.IsPSL G 3 2) : ClassicalGroup.IsPSL G 2 7 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let a : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa [← Nat.card_eq_fintype_card] using hF)
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact ⟨ZMod 7, inferInstance, inferInstance, Nat.card_zmod _,
    ⟨e.trans ((Atlas.fieldEquivPSL 3 a).trans
      Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm)⟩⟩

theorem alternating_degree_of_sylow_le_eight
    (P : Sylow 2 G) (hP : Nat.card P ≤ 8) (hns : ¬ Group.IsSolvable G)
    {n : ℕ} (hn : n ≤ 8) (e : G ≃* alternatingGroup (Fin n)) :
    n = 5 ∨ n = 6 ∨ n = 7 := by
  have h5 : 5 ≤ n := by
    by_contra! hh
    have hs : Group.IsSolvable (alternatingGroup (Fin n)) := by
      by_cases h4 : n = 4
      · subst n; exact alternatingGroup_fin_four_isSolvable
      · let := alternatingGroup.isMulCommutative_of_card_le_three
          (α := Fin n) (by simpa using (show n ≤ 3 by omega))
        exact Group.isSolvable_of_comm (isMulCommutative_iff.mp inferInstance)
    let := hs
    exact hns (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
  have hn8 : n ≠ 8 := by
    intro hh
    subst n
    have hh := not_sixteen_dvd_of_sylow_le_eight P hP
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hh
    norm_num at hh
  omega

/-- The exact Theorem C catalogue on the original group, with every
large-two-part constructor discharged. -/
theorem theoremC_model_of_sylow_le_eight
    (P : Sylow 2 G) (hP : Nat.card P ≤ 8) (hns : ¬ Group.IsSolvable G)
    (hm : ChapterA.Section02.IsTheoremCModel G) :
    (∃ p f : ℕ, p.Prime ∧ Odd p ∧ 1 ≤ f ∧ f ≤ 2 ∧
      ClassicalGroup.IsPSL G 2 (p ^ f)) ∨
    Nonempty (G ≃* alternatingGroup (Fin 6)) ∨
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
    ClassicalGroup.IsPSL G 2 8 ∨ Nonempty (G ≃* Janko1.Model) := by
  have hprime (p : ℕ) (hp : p.Prime) (ho : Odd p) (hm : ClassicalGroup.IsPSL G 2 p) :
      ∃ p f : ℕ, p.Prime ∧ Odd p ∧ 1 ≤ f ∧ f ≤ 2 ∧
        ClassicalGroup.IsPSL G 2 (p ^ f) :=
    ⟨p, 1, hp, ho, by decide, by decide, by simpa using hm⟩
  cases hm with
  | alternating n hn iso =>
    obtain ⟨e⟩ := iso
    rcases alternating_degree_of_sylow_le_eight P hP hns hn e with rfl | rfl | rfl
    · obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five
      exact .inl (hprime 5 (by decide) (by decide)
        ⟨ZMod 5, inferInstance, inferInstance, Nat.card_zmod _, ⟨e.trans a.symm⟩⟩)
    · exact .inr (.inl ⟨e⟩)
    · exact .inr (.inr (.inl ⟨e⟩))
  | odd model =>
    cases model with
    | linear_two p f hp ho hf iso =>
      have hfpos : 1 ≤ f := by
        obtain ⟨F, _, _, hc, _⟩ := iso
        have hcard : 1 < Nat.card F := Finite.one_lt_card
        by_contra! hh
        have hz : f = 0 := by omega
        simp [hz] at hc
        omega
      exact .inl ⟨p, f, hp, ho, hfpos, hf, iso⟩
    | linear_three p hp ho iso => exact (not_psl3_odd_of_small_sylow P hP ho iso).elim
    | unitary_three p hp ho iso =>
      exact (not_psu3_odd_of_small_sylow P hP hp.one_lt ho iso).elim
  | bender model =>
    rcases bender_small_sylow_cases P hP model with hm | hm
    · exact .inl (hprime 5 (by decide) (by decide) hm)
    · exact .inr (.inr (.inr (.inl hm)))
  | rank_two f model =>
    cases model with
    | linear hf iso =>
      have he := binary_linear_three_small_parameters P hP hf iso
      subst f
      have hm := prime_seven_model_of_binary_linear_three (by simpa using iso)
      exact .inl (hprime 7 (by decide) (by decide) hm)
    | symplectic hf iso => exact (not_symplectic_of_small_sylow P hP hf iso).elim
    | g2 hf iso => exact (not_g2_of_small_sylow P hP hf iso).elim
    | triality hf iso => exact (not_triality_of_small_sylow P hP hf iso).elim
    | ree_f4 m _ _ iso =>
      obtain ⟨e⟩ := iso
      exact (not_ree_f4_of_small_sylow P hP m e).elim
    | symplectic_derived _ iso =>
      obtain ⟨e⟩ := iso
      exact .inr (.inl ⟨e.trans
        Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix⟩)
    | g2_derived _ iso =>
      obtain ⟨e⟩ := iso
      exact (not_g2_derived_of_small_sylow P hP e).elim
    | tits _ iso =>
      obtain ⟨e⟩ := iso
      exact (not_tits_of_small_sylow P hP e).elim
  | linear_binary n hn model =>
    exact (not_binary_four_or_five_of_small_sylow P hP hn model).elim
  | sporadic model =>
    exact .inr (.inr (.inr (.inr (jankoOne_of_theoremC_sporadic_small_sylow P hP model))))

end CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve
