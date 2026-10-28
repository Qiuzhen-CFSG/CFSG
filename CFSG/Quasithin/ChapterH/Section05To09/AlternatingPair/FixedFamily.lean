module

public import Theory.Representation.AlternatingSevenConjugatePair
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry
public import Theory.Representation.AlternatingSevenConjugatePair.FixedFamily
public import CFSG.Quasithin.ChapterH.Section05To09.AlternatingPair.Parameters

/-!
# The unique Sylow fixed-space-family member in H.8

A member of the genuine family `A₂` lies in A₇: its even intersection has
relative index at most two and fixes a nonzero vector in the first summand.
The family equality would make that vector fixed by an odd element, contradicting
interchange of the disjoint summands. The alternating rank bound then forces
rank two, and the family condition is exactly fixed codimension four.

The structural calculation in `AlternatingSevenConjugatePair.FixedFamily`
constructs the unique such four-group in every Sylow subgroup. Its two summand
fixed spaces both have dimension two. The regular four-group supplies the
actual witness for the lower bound on `moduleA`.

The only unproved input here is the explicitly permitted single-involution
calculation `hinv`; the unconditional H.8 assembly remains in `AlternatingPair`.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.8,
printed p.389/PDF p.400, using E.3.8–9's relative-index convention.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterH.AlternatingPair
open Representation.BinaryOffender Representation.AlternatingSevenConjugatePair
open Representation.AlternatingSevenConjugatePair.ElementaryGeometry
open Representation.AlternatingSevenConjugatePair.FixedFamily
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Interchanging the summands excludes every actor outside the alternating group. -/
theorem fixedSpaceFamily_two_le_alternating (D : Pair V)
    (A : Subgroup S7) (hA : A ∈ ChapterE.fixedSpaceFamily D.representation 2) :
    A ≤ alternatingGroup (Fin 7) := by
  classical
  have hAe : IsElementaryTwo A := hA.2.1
  have hr : 2 ≤ rank A :=
    ChapterE.parameter_le_rank_of_mem_fixedSpaceFamily D.representation D.faithful hA
  have hcard : 4 ≤ Nat.card A := by
    rw [hAe.card_eq_two_pow_rank]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hr
  let B := A ⊓ alternatingGroup (Fin 7)
  have hidx : B.relIndex A ≤ 2 := by
    have hdiv := (alternatingGroup (Fin 7)).relIndex_dvd_index_of_normal A
    rw [alternatingGroup.index_eq_two, ← Subgroup.inf_relIndex_left] at hdiv
    exact Nat.le_of_dvd (by decide) hdiv
  have hB0 : B ≠ ⊥ := by
    intro he
    rw [he, Subgroup.relIndex_bot_left] at hidx
    omega
  have hsmall : Nat.log 2 (B.relIndex A) < 2 :=
    (Nat.log_mono_right hidx).trans_lt (by decide)
  have hfix := hA.2.2 B inf_le_left hsmall
  have hBe := hAe.of_le (show B ≤ A from inf_le_left) hB0
  let _ : IsElementaryAbelian 2 B := hBe.2
  let i : B →* alternatingGroup (Fin 7) := Subgroup.inclusion inf_le_right
  let σ := D.first.toRepresentation.comp i
  have hU0 : D.first.toSubmodule ≠ ⊥ := by
    intro he
    have hd := D.first_dim
    rw [he, finrank_bot] at hd
    omega
  let _ : Nontrivial D.first.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hU0
  obtain ⟨u, hu0, huf⟩ :=
    BinaryLinearThree.IrreducibleCatalogue.binary_pGroup_fixed_vector σ
      (IsElementaryAbelian.isPGroup 2 B)
  have huB : (u : V) ∈ fixedSpace D.representation B :=
    fun b => congrArg Subtype.val (huf b)
  have huA : (u : V) ∈ fixedSpace D.representation A := hfix ▸ huB
  intro a ha
  by_contra haL
  have hau : D.representation a u = u := huA ⟨a, ha⟩
  have huW : (u : V) ∈ D.second.toSubmodule := hau ▸ D.swap_first a haL u u.property
  exact hu0 (Subtype.ext (Submodule.disjoint_def.mp D.complementary.disjoint
    u u.property huW))

/-- The source fixed-space equalities are equivalent to the intrinsic rank and displacement conditions. -/
theorem mem_fixedSpaceFamily_two_iff (D : Pair V)
    (hinv : ∀ t : S7, orderOf t = 2 →
      fixedCodim D.representation (Subgroup.zpowers t) = 4) (A : Subgroup S7) :
    A ∈ ChapterE.fixedSpaceFamily D.representation 2 ↔
      IsElementaryTwo A ∧ rank A = 2 ∧ A ≤ alternatingGroup (Fin 7) ∧
        fixedCodim D.representation A = 4 := by
  constructor
  · intro hA
    have hAe := hA.2.1
    have hAL := fixedSpaceFamily_two_le_alternating D A hA
    have hlo := ChapterE.parameter_le_rank_of_mem_fixedSpaceFamily D.representation D.faithful hA
    have hhi := rank_le_two_of_le_alternating A hAe hAL
    have hr : rank A = 2 := by omega
    refine ⟨hAe, hr, hAL, ?_⟩
    let _ := hAe.2
    obtain ⟨t, htA, ht⟩ := A.bot_or_exists_ne_one.resolve_left hAe.1
    have ht2 : orderOf t = 2 :=
      orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian t htA) ht
    have hCA : Subgroup.zpowers t ≤ A := Subgroup.zpowers_le.mpr htA
    have hp := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup S7)
      (Subgroup.zpowers t) A bot_le hCA
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left,
      Nat.card_zpowers, ht2, hAe.card_eq_two_pow_rank, hr] at hp
    have hi : (Subgroup.zpowers t).relIndex A = 2 := by omega
    have he := hA.2.2 (Subgroup.zpowers t) hCA (by rw [hi]; decide)
    unfold fixedCodim
    rw [he]
    exact hinv t ht2
  · rintro ⟨hA, hr, _, hc⟩
    refine ⟨by decide, hA, ?_⟩
    intro B hBA hidx
    have hB : B ≠ ⊥ := by
      intro he
      rw [he, Subgroup.relIndex_bot_left, hA.card_eq_two_pow_rank, hr] at hidx
      exact (by decide : ¬ Nat.log 2 (2 ^ 2) < 2) hidx
    exact fixedSpace_eq_of_attaining_involution_bound D.representation
      (fun t ht => (hinv t ht).ge) hA hBA hB hc.le

/-- The actual regular four-group belongs to E.3.8's family of parameter two. -/
theorem regularFour_mem_fixedSpaceFamily_two (D : Pair V)
    (hinv : ∀ t : S7, orderOf t = 2 →
      fixedCodim D.representation (Subgroup.zpowers t) = 4) :
    regularFour ∈ ChapterE.fixedSpaceFamily D.representation 2 :=
  (mem_fixedSpaceFamily_two_iff D hinv regularFour).mpr
    ⟨regularFour_elementary, regularFour_rank, inf_le_right, regularFour_codim D hinv⟩

/-- The precise singleton and fixed-plane characterization asserted in H.8,
conditional only on the single-involution calculation. -/
theorem exists_sylowFixedSpaceFamily_singleton (D : Pair V)
    (hinv : ∀ t : S7, orderOf t = 2 →
      fixedCodim D.representation (Subgroup.zpowers t) = 4) (T : Sylow 2 S7) :
    ∃ A : Subgroup S7, A ≤ (T : Subgroup S7) ∧ A ≤ alternatingGroup (Fin 7) ∧
      IsElementaryTwo A ∧ rank A = 2 ∧
      sylowFixedSpaceFamily D.representation T 2 = {A} ∧
      Module.finrank (ZMod 2) (D.firstFixedSpace A) = 2 ∧
      Module.finrank (ZMod 2) (D.secondFixedSpace A) = 2 ∧
      (∀ B : Subgroup S7, B ≤ (T : Subgroup S7) → B ≤ alternatingGroup (Fin 7) →
        IsElementaryTwo B → rank B = 2 →
        (B = A ↔ Module.finrank (ZMod 2) (D.firstFixedSpace B) = 2 ∧
          Module.finrank (ZMod 2) (D.secondFixedSpace B) = 2)) := by
  obtain ⟨A, hAT, hAL, hA, hr, hc, huniq⟩ := exists_unique_codim_four D hinv T
  have hmem := (mem_fixedSpaceFamily_two_iff D hinv A).mpr ⟨hA, hr, hAL, hc⟩
  have hd := (codim_four_iff_summand_dimensions D hinv A hA hAL).mp hc
  refine ⟨A, hAT, hAL, hA, hr, ?_, hd.1, hd.2, ?_⟩
  · ext B
    constructor
    · rintro ⟨hBT, hB⟩
      obtain ⟨hBe, hrB, hBL, hcB⟩ := (mem_fixedSpaceFamily_two_iff D hinv B).mp hB
      exact Set.mem_singleton_iff.mpr (huniq B hBT hBL hBe hrB hcB)
    · rintro rfl
      exact ⟨hAT, hmem⟩
  · intro B hBT hBL hBe hrB
    constructor
    · rintro rfl
      exact hd
    · intro hdim
      exact huniq B hBT hBL hBe hrB
        ((codim_four_iff_summand_dimensions D hinv B hBe hBL).mpr hdim)

/-- The concrete regular four-group witnesses the lower bound `a ≥ 2`. -/
theorem two_le_moduleA (D : Pair V)
    (hinv : ∀ t : S7, orderOf t = 2 →
      fixedCodim D.representation (Subgroup.zpowers t) = 4) :
    2 ≤ ChapterE.moduleA D.representation :=
  ChapterE.le_moduleA_of_mem D.representation (regularFour_mem_fixedSpaceFamily_two D hinv)

end CFSG.Quasithin.ChapterH.AlternatingPair
