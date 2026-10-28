module

public import CFSG.Quasithin.ChapterI.Section01.SQTKMultipliers.Statement
public import CFSG.Quasithin.ChapterI.Section01.LieMultipliers.PSL2
public import CFSG.Quasithin.ChapterI.Section01.LieMultipliers.PSL4Two
public import CFSG.Quasithin.ChapterI.Section01.LieMultipliers.A2
public import Theory.GroupTheory.UniversalCoverKernelTransport
public import Theory.Alternating.theorem_5_2_3
public import Theory.SpecificGroups.Alternating.ThreeRank
public import Theory.SpecificGroups.SL2.OddProjectiveNonsolvable
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360
public import Mathlib.Data.Nat.Factorization.PrimePow

/-!
# Alternating and degree-two catalogue cases of I.1.3

Three independent three-cycles exclude Aₙ for n ≥ 9. The remaining four
alternating groups use their genuine universal covers: A₅ through PSL₂(5),
A₆ and A₇ through Schur's exceptional cyclic-six covers, and A₈ through the
actual PSL₄(2) comparison. The degree-two calculation retains q = 9 as A₆
and q = 4 as A₅; ordinary even fields have trivial canonical multiplier.
The binary PSL₃(2) alias is connected to the odd PSL₂(7) row.

Every result concerns the original group's canonical multiplier. Kernel
transport uses actual universal-cover isomorphisms, not just orders.
Source: Aschbacher--Smith I.1.3(1),(3), printed p.407; GLS3 Theorem 5.2.3.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterI.SQTKMultipliers
open Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups
universe u
variable {S : Type u} [Group S] [Finite S] [Group.IsPerfect S]

omit [Finite S] in
/-- Perfectness excludes the prime-cyclic constructor of the full catalogue. -/
theorem not_primeCyclic [IsSimpleGroup S] : ¬ KnownSimple.IsPrimeCyclicCarrier S := by
  rintro ⟨p, hp, ⟨e⟩⟩
  let : Fact p.Prime := ⟨hp⟩
  let : Group.IsPerfect (Multiplicative (ZMod p)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact Group.IsPerfect.not_isMulCommutative (Multiplicative (ZMod p)) inferInstance

/-- The ordinary odd degree-two value, with the small solvable fields excluded
by the source group's perfectness and simplicity. -/
theorem multiplier_odd_psl2 [IsSimpleGroup S] {q : ℕ}
    (ho : Odd q) (h9 : q ≠ 9) (hS : ClassicalGroup.IsPSL S 2 q) :
    Nonempty (schurMultiplier S ≃* Multiplicative (ZMod 2)) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hS
  let := hF
  let := hfin
  let : Group.IsPerfect PSL(2, F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : Nontrivial PSL(2, F) := e.injective.nontrivial
  have hoF : Odd (Nat.card F) := hcard ▸ ho
  have hlarge := Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
    hoF (Group.IsPerfect.not_isSolvable PSL(2, F))
  let : Fact (3 < Nat.card F) := ⟨hlarge⟩
  exact ⟨(schurMultiplierEquivOfUniversal e (GorensteinWalter.PSL2Cover.cover F)
    (GorensteinWalter.PSL2Cover.isUniversal_of_odd F hoF (hcard ▸ h9))).trans
      (GorensteinWalter.PSL2Cover.kernelEquivTwo F hoF)⟩

/-- Schur's actual universal cyclic-six cover of A₆ computes the canonical kernel. -/
theorem multiplier_a6 (e : S ≃* alternatingGroup (Fin 6)) :
    Nonempty (schurMultiplier S ≃* Multiplicative (ZMod 6)) := by
  obtain ⟨L, hL, hfin, hq, f, hu, hc, hn⟩ :=
    GLS3.Chapter5.SchurPresentation.theorem_5_2_3_c_multiplier_a6.{u}
  let := hL
  let := hfin
  let := hq
  let := hc
  exact ⟨(schurMultiplierEquivOfUniversal e f hu).trans
    (mulEquivOfCyclicCardEq (hn.trans (by simp)))⟩

/-- The independent exceptional A₇ calculation likewise retains the cyclic structure. -/
theorem multiplier_a7 (e : S ≃* alternatingGroup (Fin 7)) :
    Nonempty (schurMultiplier S ≃* Multiplicative (ZMod 6)) := by
  obtain ⟨L, hL, hfin, hq, f, hu, hc, hn⟩ :=
    GLS3.Chapter5.SchurPresentation.theorem_5_2_3_c_multiplier_a7.{u}
  let := hL
  let := hfin
  let := hq
  let := hc
  exact ⟨(schurMultiplierEquivOfUniversal e f hu).trans
    (mulEquivOfCyclicCardEq (hn.trans (by simp)))⟩

/-- The complete six-row value, without an additional multiplier premise. -/
theorem multiplier_six (h : MultiplierRow S .six) :
    Nonempty (schurMultiplier S ≃* MultiplierShape.six.Carrier) := by
  change Nonempty (S ≃* alternatingGroup (Fin 6)) ∨
    Nonempty (S ≃* alternatingGroup (Fin 7)) at h
  rcases h with h | h
  · exact multiplier_a6 h.some
  · exact multiplier_a7 h.some

omit [Finite S] [Group.IsPerfect S] in
/-- A₅ belongs to the odd PSL₂(5) row through the actual model comparison. -/
theorem a5_isPSL_five (e : S ≃* alternatingGroup (Fin 5)) :
    ClassicalGroup.IsPSL S 2 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact ⟨ZMod 5, inferInstance, inferInstance, by simp,
    ⟨e.trans Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five.some.symm⟩⟩

omit [Finite S] [Group.IsPerfect S] in
/-- A₈ belongs to the L₄(2) row through the checked binary matrix comparison. -/
theorem a8_isPSL_four_two (e : S ≃* alternatingGroup (Fin 8)) :
    ClassicalGroup.IsPSL S 4 2 :=
  ⟨ZMod 2, inferInstance, inferInstance, by simp,
    ⟨e.trans (Matrix.PSL4Two.binaryEquivAlternatingEight (ZMod 2) (by simp)).symm⟩⟩

omit [Group.IsPerfect S] in
/-- Strong quasithinness bounds the degree in the complete alternating catalogue. -/
theorem alternating_degree_le_eight {n : ℕ}
    (h : IsStronglyQuasithin S) (e : S ≃* alternatingGroup (Fin n)) : n ≤ 8 := by
  by_contra hn
  have hr := alternatingGroup.ThreeRank.three_le_primeRank (n := n) (by omega)
  have hb := h 3 (by decide) (by decide)
  have hle := Theory.GroupTheory.primeRank_le_of_injective 3
    e.symm.toMonoidHom e.symm.injective
  omega

/-- Every alternating constructor of the full catalogue is calculated or excluded. -/
theorem calculated_alternating [IsSimpleGroup S] {n : ℕ} (hn : 5 ≤ n)
    (h : IsStronglyQuasithin S) (e : S ≃* alternatingGroup (Fin n)) : Calculated S := by
  have h8 := alternating_degree_le_eight h e
  interval_cases n
  · have h5 := a5_isPSL_five e
    exact Or.inr ⟨.two, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨5, by decide, by decide, h5⟩))))), multiplier_odd_psl2 (by decide) (by decide) h5⟩
  · exact Or.inr ⟨.six, Or.inl ⟨e⟩, multiplier_a6 e⟩
  · exact Or.inr ⟨.six, Or.inr ⟨e⟩, multiplier_a7 e⟩
  · have h4 := a8_isPSL_four_two e
    exact Or.inr ⟨.two, Or.inl h4, LieMultipliers.PSL4Two.schurMultiplier_equiv_two h4⟩

/-- Ordinary even fields have trivial canonical multiplier. -/
theorem multiplier_even_psl2 {q : ℕ} (hq : 8 ≤ q) (he : Even q)
    (hS : ClassicalGroup.IsPSL S 2 q) : Subsingleton (schurMultiplier S) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hS
  let := hF
  let := hfin
  let : Fact (3 < Nat.card F) := ⟨by omega⟩
  let k : schurMultiplier S ≃* (PUnit : Type) := (schurMultiplierEquivOfUniversal e
    (Covering.id : Covering PSL(2, F) PSL(2, F))
    (GorensteinWalter.PSL2Cover.identity_isUniversal_of_even F
      (hcard ▸ he) (by omega))).trans
    (GorensteinWalter.PSL2Cover.identityKernelEquivOne F)
  exact k.injective.subsingleton

omit [Finite S] [Group.IsPerfect S] in
/-- The q = 4 endpoint is placed in row (1) through PSL₂(5), not through
an incorrectly trivial ordinary SL₂(4) projection kernel. -/
theorem psl2_four_isPSL_five (hS : ClassicalGroup.IsPSL S 2 4) :
    ClassicalGroup.IsPSL S 2 5 := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hS
  exact a5_isPSL_five
    (e.trans (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hcard).some)

omit [Finite S] [Group.IsPerfect S] in
/-- The q = 9 endpoint is the actual A₆ model in row (3). -/
theorem psl2_nine_equiv_a6 (hS : ClassicalGroup.IsPSL S 2 9) :
    Nonempty (S ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hS
  exact ⟨e.trans (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hcard)⟩

/-- All admissible degree-two parameters are covered, including both small aliases. -/
theorem calculated_psl2 [IsSimpleGroup S] {q : ℕ} (hq : 4 ≤ q)
    (hS : ClassicalGroup.IsPSL S 2 q) : Calculated S := by
  by_cases h9 : q = 9
  · obtain ⟨e⟩ := psl2_nine_equiv_a6 (h9 ▸ hS)
    exact Or.inr ⟨.six, Or.inl ⟨e⟩, multiplier_a6 e⟩
  by_cases h4 : q = 4
  · have h5 := psl2_four_isPSL_five (h4 ▸ hS)
    exact Or.inr ⟨.two, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨5, by decide, by decide, h5⟩))))), multiplier_odd_psl2 (by decide) (by decide) h5⟩
  rcases Nat.even_or_odd q with he | ho
  · have h8 : 8 ≤ q := by
      obtain ⟨F, hF, hfin, hc, _⟩ := hS
      let := hF
      let := hfin
      let := Fintype.ofFinite F
      have hpp : IsPrimePow q := by
        rw [← hc, Nat.card_eq_fintype_card]
        exact FiniteField.isPrimePow_card F
      have h6 : q ≠ 6 := by
        rintro rfl
        have huniq := isPrimePow_iff_unique_prime_dvd.mp hpp
        have heq : (2 : ℕ) = 3 := huniq.unique (by decide) (by decide)
        omega
      obtain ⟨k, hk⟩ := he
      omega
    exact Or.inl (multiplier_even_psl2 h8 he hS)
  · exact Or.inr ⟨.two, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨q, ho, h9, hS⟩))))), multiplier_odd_psl2 ho h9 hS⟩

/-- The binary degree-three endpoint uses the checked PSL₂(7) alias. -/
theorem calculated_psl3_two [IsSimpleGroup S] (hS : ClassicalGroup.IsPSL S 3 2) :
    Calculated S :=
  calculated_psl2 (by decide : 4 ≤ 7)
    (LieMultipliers.A2.isPSL_two_seven_of_isPSL_three_two hS)

end CFSG.Quasithin.ChapterI.SQTKMultipliers
