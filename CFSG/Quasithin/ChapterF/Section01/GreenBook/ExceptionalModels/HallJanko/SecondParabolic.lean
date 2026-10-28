module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic
public import Theory.SpecificGroups.SL2.BinaryProjective
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.HallJanko
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.HallJanko.SecondParabolic.Markings

/-!
# The source second-local calculations for the Hall--Janko markings

The actual three-point projective action identifies S₃ with SL₂(2), and the
canonical central quotient identifies SL₂(2) with PSL₂(2). This converts the
proved concrete radical quotient into all four requested second-local outputs
for F.1.12(I)(10)--(11).

The whole-overlap markings below discharge the full-normalizer quotient input
and require only the independent first-centralizer order 1920. Their Borels
have orders 384 and 768, while their fixed Sylow subgroups have orders 128
and 256. Both local Borel factors are retained. First-factor calculations
and transport to the full automorphism group belong to the parent assembly.
Source: Aschbacher--Smith, printed p.263 (PDF p.274).
-/

public section
namespace CFSG.Quasithin.ChapterF.GreenBook.HallJanko.SecondParabolic
open Theory.GroupTheory
open Sporadic.LeechRelated.J2
open Sporadic.LeechRelated.J2.ExceptionalParabolics

/-- Identify the binary source model by an actual multiplicative equivalence. -/
theorem isPSL_two_two_of_perm_three {G : Type*} [Group G]
    (h : Nonempty (G ≃* Equiv.Perm (Fin 3))) : ClassicalGroup.IsPSL G 2 2 := by
  obtain ⟨e⟩ := h
  obtain ⟨f⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  exact ⟨ZMod 2, inferInstance, inferInstance, by simp,
    ⟨e.trans (f.symm.trans Matrix.SpecialLinearGroup.sl2TwoEquivPSL2Two)⟩⟩

/-- Assemble both source second-factor calculations from a relative radical quotient. -/
theorem second_local_calculations_of_radical_quotient
    (hq : Nonempty ((Seed.l₂ ⧸ Seed.q₂.subgroupOf Seed.l₂) ≃* Equiv.Perm (Fin 3))) :
    ClassicalGroup.IsPSL (Seed.l₂ ⧸ pCore 2 Seed.l₂) 2 2 ∧
      Nat.card (pCore 2 Seed.l₂) = 64 ∧
      Nonempty ((Seed.outerL 1 ⧸ pCore 2 (Seed.outerL 1)) ≃* Equiv.Perm (Fin 3)) ∧
      Nat.card (pCore 2 (Seed.outerL 1)) = 64 :=
  ⟨isPSL_two_two_of_perm_three
      (Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.l₂_quotient_of_radical_quotient hq),
    Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.l₂_core_card_of_radical_quotient hq,
    Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.outerL₂_quotient_of_radical_quotient hq,
    Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.outerL₂_core_card_of_radical_quotient hq⟩

/-- All second-factor clauses of F.1.12(I)(10)--(11), with no quotient or core premises. -/
theorem second_local_calculations :
    ClassicalGroup.IsPSL (Seed.l₂ ⧸ pCore 2 Seed.l₂) 2 2 ∧
      Nat.card (pCore 2 Seed.l₂) = 64 ∧
      Nonempty ((Seed.outerL 1 ⧸ pCore 2 (Seed.outerL 1)) ≃* Equiv.Perm (Fin 3)) ∧
      Nat.card (pCore 2 (Seed.outerL 1)) = 64 :=
  second_local_calculations_of_radical_quotient
    Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.l₂_radical_quotient

/-- The source PSL₂(2) identification on the literal second factor. -/
theorem l₂_quotient_isPSL : ClassicalGroup.IsPSL (Seed.l₂ ⧸ pCore 2 Seed.l₂) 2 2 :=
  second_local_calculations.1

/-- The whole-overlap carrier marking needs only the independent first-factor order. -/
@[expose] def sourceMarking (h₁ : Nat.card Seed.l₁ = 1920) : Marking Carrier :=
  marking h₁ PairNormalizer.p₂_quotient_equiv

/-- The whole-overlap extension marking has the same sole first-factor premise. -/
@[expose] def outerSourceMarking (h₁ : Nat.card Seed.l₁ = 1920) : Marking Extension :=
  outerMarking h₁ PairNormalizer.p₂_quotient_equiv

variable (h₁ : Nat.card Seed.l₁ = 1920)

@[simp] theorem sourceMarking_L : (sourceMarking h₁).L = Seed.L := rfl

@[simp] theorem sourceMarking_S :
    ((sourceMarking h₁).S : Subgroup Carrier) = Seed.s := rfl

@[simp] theorem outerSourceMarking_L : (outerSourceMarking h₁).L = Seed.outerL := rfl

@[simp] theorem outerSourceMarking_S :
    ((outerSourceMarking h₁).S : Subgroup Extension) = Seed.outerS := rfl

/-- The carrier's whole Borel includes its odd factor of order three. -/
theorem card_sourceMarking_B : Nat.card (sourceMarking h₁).B = 384 :=
  card_marking_B h₁ PairNormalizer.p₂_quotient_equiv

/-- The outer involution doubles the whole Borel. -/
theorem card_outerSourceMarking_B : Nat.card (outerSourceMarking h₁).B = 768 :=
  card_outerMarking_B h₁ PairNormalizer.p₂_quotient_equiv

theorem card_sourceMarking_S : Nat.card ((sourceMarking h₁).S : Subgroup Carrier) = 128 :=
  PairNormalizer.card_s

theorem card_outerSourceMarking_S :
    Nat.card ((outerSourceMarking h₁).S : Subgroup Extension) = 256 :=
  Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.card_outerS

end CFSG.Quasithin.ChapterF.GreenBook.HallJanko.SecondParabolic
