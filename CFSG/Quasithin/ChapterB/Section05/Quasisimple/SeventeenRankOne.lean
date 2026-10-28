module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract
public import Theory.SpecificGroups.Classical.SeventeenFiveRank
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Selecting the natural rank-one row using seventeen and five-rank

The complete B.5.1 moved-section conclusion, for an actor whose order is
divisible by 17 and whose five-rank is one, has the natural binary SL₂ row.
The split or nonsplit torus excludes the larger binary families; their
orders exclude every small row. The conclusion retains the actual action
equivalence, quadratic ratio and Sylow best offenders.

This specializes the proved classification on its original moved section;
it does not replace the classification by a group-family tag. The consumer
is the C.2.7 star action in the exchanged PSL₂(16) branch of 14.6.15.
Source: Aschbacher–Smith B.4.2, B.5.1 and 14.6.15, pp.86, 99–103, 1035.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.SourceInduction.ProjectiveLine.SeventeenRankOne
open ChapterB.QuasisimpleSource

private theorem no_linearThree {E : Type*} [Group E] [Finite E]
    (h17 : 17 ∣ Nat.card E) (hr : primeRank 5 E = 1)
    (F : BinaryField) (e : E ≃* SL(3,F.Carrier)) : False := by
  have hl := Theory.SpecificGroups.Classical.SeventeenFiveRank.linearThree F.card_eq
    (by rwa [←Nat.card_congr e.toEquiv])
  rw [←primeRank_congr 5 e,hr] at hl
  omega

private theorem no_symplectic {E : Type*} [Group E] [Finite E]
    (h17 : 17 ∣ Nat.card E) (hr : primeRank 5 E = 1)
    (F : BinaryField) (e : E ≃* Matrix.symplecticGroup (Fin 2) F.Carrier) : False := by
  have hl := Theory.SpecificGroups.Classical.SeventeenFiveRank.symplectic F.card_eq
    (by rwa [←Nat.card_congr e.toEquiv])
  rw [←primeRank_congr 5 e,hr] at hl
  omega

private theorem no_g2 {E : Type*} [Group E] [Finite E]
    (h17 : 17 ∣ Nat.card E) (hr : primeRank 5 E = 1)
    (F : BinaryField) (e : E ≃* Atlas.G2.Model F.Carrier) : False := by
  have hl := Theory.SpecificGroups.Classical.SeventeenFiveRank.g2 F.card_eq
    (by rwa [←Nat.card_congr e.toEquiv])
  rw [←primeRank_congr 5 e,hr] at hl
  omega

private theorem no_binaryLinear {E : Type*} [Group E] (h17 : 17 ∣ Nat.card E)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (e : E ≃* SL(d,ZMod 2)) : False := by
  have hh := h17.trans ((Nat.card_congr e.toEquiv).symm ▸
    card_dvd_of_injective (Matrix.SpecialLinearGroup.toGL (n := Fin d) (R := ZMod 2))
      Matrix.SpecialLinearGroup.toGL_injective)
  rcases hd with rfl | rfl <;> rw [Matrix.card_GL_field] at hh <;>
    norm_num [Fin.prod_univ_succ] at hh

private theorem no_alternating {E : Type*} [Group E] (h17 : 17 ∣ Nat.card E)
    {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
    (e : E ≃* alternatingGroup (Fin n)) : False := by
  rw [Nat.card_congr e.toEquiv] at h17
  rcases hn with rfl | rfl | rfl | rfl <;>
    rw [nat_card_alternatingGroup] at h17 <;>
    norm_num [Nat.card_eq_fintype_card,Nat.factorial] at h17

private noncomputable def binarySymplecticDerivedEquiv :
    commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) ≃* alternatingGroup (Fin 6) := by
  let e := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
  refine (e.subgroupMap _).trans (MulEquiv.subgroupCongr ?_)
  rw [map_commutator_eq,MonoidHom.range_eq_top.mpr e.surjective]
  exact alternatingGroup.commutator_perm_eq (by norm_num)

universe u v
variable {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) {C J : Subgroup D}

private theorem irreducible_seventeen_natural
    (h : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ C J)
    (h17 : 17 ∣ Nat.card C) (hr : primeRank 5 C = 1) :
    ∃ F : BinaryField,
      Nonempty (ActionEquiv (ρ.comp C.subtype) (linearNatural F 2)) ∧
      quadraticRatio ρ = 1 ∧
      ∀ B, IsBestOffender ρ B → ∃ S : Sylow 2 C, B = (S : Subgroup C).map C.subtype := by
  cases h with
  | linearTwo F _ a ho hq => exact ⟨F,⟨a⟩,hq,ho⟩
  | linearThree F _ a _ => exact (no_linearThree h17 hr F a.groupEquiv).elim
  | symplectic F _ _ a _ => exact (no_symplectic h17 hr F a.groupEquiv).elim
  | symplecticTwo a _ =>
    exact (no_alternating h17 (Or.inr (Or.inl rfl))
      (a.subgroupEquiv.trans binarySymplecticDerivedEquiv)).elim
  | g2 F _ _ a _ _ => exact (no_g2 h17 hr F a.groupEquiv).elim
  | g2Two a _ _ =>
    rw [Nat.card_congr a.subgroupEquiv.toEquiv,
      Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at h17
    norm_num at h17
  | symmetric n hn a _ _ =>
    exact (no_alternating h17 (by rcases hn with rfl | rfl <;> simp) a.subgroupEquiv).elim
  | alternatingSix _ a _ _ =>
    exact (no_alternating h17 (Or.inr (Or.inl rfl)) a.groupEquiv).elim
  | alternatingSeven _ _ a _ _ _ =>
    exact (no_alternating h17 (Or.inr (Or.inr (Or.inl rfl))) a).elim
  | tripleSix _ a _ =>
    have hc : Nat.card C = 3 * 360 := by
      rw [←(center C).card_mul_index,index_eq_card,Nat.card_congr a.centerEquiv.toEquiv,
        Nat.card_congr a.quotientEquiv.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.card_eq_fintype_card,Nat.factorial]
    rw [hc] at h17
    norm_num at h17
  | binaryLinear d hd _ a _ => exact (no_binaryLinear h17 hd a.groupEquiv).elim
  | orthogonalSix _ _ a _ _ =>
    exact (no_alternating h17 (Or.inr (Or.inr (Or.inr rfl))) a.groupEquiv).elim
  | symmetricEight _ a _ =>
    exact (no_alternating h17 (Or.inr (Or.inr (Or.inr rfl))) a.subgroupEquiv).elim
  | exteriorFive _ _ a _ _ _ => exact (no_binaryLinear h17 (Or.inr rfl) a).elim

/-- Seventeen divisibility and five-rank one select the actual natural row
of the complete B.5.1 moved-section conclusion, including its offenders. -/
theorem source_natural
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ C)
    (h17 : 17 ∣ Nat.card C) (hr : primeRank 5 C = 1) :
    ∃ F : BinaryField,
      Nonempty (ActionEquiv (c.sectionData.action.comp C.subtype) (linearNatural F 2)) ∧
      quadraticRatio c.sectionData.action = 1 ∧
      ∀ B, IsBestOffender c.sectionData.action B →
        ∃ S : Sylow 2 C, B = (S : Subgroup C).map C.subtype := by
  cases c.clause_one with
  | irreducible _ _ _ hs _ => exact irreducible_seventeen_natural _ hs h17 hr
  | doubleThree F _ a _ _ => exact (no_linearThree h17 hr F a.groupEquiv).elim
  | naturalDual d hd _ hn =>
    obtain ⟨a⟩ := hn
    exact (no_binaryLinear h17 hd a.groupEquiv).elim
  | repeatedNatural d r hd _ _ _ hn =>
    obtain ⟨a⟩ := hn
    exact (no_binaryLinear h17 hd a.groupEquiv).elim

end CFSG.Quasithin.ChapterB.SourceInduction.ProjectiveLine.SeventeenRankOne
