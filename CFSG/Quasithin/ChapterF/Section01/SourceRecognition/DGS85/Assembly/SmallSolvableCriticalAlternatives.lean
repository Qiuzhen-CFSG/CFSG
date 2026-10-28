module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.TheoremBFullCatalogue
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.BinaryTransport
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallSolvableCriticalCommuting
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.EnlargementCatalogue
public import Theory.SpecificGroups.SU3.SmallSpecialExtraspecial

/-!
# Critical alternatives at a small solvable endpoint

The original D₁₀ or Sz(2) endpoint excludes noncommuting critical pairs.
When both original quotient orders are below 72, the retained small-unitary
exceptions to local enlargement are impossible, so the full DGS Theorem B
applies. Its distance-three zero-displacement branch would make every
original starred quotient SL₂(2). Transport through the literal original
quotient inclusion contradicts the D₁₀/Sz(2) marking.

Thus only distance one or distance three with nonzero displacement remains.
The Chapter 15 marked-five/S₃ and wreath mixed A₅ pairs consume this result;
no final recognition or exclusion of those remaining branches is asserted.

Source: DGS, *Groups and Graphs* (1985), Theorem B, p.102, and 9.10,
pp.147–150; Aschbacher–Smith 15.2.4–8, printed pp.1106–1110.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => Reduction.reducedFamily L S

private theorem no_small_unitary_of_card_lt {A : Type*} [Group A]
    (hc : Nat.card A < 72) :
    ¬ ClassicalGroup.IsPSU A 3 2 ∧ ¬ IsSU A 3 2 := by
  constructor
  · rintro ⟨K,hK,hfin,J,hcard,hconj,⟨e⟩⟩
    let := hK
    let := hfin
    have he : Nat.card A = 72 := (Nat.card_congr e.toEquiv).trans
      (HermitianForm.FixedFieldTwo.card_projective J hcard hconj)
    omega
  · rintro ⟨K,hK,hfin,J,hcard,hconj,⟨e⟩⟩
    let := hK
    let := hfin
    have he : Nat.card A = 216 := (Nat.card_congr e.toEquiv).trans
      (HermitianForm.SmallThreeCore.special_group_card J hcard hconj)
    omega

/-- The literal small-solvable endpoint excludes both the noncommuting and
zero-displacement cases; only distance one or nonzero distance three remains. -/
theorem reduced_small_solvable_critical_alternatives
    (h : HypothesisF11 L S) (j : Bool)
    (hm : Nonempty ((family L j ⧸ pCore 2 (family L j)) ≃* DihedralGroup 5) ∨
      Nonempty ((family L j ⧸ pCore 2 (family L j)) ≃* SuzukiMatrixGroup 0))
    (hcard : ∀ i, Nat.card (L i ⧸ pCore 2 (L i)) < 72)
    {a beta a' : Vertex F} (hc : IsCriticalPair F a a')
    (hab : (graph F).Adj a beta) (hd : (graph F).dist beta a' + 1 = b F) :
    ⁅Z F a,Z F a'⁆ = ⊥ ∧
      (b F = 1 ∨ (b F = 3 ∧ ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ ≠ ⊥)) := by
  have models := Reduction.reduced_actor_models_of_no_small_unitary h
    (fun i => no_small_unitary_of_card_lt (hcard i))
  have hcomm := Reduction.reduced_critical_commuting_of_small_solvable h j hm hc
  refine ⟨hcomm,?_⟩
  rcases reduced_critical_alternatives_from_full_catalogue h models hc hab hd with
    ⟨hn,_⟩ | ⟨_,hb⟩
  · exact (hn hcomm).elim
  rcases hb with hb | hb
  · exact Or.inl hb
  right
  refine ⟨hb,?_⟩
  intro htriv
  obtain ⟨_,K,hK,finK,charK,E,hE,finE,charE,hcardK,hcardE,⟨eb⟩,⟨ea⟩⟩ :=
    CommutingTrivial.reduced_critical_fields_two_from_chapterEight
    h models hc hab hd (by omega) hcomm htriv
  let := hK
  let := finK
  let := charK
  let := hE
  let := finE
  let := charE
  have he := CommutingTrivial.adjacent_field_two_starred_quotients
    h hab ea eb (hcardE.trans hcardK.symm) hcardK
  let e := (CommutingThreeProfile.ReducedLayer.originalQuotient h j).trans (he j).some
  have hsix0 : Nat.card (L (if j then 1 else 0) ⧸ pCore 2 (L (if j then 1 else 0))) = 6 := by
    rw [Nat.card_congr e.toEquiv,BenderSuzuki.External.huppert614_card_specialLinearGroup]
    norm_num [Nat.card_eq_fintype_card]
  have hsix : Nat.card (family L j ⧸ pCore 2 (family L j)) = 6 := by
    cases j <;> exact hsix0
  rcases hm with hm | hm
  · rw [Nat.card_congr hm.some.toEquiv,DihedralGroup.nat_card] at hsix
    norm_num at hsix
  · rw [Nat.card_congr hm.some.toEquiv,suzukiZero_card] at hsix
    norm_num at hsix

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly
