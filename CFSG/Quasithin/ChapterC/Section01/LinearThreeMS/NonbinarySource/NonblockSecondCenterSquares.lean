module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.SecondCenterSquares
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockSecondCenter

/-!
# Original nonblock square coordinates and elementary upper lifts

The genuine field-four nonabelian source configuration supplies a model of
its whole center, natural or doubled natural at one full SL₃ marking.
At that same marking construct the square map on Z₂(Q)/Z(Q), with its
literal alternating commutator polarization. The embedded Φ(Z₂(Q)) lies
in the whole U=Z(Q) and is normalized by the full KS.

Every dual-natural subsection of this upper quotient has an elementary
full preimage, with both center summands retained in the doubled branch.
This universal lift assertion does not claim that a dual subsection exists
or that such subsections exhaust Q/Z(Q). Those recognition steps, exclusion
of the nonabelian doubled center, and the arbitrary-degree fourth row remain
with the full C.1.34 assembly. No classification, whole-upper-model, or
Hypothesis1223 premise is added to this source application.

Source: Aschbacher–Smith C.1.34–35, printed pp.136–138, applied to the
original 4.3.8–10 configuration, pp.616–617.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SecondCenterSquares
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterC.LinearThreeMS.NonbinarySource.SecondCenterSquares
open ChapterC.LinearThreeMS.NonbinarySource.SecondCenterSections
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
  (hf : generalizedFitting c.K = pCore 2 c.K)
  (n : ℕ) (hn : 1<n) (hF : Nat.card F=2^n)
  (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
include D hf hn hF e
local notation "T₂" => Subgroup.upperCentralSeries (Q c) 2

/-- The original field-four nonabelian core has a marked quadratic upper
section and a central KS-normal second-center Frattini subgroup. Every
same-marking dual-natural subsection has an elementary full preimage. -/
theorem source_nonabelian_upper_squares (hfour : Nat.card F=4) (hna : ¬IsMulCommutative (Q c)) :
    ∃ mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F),
      IsElementaryAbelian 2 (center (Q c)) ∧
      let B := ((frattini T₂).map (T₂).subtype).map (Q c).subtype
      B ≤ U c ∧ K c ⊔ S c ≤ normalizer (B : Set G) ∧
      ((HasSectionModel (K c) (U c) ⊥ (linearThreeActor mark) (specialLinearNatural 3) ∧
        HasSquareCoordinates (K c) (Q c) (linearThreeActor mark) (specialLinearNatural 3)) ∨
       (HasSectionModel (K c) (U c) ⊥ (linearThreeActor mark)
          ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) ∧
        HasSquareCoordinates (K c) (Q c) (linearThreeActor mark)
          ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)))) ∧
      (∀ A : Subgroup G, A ≤ secondCenterIn (Q c) →
        HasSectionModel (K c) A (U c) (linearThreeActor mark) (specialLinearNatural 3).dual →
        IsElementaryAbelian 2 A) := by
  obtain ⟨mark,_,_,_,hm⟩ := DoubledCenter.source_nonabelian_center_models
    c D hf n hn hF e hfour hna
  have hmodels : HasSectionModel (K c) (U c) ⊥ (linearThreeActor mark) (specialLinearNatural 3) ∨
      HasSectionModel (K c) (U c) ⊥ (linearThreeActor mark)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) := hm.imp And.left id
  have hcoords : IsElementaryAbelian 2 (center (Q c)) ∧
      ((HasSectionModel (K c) (U c) ⊥ (linearThreeActor mark) (specialLinearNatural 3) ∧
        HasSquareCoordinates (K c) (Q c) (linearThreeActor mark) (specialLinearNatural 3)) ∨
       (HasSectionModel (K c) (U c) ⊥ (linearThreeActor mark)
          ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) ∧
        HasSquareCoordinates (K c) (Q c) (linearThreeActor mark)
          ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)))) := by
    rcases hmodels with hm|hm
    · obtain ⟨hi,hs⟩ := exists_marked_squares (linearThreeActor mark) _ hm
      exact ⟨hi,Or.inl ⟨hm,hs⟩⟩
    · obtain ⟨hi,hs⟩ := exists_marked_squares (linearThreeActor mark) _ hm
      exact ⟨hi,Or.inr ⟨hm,hs⟩⟩
  let := hcoords.1
  have hQ : IsPGroup 2 (Q c) := T.isPGroup'.to_le ((core_le_sylow c).trans inf_le_left)
  obtain ⟨hB,hBn⟩ := upper_frattini_structure hQ
  have hnorm : K c ⊔ S c ≤ normalizer (Q c : Set G) :=
    (sup_le (map_subtype_le _) inf_le_right).trans (core_normalized c)
  refine ⟨mark,hcoords.1,hB,hnorm.trans hBn,hcoords.2,?_⟩
  intro A hA hmA
  exact dual_section_elementary mark
    (hA.trans (map_subtype_le _)) hmodels hmA

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SecondCenterSquares
