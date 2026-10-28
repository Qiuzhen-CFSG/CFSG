module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.SecondCenterImage
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockSecondCenterSquares

/-!
# Canonical upper commutator data in the original nonblock configuration

The genuine field-four nonabelian source supplies its whole natural or
doubled center at a common full SL₃ marking. At that marking the canonical
B=[Z₂(Q),Q] is the whole center in the natural branch, and is either the
whole center or a natural central flag in the doubled branch. It is
nontrivial, lies in Q′ and Φ(Q), and is normalized by the original KS.

The literal C_Q(Z₂(Q)) is proper, contains Φ(Q), and is KS-normal. The
whole quotient by that centralizer is elementary and embeds by commutators
in Hom(Z₂(Q)/Z(Q),Z(Q)), with evaluation and automorphism transport on the
original quotient maps. The original MS3 condition also proves that B is
not characteristic in the original radical O₂(I).

The model premise is discharged using the same c, ChosenModule D,
constrained hf, field size and full quotient equivalence as the original
consumer. No Hypothesis1223 or upper-section classification premise is
introduced. Recognition and exhaustion of the upper dual sections,
exclusion of the nonabelian doubled center, and the general fourth row
remain with C.1.34 assembly.
Source: Aschbacher–Smith C.1.31 and C.1.34, printed pp.135–137, and
original 4.3.8–10, pp.616–617.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SecondCenterImage
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterC.LinearThreeMS.NonbinarySource.SecondCenterImage
open ChapterC.LinearThreeMS.NonbinarySource.SecondCenterSections
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
  (hf : generalizedFitting c.K = pCore 2 c.K)
  (n : ℕ) (hn : 1<n) (hF : Nat.card F=2^n)
  (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
include D hf hn hF e
local notation "T₂" => Subgroup.upperCentralSeries (Q c) 2
local notation "V₂" => (T₂ ⧸ Subgroup.subgroupOf (center (Q c)) T₂)
local notation "C₂" => centralizer (T₂ : Set (Q c))
local notation "B₂" => (⁅secondCenterIn (Q c),Q c⁆ : Subgroup G)

/-- The genuine field-four source supplies a nonzero canonical central image,
its natural/doubled alternatives at one marking, and the faithful effective
second variable with the original quotient maps. MS3 rules out
characteristicity of this layer in the original radical. -/
theorem source_nonabelian_upper_image
    (hfour : Nat.card F=4) (hna : ¬IsMulCommutative (Q c)) :
    ∃ mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F),
      IsElementaryAbelian 2 (center (Q c)) ∧
      B₂≠⊥ ∧ B₂≤U c ∧ B₂≤⁅Q c,Q c⁆ ∧ B₂≤frattiniIn (Q c) ∧
      K c ⊔ S c ≤ normalizer (B₂ : Set G) ∧
      ((B₂=U c ∧ HasSectionModel (K c) (U c) ⊥ (linearThreeActor mark) (specialLinearNatural 3)) ∨
        (HasSectionModel (K c) (U c) ⊥ (linearThreeActor mark)
            ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) ∧
          (B₂=U c ∨ (HasSectionModel (K c) B₂ ⊥ (linearThreeActor mark) (specialLinearNatural 3) ∧
            HasSectionModel (K c) (U c) B₂ (linearThreeActor mark) (specialLinearNatural 3))))) ∧
      (C₂).map (Q c).subtype = Q c ⊓ centralizer (secondCenterIn (Q c) : Set G) ∧
      frattiniIn (Q c) ≤ Q c ⊓ centralizer (secondCenterIn (Q c) : Set G) ∧
      Q c ⊓ centralizer (secondCenterIn (Q c) : Set G) < Q c ∧
      K c ⊔ S c ≤ normalizer ((Q c ⊓ centralizer (secondCenterIn (Q c) : Set G) : Subgroup G) : Set G) ∧
      IsElementaryAbelian 2 ((Q c) ⧸ C₂) ∧
      (∃ b : ((Q c) ⧸ C₂) →* (V₂ →* center (Q c)), Function.Injective b ∧
        (∀ (x : T₂) (y : Q c),
          (b (QuotientGroup.mk' C₂ y) (QuotientGroup.mk' _ x):Q c)=⁅(x:Q c),y⁆) ∧
        (∀ (a : MulAut (Q c)) (x : T₂) (y : Q c),
          b (QuotientGroup.mk' C₂ (a y))
            (QuotientGroup.mk' _ (MulAut.characteristic T₂ a x)) =
          centerCongr a (b (QuotientGroup.mk' C₂ y) (QuotientGroup.mk' _ x)))) ∧
      ¬ ((B₂).subgroupOf (c.I.pCoreIn 2)).Characteristic := by
  obtain ⟨mark,_,_,_,hm⟩ := DoubledCenter.source_nonabelian_center_models c D hf n hn hF e hfour hna
  have hQ : IsPGroup 2 (Q c) := T.isPGroup'.to_le ((core_le_sylow c).trans inf_le_left)
  have hnorm : K c ⊔ S c ≤ normalizer (Q c : Set G) :=
    (sup_le (map_subtype_le _) inf_le_right).trans (core_normalized c)
  have hKQ : K c ≤ normalizer (Q c : Set G) := le_sup_left.trans hnorm
  have hi : IsElementaryAbelian 2 (center (Q c)) := by
    rcases hm with hm|hm
    · exact (ChapterC.LinearThreeMS.NonbinarySource.SecondCenterSquares.exists_marked_squares
        (linearThreeActor mark) _ hm.1).1
    · exact (ChapterC.LinearThreeMS.NonbinarySource.SecondCenterSquares.exists_marked_squares
        (linearThreeActor mark) _ hm).1
  let := hi
  obtain ⟨hb,hbz,hbd,hbp,hbn⟩ := image_structure hQ hna
  obtain ⟨hCP,hCQ,hCN,hCE⟩ := effective_section_structure hQ hna
  refine ⟨mark,hi,hb,hbz,hbd,hbp,hnorm.trans hbn,?_,centralizer_image,
    hCP,hCQ,hnorm.trans hCN,hCE,?_,?_⟩
  · rcases hm with hm|hm
    · exact Or.inl ⟨natural_image_eq hQ hna hKQ mark hm.1,hm.1⟩
    · exact Or.inr ⟨hm,doubled_image_sections hQ hna hKQ mark hm⟩
  · exact ⟨SecondCenterFrattini.rightPairing,SecondCenterFrattini.rightPairing_injective,
      SecondCenterFrattini.rightPairing_apply,SecondCenterFrattini.rightPairing_automorphism⟩
  · have hp := msPair_of_quotient c D hf n (by omega) hF e
    have hh := ms_image_not_characteristic_radical hp hn
    rw [ms_commutator_eq c] at hh
    exact hh hna

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SecondCenterImage
