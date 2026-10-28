module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.CentralInvariantFlags
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockDoubledCenter

/-!
# A normal central flag in the original nonabelian core

The original full Sylow intersection normalizes both K and Q. It therefore
permutes the odd projective-line family in a doubled natural whole center.
Choose a fixed natural summand in Z(Q) ∩ Q', using that canonical intersection
itself when proper. This makes the central flag invariant under the full
original KS, with its bottom in both Q' and Φ(Q), at the supplied SL₃ marking.

For the original field-four nonabelian configuration, the genuine whole-center
recognition then supplies this flag without a module-classification or radical-
invariance premise: the bottom is the whole natural center, or has natural
quotient in the doubled center. The original c, ChosenModule D, constrained hf,
field and full quotient are retained. No Hypothesis1223 is used.

This strengthens the earlier central flags by supplying their missing radical
invariance. The nonabelian doubled-center exclusion and the upper/Frattini
section recognition, including the arbitrary-degree fixed factor, remain
required for full C.1.34 and its original nonblock classification consumer.
Source: Aschbacher–Smith original 4.3.8–10, printed pp.616–617, and C.1.34,
pp.136–137; compare the odd projective-line family in C.1.35, pp.137–139.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.CentralInvariantFlags
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterC.LinearThreeMS.NonbinarySource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
  (hf : generalizedFitting c.K = pCore 2 c.K)
  (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
  (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
include D hf hn hF e
local notation "O" => Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (Q c)

/-- The original doubled-omega branch has a natural central flag inside
Q' and Φ(Q) invariant under the full original KS, for every n>1. -/
theorem source_doubled_derived_normal_flag
    (mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) O ⊥ (linearThreeActor mark)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)))
    (hna : ¬ IsMulCommutative (Q c)) :
    ∃ B : Subgroup G, ⊥ < B ∧ B < U c ∧ B ≤ ⁅Q c,Q c⁆ ∧ B ≤ frattiniIn (Q c) ∧
      K c ⊔ S c ≤ normalizer (B : Set G) ∧
      HasSectionModel (K c) B ⊥ (linearThreeActor mark) (specialLinearNatural 3) ∧
      HasSectionModel (K c) (U c) B (linearThreeActor mark) (specialLinearNatural 3) := by
  have hQ : IsPGroup 2 (Q c) :=
    T.isPGroup'.to_le ((core_le_sylow c).trans inf_le_left)
  have hKQ : K c ≤ normalizer (Q c : Set G) := (map_subtype_le _).trans (core_normalized c)
  have heven : Even (Nat.card F) := by
    rw [hF]
    exact even_two.pow_of_ne_zero (by omega : n ≠ 0)
  exact ChapterC.LinearThreeMS.NonbinarySource.CentralInvariantFlags.exists_derived_invariant_flag
    hQ hKQ heven mark (DoubledCenter.source_doubled_center c D hf n hn hF e mark hm).2
    hna (S c) (T.isPGroup'.to_le inf_le_left)
    (inf_le_right.trans c.normalizer_component.le) (inf_le_right.trans (core_normalized c))

/-- At field four the literal nonabelian source supplies a natural central
bottom layer in Q' and Φ(Q), normalized by the whole original KS. The same
marking describes either the whole center or its natural quotient by B. -/
theorem source_nonabelian_normal_central_flag
    (hfour : Nat.card F=4) (hna : ¬ IsMulCommutative (Q c)) :
    ∃ (mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) (B : Subgroup G),
      U c=O ∧ ⁅U c,K c⁆=U c ∧ U c ⊓ centralizer (K c : Set G)=⊥ ∧
      B ≤ U c ∧ B ≤ ⁅Q c,Q c⁆ ∧ B ≤ frattiniIn (Q c) ∧
      K c ⊔ S c ≤ normalizer (B : Set G) ∧
      HasSectionModel (K c) B ⊥ (linearThreeActor mark) (specialLinearNatural 3) ∧
      (B=U c ∨
        (B < U c ∧ HasSectionModel (K c) (U c) ⊥ (linearThreeActor mark)
          ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) ∧
          HasSectionModel (K c) (U c) B (linearThreeActor mark) (specialLinearNatural 3))) := by
  obtain ⟨mark,hU,hmoved,hfixed,hm | hm⟩ :=
    DoubledCenter.source_nonabelian_center_models c D hf n hn hF e hfour hna
  · have hZU : K c ⊔ S c ≤ normalizer (U c : Set G) :=
      (sup_le (map_subtype_le _) inf_le_right).trans ((core_normalized c).trans
        (normalizer_le_normalizer_characteristic_image (Q c) (center (Q c))))
    exact ⟨mark,U c,hU,hmoved,hfixed,le_rfl,hm.2.1,hm.2.2,hZU,hm.1,Or.inl rfl⟩
  · have hmo : HasSectionModel (K c) O ⊥ (linearThreeActor mark)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) := hU ▸ hm
    obtain ⟨B,_,hBU,hBD,hBP,hBn,hB,hquot⟩ :=
      source_doubled_derived_normal_flag c D hf n hn hF e mark hmo hna
    exact ⟨mark,B,hU,hmoved,hfixed,hBU.le,hBD,hBP,hBn,hB,Or.inr ⟨hBU,hm,hquot⟩⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.CentralInvariantFlags
