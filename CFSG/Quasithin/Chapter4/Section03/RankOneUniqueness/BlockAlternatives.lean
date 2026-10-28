module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesPreparation
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesActionSelection
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesFinite
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesBinaryLinear
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesSeven
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesSymplectic
public import Theory.GroupTheory.MaximalTwoLocalOvergroups

/-!
# Assembly of the concrete rank-one block alternatives

C.2.7 supplies the full catalogue of the actual star component. The constrained
rank-one and A₅ obstructions eliminate two rows without any extra premise.
The remaining row recognitions are explicit below: they must identify the
intrinsic conjugation module, not merely the group carrier. The SL₃ row must
also recover the original field degree n.

This is a conditional consumer, not a proof of C.4.1 or 4.3.7. Final assembly
must supply the remaining row implications under the unchanged original
D, h, hmany, hn, hpsl, c, hf and hb hypotheses. The specialized assemblies
supply the SL₃ action selection and the G₂(2)′, A₆ and 3.A₆ exclusions
internally. The last group-row assembly also recognizes the ordinary A₇ row.
The re-exported action-level assembly in BlockAlternativesSymplectic excludes
every nonbinary symplectic action directly; only its large-G₂ premise remains.
Source: Aschbacher--Smith C.4.1, pp.151--153, and 4.3.7, pp.615--616.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open ChapterC Chapter12.Section02 ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Conditional assembly retaining every original source input. The callback
premises are the remaining concrete C.4.1 rows and are not assumed source facts.
The original ambient arguments are retained for the eventual source application;
the row producers must use them to discharge these premises. -/
theorem source_block_alternatives_of_star_rows
    (_D : ChosenModule T L V)
    (_h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (_hn : 1 < n)
    (_hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (_hb : IsBlock c.K)
    (hlinear : ∀ F : BinaryField,
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        Matrix.SpecialLinearGroup (Fin 3) F.Carrier) → IsSL3EvenBlock c.K n)
    (hsymplectic : ∀ F : BinaryField, 1 < F.degree →
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        Matrix.symplecticGroup (Fin 2) F.Carrier) → n = 2 ∧ IsSp4FourBlock c.K)
    (hg2 : ∀ F : BinaryField, 1 < F.degree →
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        Atlas.G2.Model F.Carrier) → False)
    (hderived :
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        commutator (Atlas.G2.Model (ZMod 2))) → False)
    (halt : ∀ m : ℕ, (m = 6 ∨ m = 7 ∨ m = 8) →
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        alternatingGroup (Fin m)) → n = 2 ∧ IsAlternatingBlock c.K 7)
    (hfive :
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) → False)
    (htriple :
      (center (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
        (c.K.map c.H.subtype)) ≃* Multiplicative (ZMod 3)) →
      ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ⧸
        center (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype))) ≃*
        alternatingGroup (Fin 6)) → False) :
    IsSL3EvenBlock c.K n ∨ (n = 2 ∧ (IsAlternatingBlock c.K 7 ∨ IsSp4FourBlock c.K)) := by
  cases c.block_star_models hf with
  | linearTwo F e => exact (c.block_star_not_linearTwo hf F e).elim
  | linearThree F e => exact Or.inl (hlinear F e)
  | symplectic F hF e =>
    obtain ⟨hn2,hsp⟩ := hsymplectic F hF e
    exact Or.inr ⟨hn2,Or.inr hsp⟩
  | g2 F hF e => exact (hg2 F hF e).elim
  | g2DerivedTwo e => exact (hderived e).elim
  | alternating m hm e =>
    rcases hm with rfl | hm
    · exact (c.block_star_not_alternatingFive hf e).elim
    · obtain ⟨hn2,ha⟩ := halt m hm e
      exact Or.inr ⟨hn2,Or.inl ha⟩
  | linearFiveTwo e => exact (hfive e).elim
  | tripleSix z e => exact (htriple z e).elim

/-- The source action selector discharges the SL₃ row of the concrete
alternatives. This interface retains six row parameters; the stronger assembly
below discharges the finite soluble-normalizer rows internally. -/
theorem source_block_alternatives_of_remaining_star_rows
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    (hsymplectic : ∀ F : BinaryField, 1 < F.degree →
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        Matrix.symplecticGroup (Fin 2) F.Carrier) → n = 2 ∧ IsSp4FourBlock c.K)
    (hg2 : ∀ F : BinaryField, 1 < F.degree →
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        Atlas.G2.Model F.Carrier) → False)
    (hderived :
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        commutator (Atlas.G2.Model (ZMod 2))) → False)
    (halt : ∀ m : ℕ, (m = 6 ∨ m = 7 ∨ m = 8) →
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        alternatingGroup (Fin m)) → n = 2 ∧ IsAlternatingBlock c.K 7)
    (hfive :
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) → False)
    (htriple :
      (center (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
        (c.K.map c.H.subtype)) ≃* Multiplicative (ZMod 3)) →
      ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ⧸
        center (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype))) ≃*
        alternatingGroup (Fin 6)) → False) :
    IsSL3EvenBlock c.K n ∨ (n = 2 ∧ (IsAlternatingBlock c.K 7 ∨ IsSp4FourBlock c.K)) := by
  exact source_block_alternatives_of_star_rows D h hmany hn hpsl c hf hb
    (fun F e => c.linearThree_block_of_star_group hn hpsl hf hb F e)
    hsymplectic hg2 hderived halt hfive htriple

/-- After the natural SL₃ selector and the finite two-local exclusions, the
remaining C.4.1 obligations are the symplectic, large G₂, A₇/A₈ and SL₅(2)
rows. They remain obligations of qt-d-1222-rankone-uniqueness-block. -/
theorem source_block_alternatives_of_four_star_rows
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    (hsymplectic : ∀ F : BinaryField, 1 < F.degree →
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        Matrix.symplecticGroup (Fin 2) F.Carrier) → n = 2 ∧ IsSp4FourBlock c.K)
    (hg2 : ∀ F : BinaryField, 1 < F.degree →
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        Atlas.G2.Model F.Carrier) → False)
    (halt : ∀ m : ℕ, (m = 7 ∨ m = 8) →
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        alternatingGroup (Fin m)) → n = 2 ∧ IsAlternatingBlock c.K 7)
    (hfive :
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) → False) :
    IsSL3EvenBlock c.K n ∨ (n = 2 ∧ (IsAlternatingBlock c.K 7 ∨ IsSp4FourBlock c.K)) := by
  apply source_block_alternatives_of_remaining_star_rows D h hmany hn hpsl c hf hb
    hsymplectic hg2 (c.block_star_not_g2DerivedTwo hf) ?_ hfive
    (fun _ e => c.block_star_central_not_alternatingSix hf e)
  intro m hm e
  rcases hm with rfl | hm
  · exact (c.block_star_not_alternatingSix hf e).elim
  · exact halt m hm e


/-- The actual binary-linear exclusions leave only Sp₄, large G₂ and A₇.
All three remaining implications belong to this task's final C.4.1 assembly. -/
theorem source_block_alternatives_of_three_star_rows
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    (hsymplectic : ∀ F : BinaryField, 1 < F.degree →
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        Matrix.symplecticGroup (Fin 2) F.Carrier) → n = 2 ∧ IsSp4FourBlock c.K)
    (hg2 : ∀ F : BinaryField, 1 < F.degree →
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        Atlas.G2.Model F.Carrier) → False)
    (hseven :
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        alternatingGroup (Fin 7)) → n = 2 ∧ IsAlternatingBlock c.K 7) :
    IsSL3EvenBlock c.K n ∨ (n = 2 ∧ (IsAlternatingBlock c.K 7 ∨ IsSp4FourBlock c.K)) := by
  apply source_block_alternatives_of_four_star_rows D h hmany hn hpsl c hf hb
    hsymplectic hg2 ?_ (c.block_star_not_linearFiveTwo hn hpsl hf hb)
  intro m hm e
  rcases hm with rfl | rfl
  · exact hseven e
  · exact (c.block_star_not_alternatingEight hn hpsl hf hb e).elim

/-- The actual binary-linear exclusions leave only Sp₄ and large G₂.
Both remaining implications belong to this task's final C.4.1 assembly. -/
theorem source_block_alternatives_of_two_star_rows
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    (hsymplectic : ∀ F : BinaryField, 1 < F.degree →
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        Matrix.symplecticGroup (Fin 2) F.Carrier) → n = 2 ∧ IsSp4FourBlock c.K)
    (hg2 : ∀ F : BinaryField, 1 < F.degree →
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
        Atlas.G2.Model F.Carrier) → False) :
    IsSL3EvenBlock c.K n ∨ (n = 2 ∧ (IsAlternatingBlock c.K 7 ∨ IsSp4FourBlock c.K)) := by
  exact source_block_alternatives_of_three_star_rows D h hmany hn hpsl c hf hb
    hsymplectic hg2 (c.alternatingSeven_block_of_star_group hn hpsl hf hb)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
