module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCatalogue.Linear
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCatalogue.Symplectic
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCatalogue.Twisted
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.Catalogue

/-!
# Reduction of the full A5 catalogue to its ordinary G2 core calculation

Starting with the genuine full ReducedAlternatives predicate, the original
A5 quotients exclude every exceptional and binary clause. The linear and
symplectic rows give both original join-core equalities and containments.
The earlier five-row result is retained. The stronger result also excludes
triality, Ree, U4 and U5 using the original A5 markings and generated
quasithinness. Only the actual reduced G2 comparison remains, in both
orientations and with its field unchanged.

This is a partial catalogue reduction, not the complete F.1.12 implication.
The G2 join-core calculation and genuine source selection still require proof.

Source: DGS Theorem A and (15.2)–(15.3), pp.99–100 and 226–231;
Aschbacher–Smith F.1.12, pp.262–264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.A5PairCatalogue
open DGS85.OriginalExtension GreenBook

/-- The five regular rows still to be discharged after the original A5-pair
linear/symplectic core calculation. Every row retains its actual reduced Iso. -/
inductive RemainingReducedRows {G : Type*} [Group G] (K R S : Subgroup G) : Prop
  | g2 (F : Type) [Field F] [Finite F] [CharP F 2] (short : Bool)
      (e : Nonempty (Iso (reducedAmalgam ![K,R] S) (G2Native.amalgam F short)))
  | triality (m : ℕ) (hm : 0 < m) (point : Bool)
      (e : Nonempty (Iso (reducedAmalgam ![K,R] S) (TrialityNative.amalgam m hm point)))
  | ree (m : ℕ) (point : Bool)
      (e : Nonempty (Iso (reducedAmalgam ![K,R] S) (ReeNative.amalgam m point)))
  | unitaryFour (m : ℕ) (hm : 1 ≤ m) (point : Bool)
      (e : Nonempty (Iso (reducedAmalgam ![K,R] S) (UnitaryFourNative.amalgam m hm point)))
  | unitaryFive (q : ℕ) (hq : IsPrimePow q) (heven : Even q)
      (M : UnitaryFive.Model q) (line : Bool)
      (e : Nonempty (Iso (reducedAmalgam ![K,R] S) (UnitaryFiveNative.amalgam M line)))

/-- A genuine full reduced catalogue either gives both original core equalities
and containments, or one of the five remaining actual regular comparisons.
No perfectness, original marking, splitting or local core premise is assumed. -/
theorem core_and_containment_or_remaining
    {G : Type*} [Group G] [Finite G] {K R S : Subgroup G}
    (h : HypothesisF11 ![K,R] S)
    (a : ∀ i, Nonempty ((![K,R] i ⧸ pCore 2 (![K,R] i)) ≃* alternatingGroup (Fin 5)))
    (hnorm : ∃ j, borel (![K,R] j) S ≤ normalizer (S : Set G))
    (ha : Chapter6.Source.RankOneGeneric.Global.OriginalExtension.ReducedAlternatives K R S) :
    ((∀ i, twoCore (![K,R] i ⊔ S) = twoCore (![K,R] i)) ∧ (∀ i, S ≤ ![K,R] i)) ∨
      RemainingReducedRows K R S := by
  cases ha with
  | linear F n hn hF b e =>
    exact Or.inl (linear_core_and_containment h a hnorm F hF hn b e.some)
  | symplectic F n hn hF b e =>
    exact Or.inl (Symplectic.core_and_containment F h a hnorm hF hn b e.some)
  | g2 F b e => exact Or.inr (.g2 F b e)
  | triality n hn b e => exact Or.inr (.triality n hn b e)
  | ree n b e => exact Or.inr (.ree n b e)
  | unitaryFour n hn b e => exact Or.inr (.unitaryFour n hn b e)
  | unitaryFive q hq heven M b e => exact Or.inr (.unitaryFive q hq heven M b e)
  | exceptional c e => exact (not_reduced_exceptional a c e).elim
  | binaryLocal i e => exact (not_binary_overgroup_quotient i (a i).some le_rfl e).elim
  | binaryJoin i e => exact (not_binary_overgroup_quotient i (a i).some le_sup_left e).elim
  | binaryParabolic i e =>
    exact (not_binary_overgroup_quotient i (a i).some (le_sup_left.trans le_sup_left) e).elim

/-- The full reduced catalogue leaves only the genuine G2 comparison after
all four twisted rows have been excluded. Quasithinness is required only of
the original generated subgroup; no perfectness or original marking is added. -/
theorem core_and_containment_or_g2
    {G : Type*} [Group G] [Finite G] {K R S : Subgroup G}
    (h : HypothesisF11 ![K,R] S)
    (hqt : IsQuasithin (generated ![K,R] S))
    (a : ∀ i, Nonempty ((![K,R] i ⧸ pCore 2 (![K,R] i)) ≃* alternatingGroup (Fin 5)))
    (hnorm : ∃ j, borel (![K,R] j) S ≤ normalizer (S : Set G))
    (ha : Chapter6.Source.RankOneGeneric.Global.OriginalExtension.ReducedAlternatives K R S) :
    ((∀ i, twoCore (![K,R] i ⊔ S) = twoCore (![K,R] i)) ∧ (∀ i, S ≤ ![K,R] i)) ∨
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (short : Bool),
        Nonempty (Iso (reducedAmalgam ![K,R] S) (G2Native.amalgam F short)) := by
  rcases core_and_containment_or_remaining h a hnorm ha with hc | hr
  · exact Or.inl hc
  · cases hr with
    | g2 F b e => exact Or.inr ⟨F,inferInstance,inferInstance,inferInstance,b,e⟩
    | triality m hm b e => exact (not_triality h a m hm b e.some).elim
    | ree m b e => exact (not_ree h a m b e.some).elim
    | unitaryFour m hm b e => exact (not_unitaryFour h a m hm b e.some).elim
    | unitaryFive q hq heven M b e =>
      exact (not_unitaryFive h hqt a hq heven M b e.some).elim

end CFSG.Quasithin.ChapterF.Source.A5PairCatalogue
