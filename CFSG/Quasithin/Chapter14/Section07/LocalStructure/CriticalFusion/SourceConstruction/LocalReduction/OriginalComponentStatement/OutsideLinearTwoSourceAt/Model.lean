module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoSourceAt.Transport
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Packaged binary and alternating-five original source sections

Unpack the actual projective linear-two field model, or identify the given
alternating-five component quotient with PSL₂ over the field of four.
The original-source theorem then supplies a rank-eight literal section.
No natural-module coordinates or quotient dimension is assumed.
Source: Aschbacher–Smith 14.7.42 and 14.7.46, printed pp.1061–1063.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoSourceAt
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The packaged actual binary linear-two row has field four and an original
section of rank at least eight when the point lies outside the normal component. -/
theorem local_normal_binary_model_field_four_rank_ge_eight_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) [C.Normal] (hC : C.IsCComponent)
    (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    (n : ℕ) (hn : 1 < n) (hm : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 (2^n)) :
    n = 2 ∧ ∃ hU : IsElementaryAbelian 2 (F.UH I),
      let := hU
      ∃ _a : LocalQuotientAction I (F.UH I) (F.Vi 1),
        8 ≤ Module.finrank (ZMod 2) (Additive ((F.UH I) ⧸ (F.Vi 1).subgroupOf (F.UH I))) := by
  obtain ⟨E,hEf,hEfin,hE,⟨e⟩⟩ := hm
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hE)
  exact local_normal_field_four_rank_ge_eight_at d h hab structural previous faithful earlier
    I hI C hC hout hE hn e

/-- The actual normal outside alternating-five component supplies the original
rank-eight section required by the mixed-amalgam size comparison. -/
theorem local_normal_alternating_five_rank_ge_eight_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) [C.Normal] (hC : C.IsCComponent)
    (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    (e : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5)) :
    ∃ hU : IsElementaryAbelian 2 (F.UH I),
      let := hU
      ∃ _a : LocalQuotientAction I (F.UH I) (F.Vi 1),
        8 ≤ Module.finrank (ZMod 2) (Additive ((F.UH I) ⧸ (F.Vi 1).subgroupOf (F.UH I))) := by
  have hfield : Nat.card (GaloisField 2 2) = 2^2 := GaloisField.card 2 2 (by decide)
  obtain ⟨e₀⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (by simpa only [Nat.reducePow] using hfield)
  exact (local_normal_field_four_rank_ge_eight_at d h hab structural previous faithful earlier
    I hI C hC hout hfield (by decide) (e.trans e₀.symm)).2

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoSourceAt
