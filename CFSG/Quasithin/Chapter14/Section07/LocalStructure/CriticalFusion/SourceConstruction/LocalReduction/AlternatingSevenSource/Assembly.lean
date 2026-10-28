module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Dimension
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.FourExclusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.NaturalExclusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Assembly

/-!
# Original 14.7.50 and its source-data consumer

Every original local admits a faithful irreducible quotient of its actual
U_I/V₁ section. The marked small-module catalogue, the two-cubic exclusion
of four plus its dual, the four-space partial-inverter contradiction, and
the natural-module flag-word contradictions exclude an A₇ component.
All markings and proper quotients are constructed from the original inputs.

The final consumers discharge precisely the A₇ conjunct of RowExclusions
and feed the existing 14.7.52/Data constructor. The independently owned
linear and A₆ exclusions and the earlier component statement remain explicit.

Source: Aschbacher–Smith 14.7.50, printed pp.1064–1065,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Original 14.7.50 at each actual local and each actual C-component. -/
theorem source_14_7_50_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) :
    ¬ Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 7)) := by
  rintro ⟨e⟩
  obtain ⟨hU,hr⟩ := local_exists_faithful_irreducible_quotient_at
    d h hab structural previous faithful earlier source47 I hI C hC
  let := hU
  obtain ⟨a,_ha,N,hN,hirr,_hf,hq⟩ := hr
  obtain ⟨j,hj,_hmark,hm,hcases⟩ := local_permutation_marking_at
    d h hab structural previous faithful earlier source47 I hI C hC e
  have hCj : (C.map (QuotientGroup.mk' (pCore 2 I))).map j =
      alternatingGroup (Fin 7) := by
    rw [Subgroup.map_map]
    exact hm
  rcases local_quotient_dimension_dichotomy_at d h hab structural previous faithful
    earlier source47 I hI C hC a N hN.ne_top hirr hq j hj hCj hcases with hd | hn
  · exact local_four_quotient_impossible_at d h hab structural previous faithful
      earlier source47 I hI C hC e a N hN.ne_top hd
  · exact local_natural_quotient_impossible_at d h hab structural previous faithful
      earlier source47 I hI C hC e a N hN.ne_top j hj hcases hn

/-- The genuine original A₇ theorem completes the final RowExclusions
conjunct; only the other independent rows remain inputs. -/
theorem row_exclusions_of_other_rows_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (otherRows : ∀ I : Subgroup G, I ∈ F.Hz L (normalizer (L : Set G)) →
      ∀ C : Subgroup I, C.IsCComponent →
        (∀ n : ℕ, 3 ≤ n → n ≤ 5 → ¬ Nonempty ((C ⧸ pCore 2 C) ≃* SL(n,ZMod 2))) ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 6))) :
    RowExclusions F L := by
  intro I hI C hC
  obtain ⟨hl,h6⟩ := otherRows I hI C hC
  exact ⟨hl,h6,source_14_7_50_at d h hab structural previous faithful earlier
    source47 I hI C hC⟩

/-- The completed A₇ row is consumed by the original source-data
constructor, retaining the independent linear, A₆, and G₂ rows. -/
theorem exists_data_of_other_rows_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (otherRows : ∀ I : Subgroup G, I ∈ F.Hz L (normalizer (L : Set G)) →
      ∀ C : Subgroup I, C.IsCComponent →
        (∀ n : ℕ, 3 ≤ n → n ≤ 5 → ¬ Nonempty ((C ⧸ pCore 2 C) ≃* SL(n,ZMod 2))) ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 6)))
    (h53 : ¬ G2Residual F) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W),
      Nonempty (Data T L V F W) := by
  exact exists_data_of_component_statement_at d h hab structural previous faithful earlier
    source47 (row_exclusions_of_other_rows_at d h hab structural previous faithful
      earlier source47 otherRows) h53

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
