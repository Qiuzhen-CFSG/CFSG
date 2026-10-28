module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.NonEnlargement
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Alternating.NaturalRecognition
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.Component

/-!
# Source 14.7.48–52 from the preceding component statement

The local family proves component uniqueness, trivial quotient centralizer,
Sylow supplementation, full module movement and identification with O²(I).
The row exclusions then force every original local to equal G₁. Transport
through the literal subtype and two-core maps identifies the embedded
whole residual and supplies its relative C-component property.

The final theorem applies the existing source-data constructor. Natural
A₅ recognition is discharged, while the independent G₂ exclusion remains explicit at the
original flag; no Data record, final residual alternative, or uniqueness
conclusion is part of the earlier input. Their final discharge remains
with qt-d-14752-local-reduction and qt-d-14763-source-data, and the genuine
earlier structural inputs remain with the source assembly owners.

Source: Aschbacher–Smith, 14.7.48 and 14.7.52, printed pp.1064–1065,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The local component is the original embedded whole residual once the
remaining rows have been excluded. In particular its overcomponent in G₁
cannot contain it strictly. -/
theorem local_component_eq_full_residual_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L) (exclusions : RowExclusions F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) : C.map I.subtype = K F := by
  have hi := local_eq_full_point_of_row_exclusions_at d h hab structural previous faithful
    earlier source47 exclusions I hI
  have hc := (local_component_eq_residual_at d h hab structural previous faithful earlier
    source47 I hI C hC).1
  rw [←hc]
  subst I
  rfl

/-- The actual overcomponent in G₁ and the literal inclusion of every
original component; equality is the two surviving cases of A.3.12. -/
theorem local_overcomponent_eq_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L) (exclusions : RowExclusions F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) :
    ∃ D : Subgroup F.H, D.IsCComponent ∧ C.map (inclusion (show I ≤ F.H from hI.2.1)) = D := by
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)
  obtain ⟨D,hD,_,_⟩ := GuardedSource.local_exists_quasisimple_component d h hab structural previous
    faithful earlier F.H hH
  refine ⟨D,hD,?_⟩
  apply map_injective F.H.subtype_injective
  rw [Subgroup.map_map]
  have hj : F.H.subtype.comp (inclusion (show I ≤ F.H from hI.2.1)) = I.subtype := rfl
  rw [hj,local_component_eq_full_residual_at d h hab structural previous faithful earlier
    source47 exclusions I hI C hC,
    local_component_eq_full_residual_at d h hab structural previous faithful earlier
    source47 exclusions F.H hH D hD]

/-- Source 14.7.52, retaining all original locals and the literal whole-residual quotient. -/
theorem source_14_7_52_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L) (exclusions : RowExclusions F L) :
    F.Hz L (normalizer (L : Set G)) = {F.H} ∧
      ((K F).subgroupOf F.H).IsCComponent ∧
      K F ⊔ (T : Subgroup G) = F.H ∧
      (AlternatingResidual F ∨ G2Residual F) ∧
      ∀ I ∈ F.Hz L (normalizer (L : Set G)), I = F.H ∧ F.UH I = F.U := by
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)
  obtain ⟨C,hC,_,_,_,hc,hgen,_⟩ := source_14_7_48_at d h hab structural previous faithful
    earlier source47 F.H hH
  have he : C.map F.H.subtype = K F := by rw [←hc]; rfl
  let e : C ≃* K F := (equivMapOfInjective C F.H.subtype F.H.subtype_injective).trans
    (MulEquiv.subgroupCongr he)
  let eq := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  have hrows : AlternatingResidual F ∨ G2Residual F := by
    rcases local_component_residual_rows source47 exclusions F.H hH C hC with ha | ha
    all_goals obtain ⟨a⟩ := ha
    · exact Or.inl ⟨eq.symm.trans a⟩
    · exact Or.inr ⟨eq.symm.trans a⟩
  have hi : ∀ I ∈ F.Hz L (normalizer (L : Set G)), I = F.H :=
    fun I hI => local_eq_full_point_of_row_exclusions_at d h hab structural previous faithful
      earlier source47 exclusions I hI
  refine ⟨?_,?_,he ▸ hgen,hrows,?_⟩
  · ext I
    simp only [Set.mem_singleton_iff]
    exact ⟨hi I,fun he => he.symm ▸ hH⟩
  · rw [residual_subgroupOf,hc]
    exact hC
  · intro I hI
    exact ⟨hi I hI,by rw [hi I hI]; rfl⟩

/-- The substantive component-to-residual family feeds the existing source-data
construction. The guarded natural A₅ recognition is proved; only the
independent G₂ exclusion remains at its original-flag hypothesis. -/
theorem exists_data_of_component_statement_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L) (exclusions : RowExclusions F L)
    (h53 : ¬ G2Residual F) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W),
      Nonempty (Data T L V F W) := by
  obtain ⟨_,_,_,hr,_⟩ := source_14_7_52_at d h hab structural previous faithful earlier
    source47 exclusions
  exact exists_data_of_residual_alternatives_at d h hab structural hr h53

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly
