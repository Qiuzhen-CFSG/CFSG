module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NonnormalBinarySourceAt.FullAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.Section
public import Theory.Representation.BinaryConjugationSection.Coinvariants

/-!
# Full movement in the exchanged field-four branch

The original point residual lies in the actual component orbit: its
cubic quotient is contained in the full three-prime residual, and its
two-perfectness removes the two-core ambiguity. The seed commutator
therefore makes the whole orbit move U. Transport through any literal
binary conjugation section gives full coinvariant generation on U/V₁.
The final application constructs this action on that same quotient.

Source: Aschbacher–Smith, proof of 14.7.32, printed pp.1056–1057,
refs/quasithin.pdf. Orthogonal recognition and the ensuing weak-closure
contradiction are subsequent steps, not assumptions of these results.
-/

/-! This same-G,T source replay uses only Structural1222At and Theorem12213At
at the original Sylow; it does not infer universal earlier records. -/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.Components Swapped Swapped.LinearTwo
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

theorem local_nonnormal_component_point_le_orbit_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal) :
    F.Li L 1 ≤ conjugateSpanBy K (T : Subgroup G) := by
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape_at F previous)
  exact marked_le_orbit F.H _ (F.Li L 1) (F.Li_one_le_of_mem_Hz hH)
    (isPPerfect_embedded_pResidual 2 _)
    (IsPGroup.of_card (n := 1)
      (by simpa using pointResidual_core_quotient_card_at (F := F) h structural))
    (local_nonnormal_component_full_component_at d h hab structural previous faithful earlier
      I K hI hKI hK hnormal).2

theorem local_nonnormal_component_commutator_U_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal) :
    ⁅F.U, conjugateSpanBy K (T : Subgroup G)⁆ = F.U := by
  have hgen := (local_nonnormal_component_eq_full_point_at d h hab structural previous faithful earlier
    I K hI hKI hK hnormal).1
  have hnormalH : F.H ≤ normalizer (conjugateSpanBy K (T : Subgroup G) : Set G) := by
    rw [hgen]
    exact sup_le (conjugateSpanBy K (T : Subgroup G)).le_normalizer
      (le_normalizer_conjugateSpanBy K (T : Subgroup G))
  exact (conjugateSpanBy_eq_commutator_of_seed V F.H _ (F.Li L 1)
    (hgen ▸ le_sup_left) hnormalH
    (local_nonnormal_component_point_le_orbit_at d h hab structural previous faithful earlier
      I K hI hKI hK hnormal) (seed_commutator h F)).symm

theorem local_nonnormal_component_section_moved_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    Coinvariants.ker (ρ.comp ((conjugateSpanBy K (T : Subgroup G)).subgroupOf F.H).subtype) = ⊤ := by
  have hgen := (local_nonnormal_component_eq_full_point_at d h hab structural previous faithful earlier
    I K hI hKI hK hnormal).1
  have hNH : conjugateSpanBy K (T : Subgroup G) ≤ F.H := hgen ▸ le_sup_left
  let r := (subgroupOfEquivOfLe hNH).symm.toMonoidHom
  apply c.coinvariants_eq_top_of_group_generation _ hNH _ r (fun _ _ => rfl)
  rw [commutator_comm, local_nonnormal_component_commutator_U_at d h hab structural previous faithful
    earlier I K hI hKI hK hnormal, sup_eq_left.mpr c.kernel_le]

theorem local_nonnormal_component_exists_moved_section_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal) :
    ∃ hU : IsElementaryAbelian 2 F.U,
      letI := hU
      ∃ ρ : Representation (ZMod 2) F.H (Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U)),
        Nonempty (BinaryConjugationSection F.H F.U (F.Vi 1) ρ) ∧
        Coinvariants.ker
          (ρ.comp ((conjugateSpanBy K (T : Subgroup G)).subgroupOf F.H).subtype) = ⊤ := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  refine ⟨elementary_U F,?_⟩
  obtain ⟨ρ,⟨c⟩⟩ := exists_section F
  exact ⟨ρ,⟨c⟩,local_nonnormal_component_section_moved_at d h hab structural previous faithful earlier
    I K hI hKI hK hnormal c⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
