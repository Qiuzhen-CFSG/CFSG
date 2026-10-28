module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryBorel
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityPointBinary

/-!
# Comparing the exchanged binary component with the full point normalizer

For field degree greater than two, the actual moved component belongs to
Chapter 1's local family. The source maximality theorem and unique containing
component in 1.2.4 make it a component of the original full point normalizer.
The original three-residual calculation then identifies the same Sylow orbit
with O^{3′}(F.H). All intrinsic two-core quotients are transported through
their actual subgroup equivalences.

The only excluded parameter in the Chapter 1 theorem is PSL₂(4). The
already proved factor-torus order distinguishes it from the larger fields.
Applied to every original nonnormal component, the even binary catalogue
therefore leaves the literal PSL₂(4) exception or the proved full-point
component and residual identities. No comparison premise is assumed.

Source: Aschbacher–Smith, proof of 14.7.32, printed p.1056, using
1.2.4 and 1.2.8, refs/quasithin.pdf. The field-four overcomponent case and
the later B = L₁ B_C argument remain separate source steps.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.Components Swapped Swapped.LinearTwo
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem binary_large_not_four {X : Type*} [Group X] [Finite X]
    {n : ℕ} (hn : 2 < n) (hm : ClassicalGroup.IsPSL X 2 (2 ^ n)) :
    ¬ ClassicalGroup.IsPSL X 2 4 := by
  intro hfour
  let S : Sylow 2 X := Classical.choice inferInstance
  have hc := BinaryBorel.torus_card (by omega : 2 ≤ n) hm S
  have hc4 := BinaryBorel.torus_four_card hfour S
  have hp := Nat.pow_le_pow_right (n := 2) (by decide) (show 3 ≤ n by omega)
  norm_num at hp
  omega

/-- Away from the field-four exception in 1.2.8, the actual moved component
is a component of the original full point normalizer. Its full orbit is
therefore the three-residual there as well. -/
theorem local_binary_large_full_component
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    {n : ℕ} (hn : 2 < n)
    (hm : ClassicalGroup.IsPSL (Chapter13.Section08.Source.starImage I K) 2 (2 ^ n))
    (hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K) :
    (K.subgroupOf F.H).IsCComponent ∧
      (primeToResidual 3 F.H).map F.H.subtype = conjugateSpanBy K (T : Subgroup G) := by
  have hTI := F.sylow_le_of_mem_Hz hI
  have hSyl : Chapter1.IsSylowIn 2 (T : Subgroup G) I :=
    ⟨T.subtype hTI, by rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTI]⟩
  have hKL := Chapter1.mem_L_of_cComponent hI.1.1 hSyl hKI hK
  have hKF := hKI.trans hI.2.1
  let eI := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKI)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKI))
  have hmK := hm.of_mulEquiv (eI.symm.trans (cComponentTwoCoreQuotientEquiv hK))
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)
  have hTH : (T : Subgroup G) ≤ F.H := F.sylow_le_of_mem_Hz hH
  have hSylH : Chapter1.IsSylowIn 2 (T : Subgroup G) F.H :=
    ⟨T.subtype hTH, by rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]⟩
  have hmove : ¬ (T : Subgroup G) ≤ normalizer (K : Set G) := by
    intro hn
    exact hmoving (le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy _ _))
  have hfull := Chapter1.Section02.MovedMaximalityPoint.binary_component_in_overgroup
    d.qtke hKL hKF hH.1.1 hSylH hmove hn hmK (binary_large_not_four hn hmK)
  let eF := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKF)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKF))
  have hmF := hmK.of_mulEquiv ((cComponentTwoCoreQuotientEquiv hfull).symm.trans eF)
  exact ⟨hfull,local_binary_threeResidual h hab structural previous faithful F.H K hH hKF hfull
    (by omega) hmF hmoving⟩

/-- The remaining overcomponent comparison is confined to the literal
PSL₂(4) exception. Every larger nonnormal component is already a component
of the full point normalizer, with its original three-residual orbit. -/
theorem local_nonnormal_component_full_or_four
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal) :
    ClassicalGroup.IsPSL (Chapter13.Section08.Source.starImage I K) 2 4 ∨
      (K.subgroupOf F.H).IsCComponent ∧
        (primeToResidual 3 F.H).map F.H.subtype = conjugateSpanBy K (T : Subgroup G) := by
  obtain ⟨n,hn,_,hm⟩ := local_nonnormal_component_even_binary
    d h hab structural previous faithful earlier I K hI hKI hK hnormal
  by_cases he : n = 2
  · exact Or.inl (by simpa [he] using hm)
  · right
    have hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K := by
      intro he
      exact hnormal (normal_of_sylow_span_eq I K T hKI (F.sylow_le_of_mem_Hz hI)
        ((Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
          (local_star_sqtk h I hI) hK).imp_right And.left) he)
    exact local_binary_large_full_component d h hab structural previous faithful
      I K hI hKI hK (by omega) hm hmoving

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
