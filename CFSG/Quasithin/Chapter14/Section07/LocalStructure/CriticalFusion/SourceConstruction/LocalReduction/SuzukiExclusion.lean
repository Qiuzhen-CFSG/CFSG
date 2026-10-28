module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SuzukiBorel

/-!
# Excluding Suzuki components from every original local

Pass to the actual component-orbit overgroup in the same H_z. The full
Borel argument centralizes its point image, so generation gives point
normality. Source 14.7.7 then kills the three-prime core. But the nontrivial
Suzuki orbit is normal and has order prime to three, a contradiction.
Transport back through the intrinsic two-core quotient proves 14.7.33
without a component-normality assumption or a natural-module callback.

Source: Aschbacher–Smith, 14.7.33 and the preceding argument in 14.7.32,
printed p.1056, using 14.7.7, printed p.1045, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open Chapter13.Section08.Components
open BenderSuzuki.MatrixGroups
open Chapter15.Section03
open Chapter15.Section03.Candidates.SuzukiExclusion
open Suzuki.BorelSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- In the literal reduced local, the Suzuki Borel forces point normality.
Source 14.7.7 then excludes the nontrivial three-free normal component orbit. -/
theorem local_reduced_suzuki_impossible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) = I)
    {m : ℕ} (hm : 0 < m) (eK : (K ⧸ pCore 2 K) ≃* SuzukiMatrixGroup m) : False := by
  let N := conjugateSpanBy K (T : Subgroup G)
  let X := Chapter13.Section08.Source.starImage I N
  let Y := Chapter13.Section08.Source.starImage I (F.Li L 1)
  let S := Chapter13.Section08.Source.starImage I (T : Subgroup G)
  have hLI := F.Li_one_le_of_mem_Hz hI
  have hTI := F.sylow_le_of_mem_Hz hI
  have hbase := sup_le hLI hTI
  have hNI : N ≤ I := conjugateSpanBy_le hKI (hTI.trans I.le_normalizer)
  have hcomm : Y ≤ centralizer (X : Set (HStar I)) :=
    local_suzuki_point_centralizes_orbit d h hab structural previous faithful earlier I K hI hKI hK hm eK
  obtain ⟨b⟩ := local_suzuki_invariantBorel h hab structural previous faithful I K hI hKI hK hm eK
  have hgen' : X ⊔ (Y ⊔ S) = ⊤ := by
    rw [←Swapped.LinearTwo.starImage_sup I (F.Li L 1) (T : Subgroup G) hLI hTI,
      ←Swapped.LinearTwo.starImage_sup I N _ hNI hbase,hgen]
    simp only [Chapter13.Section08.Source.starImage,subgroupOf_self,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hnY : Y.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [←hgen']
    exact sup_le ((le_centralizer_iff.mp hcomm).trans (Subgroup.centralizer_le_normalizer _))
      (sup_le Y.le_normalizer (starImage_normalizes I (F.Li L 1) (T : Subgroup G)
        (ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes structural))))
  have hcore := local_threePrimeCore_eq_bot_of_point_normal h hab structural previous faithful I hI hnY
  have hnN : (N.subgroupOf I).Normal :=
    (normal_subgroupOf_iff_le_normalizer hNI).mpr (by
      rw [←hgen]
      exact sup_le N.le_normalizer b.orbit_normalized)
  let : X.Normal := hnN.map _ (QuotientGroup.mk'_surjective _)
  have hX3 : Nat.Coprime 3 (Nat.card X) := by
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    rw [Nat.card_congr b.equiv.toEquiv,Nat.card_fun]
    exact fun hd => suzukiMatrixGroup_three_free m hm (Nat.prime_three.dvd_of_dvd_pow hd)
  have hXle : X ≤ pPrimeCore 3 (HStar I) := le_sSup ⟨inferInstance,hX3⟩
  rw [hcore] at hXle
  have hB := local_component_star_isComponent h hab structural previous faithful I hI (K.subgroupOf I) hK
  exact hB.isCComponent.ne_bot (bot_unique ((map_mono (subgroupOf_mono I
    (le_conjugateSpanBy K (T : Subgroup G)))).trans hXle))

/-- Source 14.7.33: no C-component of any original local has a Suzuki
intrinsic two-core quotient. No component-normality premise is required. -/
theorem local_component_not_suzuki
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (K : Subgroup I) (hK : K.IsCComponent)
    (m : ℕ) (hm : 1 ≤ m) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* SuzukiMatrixGroup m) := by
  rintro ⟨eK⟩
  let N := conjugateSpanBy (K.map I.subtype) (T : Subgroup G)
  let J := N ⊔ (F.Li L 1 ⊔ (T : Subgroup G))
  obtain ⟨_,hJI,hJ⟩ := local_component_reduced_mem_Hz h structural I hI K hK
  have hKJle : K.map I.subtype ≤ J := (le_conjugateSpanBy _ _).trans le_sup_left
  have hKI : ((K.map I.subtype).subgroupOf I).IsCComponent := by
    simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hK
  have hKJ := hKI.subgroupOf_of_le hKJle hJI
  let e : K ≃* K.map I.subtype := equivMapOfInjective K I.subtype I.subtype_injective
  let eq : (K ⧸ pCore 2 K) ≃* (K.map I.subtype ⧸ pCore 2 (K.map I.subtype)) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  exact local_reduced_suzuki_impossible d h hab structural previous faithful earlier
    J (K.map I.subtype) hJ hKJle hKJ rfl (by omega) (eq.symm.trans eK)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
