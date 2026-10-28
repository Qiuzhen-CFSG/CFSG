module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NonnormalBinarySourceAt.Borel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedProjectiveAt.Borel
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.CubicSupplement

/-!
# Field four and the actual point inverter in the exchanged binary branch

The original Sylow Borel has odd quotient E = C × C and a diagonal cubic
P from L₁. Its actual quotient-action centralizer residual has fixed image
D under the constructed point inverter t_L in T∩L, with E = P D. The
paired-torus displacement argument forces t_L to exchange factors and
|C| ≤ 3. Since |C| = 2ⁿ−1 and n ≥ 2, n = 2. The original component
coordinates also prove that this same t_L exchanges the two components.

Applying the result to the complete nonnormal-component catalogue leaves
only PSL₂(4). The full-point overcomponent comparison, full quotient
centralizer, orthogonal-module and weak-closure arguments remain separate
source steps; this does not complete 14.7.32 or identify the full residual.

Source: Aschbacher–Smith, proof of 14.7.32, printed p.1056,
refs/quasithin.pdf. All quotient maps, kernels and component coordinates
are those of the original local, without additional recognition premises.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.Components Swapped Swapped.LinearTwo
open Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
  (coreAction coreAction_eq_one_iff)
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
/-- The remaining moved binary component has field four. Moreover an actual
point-cubic inverter in T∩L exchanges the original two components. -/
theorem local_binary_field_four_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (Chapter13.Section08.Source.starImage I K) 2 (2 ^ n))
    (hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K) :
    n = 2 ∧ ∃ s : ((T : Subgroup G) ⊓ L : Subgroup G),
      s.val ∉ normalizer (K : Set G) ∧
      ∀ x : F.Li L 1 ⧸ pCore 2 (F.Li L 1),
        coreAction (F.Li L 1)
          ⟨s,ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes_at structural) s.property.1⟩ x = x⁻¹ := by
  obtain ⟨t,ht,htn,hNI,e,S,horbit,hcoord,hres,hS,him,hsol,hLB,hBM,hnB,hBN,hLres,
    heven,hrank,hP,hfst,hsnd⟩ :=
    local_binary_borel_at d h hab structural previous faithful earlier I K hI hKI hK hn hm hmoving
  let N := K ⊔ K.conjBy t
  let B₀ := SourceTorus.chosenLift I N hNI S
  let C := SourceActions.CommonTorus I N e S
  let f := SourceTorus.toCommonTori I N hNI e S hn hm
  let P := SourceActions.Markings.image B₀ (F.Li L 1) f
  let : IsCyclic C := BinaryBorel.torus_cyclic hn hm _
  let : CommGroup C := IsCyclic.commGroup
  have hTI := F.sylow_le_of_mem_Hz hI
  have hi : (normalizer (K.subgroupOf I : Set I)).index = 2 := by
    rcases Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
      (local_star_sqtk h I hI) hK with hh | hh
    · exact (hmoving (conjugateSpan_eq_of_normal I K T hKI hTI hh)).elim
    · exact hh.1
  have hTB : (T : Subgroup G) ≤ normalizer (B₀ : Set G) := le_sup_right.trans hnB
  obtain ⟨s,hs⟩ := AlternatingSevenSource.exists_point_core_inverter_at (F := F) h structural
  let α := SourceTorus.normalizerAction I N hNI e S hn hm ⟨s,hTB s.property.1⟩
  have hk : IsPGroup 2 f.ker := by
    rw [SourceTorus.toCommonTori_ker]
    exact pCore_isPGroup
  have ho := SourceActions.commonTori_odd I N e S hn hm
  have heq := SourceTorus.normalizerAction_toCommonTori I N hNI e S hn hm
    ⟨s,hTB s.property.1⟩
  obtain ⟨hgen,hfix⟩ := OriginalComponentStatement.ContainedProjectiveAt.point_borel_torus_supplement_at h structural B₀ hBM hLres hBN f
    (SourceTorus.toCommonTori_surjective I N hNI e S hn hm) hk ho
    s s.property.2 (hTB s.property.1) α heq
  have hinv : ∀ x ∈ P, α x = x⁻¹ := SourceActions.Markings.image_inverted
    B₀ (F.Li L 1) hLB f hk ho ⟨s,hTB s.property.1⟩
      (ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes_at structural) s.property.1)
      α heq hs
  have hperm := (SourceActions.source_factor_actions I K T hTI ht hNI hi htn
    e hcoord S hn hm hTB).2 ⟨s,s.property.1⟩
  obtain ⟨hex,hcard⟩ := CartanAction.exchanges_and_card_le_of_fixed_supplement
    α P _ hP hfst hsnd hgen hfix hinv hperm
  have hc : Nat.card C = 2 ^ n - 1 := BinaryBorel.torus_card hn hm _
  change Nat.card C ≤ 3 at hcard
  rw [hc] at hcard
  have hn2 : n = 2 := by
    by_contra hh
    have hp := Nat.pow_le_pow_right (n := 2) (by decide) (show 3 ≤ n by omega)
    norm_num at hp
    omega
  refine ⟨hn2,s,?_,hs⟩
  intro hsn
  have hsI : (s : G) ∈ I := hTI s.property.1
  have hsN := SourceActions.normalizes_orbit I K hKI hi (hTI ht) htn hsI
  have hpairs : K.conjBy (s : G) = K ∧ (K.conjBy t).conjBy (s : G) = K.conjBy t := by
    rcases SourceActions.component_permutation I K hKI hi (hTI ht) hsI htn with hfix | hswap
    · exact hfix
    · have heK : K.conjBy (s : G) = K := (mem_normalizer_iff_map_conj_eq).mp hsn
      have heT : K.conjBy t = K := hswap.1.symm.trans heK
      exact (htn ((mem_normalizer_iff_map_conj_eq).mpr heT)).elim
  obtain ⟨h₁,h₂⟩ := (SourceActions.productAction_axes I K (hTI ht) e hcoord hNI hsI hsN).1 hpairs
  have hpres := SourceActions.normalizerAction_preserves I N hNI e S hn hm
    hsI hsN (hTB s.property.1)
    (BinaryBorel.restrictAut_map _ _ _ _ _ h₁) (BinaryBorel.restrictAut_map _ _ _ _ _ h₂)
  have haxes : CartanAction.firstFactor C = CartanAction.secondFactor C :=
    hpres.1.symm.trans hex.1
  have hone : Nat.card C = 1 := Nat.card_eq_one_iff_exists.mpr ⟨1,fun c =>
    (CartanAction.mem_secondFactor (c,1)).mp (haxes ▸
      (by simp : (c,1) ∈ CartanAction.firstFactor C))⟩
  norm_num [hn2] at hc
  omega

/-- The original nonnormal-component catalogue now has just the literal
PSL₂(4) model; even larger fields are excluded by the same actual Borel. -/
theorem local_nonnormal_component_field_four_at
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
    ClassicalGroup.IsPSL (Chapter13.Section08.Source.starImage I K) 2 4 := by
  obtain ⟨n,hn,_,hm⟩ := local_nonnormal_component_even_binary_at d h hab structural previous
    faithful earlier I K hI hKI hK hnormal
  have hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K := by
    intro he
    exact hnormal (normal_of_sylow_span_eq I K T hKI (F.sylow_le_of_mem_Hz hI)
      ((Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
        (local_star_sqtk h I hI) hK).imp_right And.left) he)
  have hn2 := (local_binary_field_four_at d h hab structural previous faithful earlier
    I K hI hKI hK hn hm hmoving).1
  simpa [hn2] using hm

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
