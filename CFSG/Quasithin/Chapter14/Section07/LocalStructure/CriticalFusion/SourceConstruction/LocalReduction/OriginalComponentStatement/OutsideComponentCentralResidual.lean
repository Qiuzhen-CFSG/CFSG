module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideComponentBorel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryBorelKernel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinarySeedMarkings
public import Theory.GroupTheory.PResidual.CubicFixedSupplement
public import Theory.GroupTheory.TwoPerfectCubicKernel

/-!
# The outside-component Borel equals the centralizer residual

For every actual local I and C-component C with L₁ not contained in C,
let B₀ be the original Sylow normalizer in C and B = O²(B₀). Then
O²(C_{L₁B}(L/O₂(L))) = B. The proof uses the original inverter in T∩L,
relative component normality, and the nontrivial map L₁ → I/C to establish
the two-group intersection needed for the complement argument.

Consequently B fixes the original seed V and L/O₂(L), while L₁ and the
same inverter fix B/O₂(B). These are the actual action inputs for the
outside-component automorphism and module arguments; no field marking
or module decomposition is assumed. The earlier structural, faithful
classification and 14.7.10 inputs retain their existing producers.

Source: Aschbacher–Smith, 14.7.41 and the opening of 14.7.42,
printed p.1061, refs/quasithin.pdf. The remaining outer-action analysis,
field reductions and full 14.7.47 component theorem are subsequent steps.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
  (coreAction coreAction_mk coreAction_eq_one_iff)
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original outside-component Borel residual is exactly the two-residual
of the literal L/O₂(L) action kernel on L₁B. -/
theorem local_component_borel_central_residual_eq
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) (hout : ¬ F.Li L 1 ≤ C.map I.subtype) :
    let B₀ := componentSylowNormalizer T I C
    let B := (pResidual 2 B₀).map B₀.subtype
    ∃ hJM : F.Li L 1 ⊔ B ≤ normalizer (L : Set G),
      binaryBorelCentralResidual L (F.Li L 1 ⊔ B) hJM = B := by
  let A := F.Li L 1
  let B₀ := componentSylowNormalizer T I C
  let B := (pResidual 2 B₀).map B₀.subtype
  let J := A ⊔ B
  obtain ⟨hB₀C,_,_,_,_,hnB,hBM,hBA,_⟩ :=
    local_component_borel_of_not_contains_point d h hab structural previous faithful earlier
      I hI C hC hout
  have hAL : A ≤ L := (F.Li_le L 1).trans inf_le_left
  have hJM : J ≤ normalizer (L : Set G) := sup_le (hAL.trans L.le_normalizer) hBM
  refine ⟨hJM,?_⟩
  let D := binaryBorelCentralResidual L J hJM
  have hpA : IsPPerfect 2 A := isPPerfect_embedded_pResidual 2 _
  have hpB : IsPPerfect 2 B := isPPerfect_embedded_pResidual 2 _
  have hpD : IsPPerfect 2 D := by
    let R := (pResidual 2 (binaryBorelAction L J hJM).ker).map
      (binaryBorelAction L J hJM).ker.subtype
    exact (isPPerfect_embedded_pResidual 2 (binaryBorelAction L J hJM).ker).of_surjective
      (J.subtype.subgroupMap R) (J.subtype.subgroupMap_surjective R)
  have hgen : A ⊔ D = J := point_borel_kernel_supplement h structural J hJM
    (isPPerfect_sup A B hpA hpB) le_sup_left (sup_le A.le_normalizer hBA)
  have hnD : J ≤ normalizer (D : Set G) :=
    (le_inf J.le_normalizer hJM).trans (binaryBorelCentralResidual_normalized L J hJM)
  have hC' : ((C.map I.subtype).subgroupOf I).IsCComponent := by
    simpa only [subgroupOf, comap_map_eq_self_of_injective I.subtype_injective] using hC
  have hn := local_cComponent_normal d h hab structural previous faithful earlier
    I (C.map I.subtype) hI (map_subtype_le _) hC'
  let : C.Normal := by
    simpa only [subgroupOf, comap_map_eq_self_of_injective I.subtype_injective] using hn
  have hAI : A ≤ I := F.Li_one_le_of_mem_Hz hI
  let f : A →* I ⧸ C := (QuotientGroup.mk' C).comp (inclusion hAI)
  have hf : f ≠ 1 := by
    intro hf
    apply hout
    intro a ha
    have he : f ⟨a,ha⟩ = 1 := by rw [hf]; rfl
    have hc : (⟨a,hAI ha⟩ : I) ∈ C := (QuotientGroup.eq_one_iff _).mp he
    exact ⟨⟨a,hAI ha⟩,hc,rfl⟩
  have hcA : Nat.card (A ⧸ pCore 2 A) = 3 := pointResidual_core_quotient_card h structural
  have hk := f.kernel_isTwoGroup_of_twoPerfect_cubic hpA hcA hf
  have hBC : B ≤ C.map I.subtype := (map_subtype_le _).trans hB₀C
  have hi : IsPGroup 2 (A ⊓ B : Subgroup G) := by
    apply (hk.map A.subtype).to_le
    intro a ha
    refine ⟨⟨a,ha.1⟩,?_,rfl⟩
    apply (QuotientGroup.eq_one_iff _).mpr
    obtain ⟨c,hc,he⟩ := hBC ha.2
    have he' : c = inclusion hAI (⟨a,ha.1⟩ : A) := Subtype.ext he
    exact he' ▸ hc
  obtain ⟨t,hti⟩ := exists_point_core_inverter (F := F) h structural
  have htA : (t : G) ∈ normalizer (A : Set G) :=
    ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes structural) t.property.1
  have htB : (t : G) ∈ normalizer (B : Set G) := hnB (mem_sup_right t.property.1)
  have htJ : (t : G) ∈ normalizer (J : Set G) :=
    normalizer_inf_normalizer_le_normalizer_sup A B ⟨htA,htB⟩
  apply eq_of_inverted_cubic_fixed_supplement A B D hpA hpB hpD hcA
    (le_sup_left.trans hnB) hBA hnD hgen hi (fun hh => hout (hh.trans hBC))
    (t : G) htJ htB
  · intro a ha
    let a' : A := ⟨a,ha⟩
    let t' : normalizer (A : Set G) := ⟨t,htA⟩
    have hi := hti (QuotientGroup.mk' (pCore 2 A) a')
    rw [coreAction_mk] at hi
    have hc : A.normalizerMonoidHom t' a' * a' ∈ pCore 2 A := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (pCore 2 A) (A.normalizerMonoidHom t' a' * a') = 1
      rw [map_mul,hi,inv_mul_cancel]
    exact ⟨_,hc,rfl⟩
  · intro a ha
    have hf := (coreAction_eq_one_iff _ _).mp
      (binaryBorelCentralResidual_fixed L J hJM t.property.2 htJ) (⟨a,ha⟩ : D)
    exact ⟨_,hf,rfl⟩

/-- In the outside-component branch, the Borel residual fixes the actual
seed and L/O₂(L). The actual point inverter fixes B/O₂(B), as does L₁. -/
theorem local_component_borel_fixed_actions
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) (hout : ¬ F.Li L 1 ≤ C.map I.subtype) :
    let B₀ := componentSylowNormalizer T I C
    let B := (pResidual 2 B₀).map B₀.subtype
    B ≤ centralizer (V : Set G) ∧
      ⁅L,B⁆ ≤ L.pCoreIn 2 ∧ ⁅F.Li L 1,B⁆ ≤ B.pCoreIn 2 ∧
      ∃ (t : ((T : Subgroup G) ⊓ L : Subgroup G))
        (htB : (t : G) ∈ normalizer (B : Set G)),
        (∀ x : F.Li L 1 ⧸ pCore 2 (F.Li L 1),
          coreAction (F.Li L 1)
            ⟨t,ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes structural)
              t.property.1⟩ x = x⁻¹) ∧
        coreAction B ⟨t,htB⟩ = 1 := by
  let A := F.Li L 1
  let B₀ := componentSylowNormalizer T I C
  let B := (pResidual 2 B₀).map B₀.subtype
  let J := A ⊔ B
  obtain ⟨hJM,he⟩ := local_component_borel_central_residual_eq d h hab structural previous
    faithful earlier I hI C hC hout
  change binaryBorelCentralResidual L J hJM = B at he
  obtain ⟨hB₀C,_,_,_,_,hnB,hBM,_,_⟩ :=
    local_component_borel_of_not_contains_point d h hab structural previous faithful earlier
      I hI C hC hout
  have hJH : J ≤ F.H := sup_le ((F.Li_one_le_of_mem_Hz hI).trans hI.2.1)
    ((map_subtype_le _).trans (hB₀C.trans ((map_subtype_le _).trans hI.2.1)))
  have hseed : B ≤ centralizer (V : Set G) := by
    rw [←he]
    exact binaryBorelCentralResidual_centralizes_seed h J hJM hJH
  have hc : ⁅L,B⁆ ≤ L.pCoreIn 2 := by
    apply commutator_le_of_normalizerQuotientAction_eq_one L B (pCore 2 L) hBM
    rintro ⟨x,hx⟩
    rw [←he] at hx
    obtain ⟨b,⟨c,hc,rfl⟩,rfl⟩ := hx
    exact c.property
  have hAB : A ≤ normalizer (B : Set G) := le_sup_left.trans hnB
  have hcomA : ⁅A,B⁆ ≤ B.pCoreIn 2 :=
    (le_inf ((commutator_mono ((F.Li_le L 1).trans inf_le_left) le_rfl).trans hc)
      (le_normalizer_iff_commutator_le_right.mp hAB)).trans
        (pCoreIn_inf_le_of_normalizes hBM)
  refine ⟨hseed,hc,hcomA,?_⟩
  obtain ⟨t,hti⟩ := exists_point_core_inverter (F := F) h structural
  have htB : (t : G) ∈ normalizer (B : Set G) := hnB (mem_sup_right t.property.1)
  refine ⟨t,htB,hti,?_⟩
  apply (coreAction_eq_one_iff _ _).mpr
  intro b
  have hb : (t : G) * (b : G) * (t : G)⁻¹ * (b : G)⁻¹ ∈ B.pCoreIn 2 :=
    pCoreIn_inf_le_of_normalizes hBM
      ⟨hc (commutator_mem_commutator t.property.2 b.property),
        B.mul_mem ((mem_normalizer_iff.mp htB b).mp b.property) (B.inv_mem b.property)⟩
  exact (mem_map_iff_mem B.subtype_injective).mp hb

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
