module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.CenterCubic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ComponentEscapeAt
public import Theory.GroupTheory.CComponent.CubicCenterRankNormal
public import Theory.Representation.HexacodeAction.ThreeRank
public import Theory.GroupTheory.GeneralizedFitting.NormalComponentCentralizer
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient

/-!
# The original triple-six component and its cubic center

The concrete triple cover has cubic rank two and center of order three.
The same local strongly quasithin bound therefore forces its original
C-component to be normal. In a reduced K T local its image is the whole
generalized Fitting subgroup. The original center theorem identifies the
point image with the entire cubic center, retaining its upstairs normality.

Source: Aschbacher--Smith 14.7.28, 14.7.32 and 14.7.47, printed
pp.1055,1057,1064, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Cubic rank forces normality for the genuine triple-six component. -/
theorem local_triple_alternatingSix_normal_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Atlas.Codes.HexEvenAutomorphisms) : C.Normal := by
  let : IsQuasisimple Atlas.Codes.HexEvenAutomorphisms := Representation.Hexacode.even_isQuasisimple
  let : IsQuasisimple (C ⧸ pCore 2 C) := IsQuasisimple.of_mulEquiv e.symm
  let := pCore_isNilpotent (p := 2) (G := I)
  let q := QuotientGroup.mk' (pCore 2 I)
  let B := C.map q
  let eB : (C ⧸ pCore 2 C) ≃* B := cComponentTwoCoreQuotientEquiv hC
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv eB
  have hb : IsComponent (HStar I) B :=
    ⟨(hC.map_quotient (pCore 2 I)).subnormal,inferInstance⟩
  let eHex := eB.symm.trans e
  have hc : Nat.card (center B) ≤ 3 := by
    rw [Nat.card_congr (centerCongr eHex).toEquiv,Representation.Hexacode.even_center_card]
  have hr : 2 ≤ primeRank 3 B := by
    rw [primeRank_congr 3 eHex]
    exact Representation.Hexacode.two_le_primeRank_even
  let : B.Normal := hb.normal_of_cubic_center_threeRank hc hr
    ((WholeResidualAssembly.GuardedSource.local_star_sqtk h I hI).stronglyQuasithin
      3 (by decide) (by decide))
  exact cComponent_normal_of_quotient_normal hC (pCore 2 I) inferInstance

/-- The reduced literal component image is F*, with the original point center. -/
theorem reduced_triple_alternatingSix_structure_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Atlas.Codes.HexEvenAutomorphisms)
    (hgen : C ⊔ (T : Subgroup G).subgroupOf I = ⊤) :
    let q := QuotientGroup.mk' (pCore 2 I)
    let B := C.map q
    B.Normal ∧ Nonempty (B ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      generalizedFitting (HStar I) = B ∧
      B ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map q = ⊤ ∧
      ((F.Li L 1).subgroupOf I).Normal ∧
      ((F.Li L 1).subgroupOf I).map q = (center B).map B.subtype := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let B := C.map q
  have hzc : Nat.card (center (C ⧸ pCore 2 C)) = 3 :=
    (Nat.card_congr (centerCongr e).toEquiv).trans Representation.Hexacode.even_center_card
  have hzne : center (C ⧸ pCore 2 C) ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hzc
    omega
  obtain ⟨_,hpn,hz,_⟩ := local_nontrivial_component_center_at
    d h hab structural previous faithful earlier I hI C hC hzne
  let hn := local_triple_alternatingSix_normal_at h I hI C hC e
  let hnB : B.Normal := hn.map q (QuotientGroup.mk'_surjective _)
  let eB : B ≃* Atlas.Codes.HexEvenAutomorphisms :=
    (cComponentTwoCoreQuotientEquiv hC).symm.trans e
  let : IsQuasisimple Atlas.Codes.HexEvenAutomorphisms := Representation.Hexacode.even_isQuasisimple
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv eB.symm
  have hg : B ⊔ ((T : Subgroup G).subgroupOf I).map q = ⊤ := by
    rw [←Subgroup.map_sup,hgen,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hquot : IsPGroup 2 (HStar I ⧸ B) :=
    isPGroup_quotient_of_sup_eq_top B _ (T.isPGroup'.comap_subtype.map q) hg
  refine ⟨hnB,⟨eB⟩,generalizedFitting_eq_of_quasisimple_two_quotient B hquot
    (pCore_quotient_pCore_eq_bot 2),?_,hpn,hz⟩
  apply top_unique
  rw [←hg]
  exact sup_le_sup_left (map_mono (subgroupOf_mono I le_sup_right)) _

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
