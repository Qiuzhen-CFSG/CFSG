module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.Defs
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorPointCentralizer
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorSupplementSylow

/-!
# A common marking for the strict-centralizer branch of 14.3.20

The point is the preimage of the sixth deleted coordinate in the actual
normalizer action on the source A₆ block. Its block and ambient centralizers
are kept distinct. The marking is constructed from the original hypotheses;
the four-center geometry and the later global core calculation are not fields
of this construction.

Source: Aschbacher--Smith, 14.3.20, printed pp.997--998.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Recognition BinaryPermutation.SixNaturalSplit
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G}

/-- The literal block used in 14.3.19--20. -/
abbrev factorBlock (F : InvariantFlag T V 2) (L A : Subgroup G) : Subgroup G :=
  L ⊔ (pResidual 2 (F.H ⊓ normalizer (A : Set G) : Subgroup G)).map
    (F.H ⊓ normalizer (A : Set G)).subtype

/-- Exactly the elementary factors quantified over in `FactorSelfCentralizing`. -/
structure ElementaryFactor (F : InvariantFlag T V 2) (L A : Subgroup G) : Prop where
  elementary : IsElementaryAbelian 2 A
  le_core : A ≤ (F.I₂ L).pCoreIn 2
  seed_le : V ≤ A
  card : Nat.card A = 16
  intersection_card : Nat.card (A ⊓ F.U : Subgroup G) = 8
  normalized : F.I₂ L ⊔ F.H.pCoreIn 2 ≤ normalizer (A : Set G)

/-- A single compatible marking of the block, its quaternion core and d.
This contains only the already established local data. -/
structure MarkedPoint (F : InvariantFlag T V 2) (L A : Subgroup G) where
  marking : factorBlock F L A ≃* Model
  factor_le : A ≤ factorBlock F L A
  factor_map : (A.subgroupOf (factorBlock F L A)).map marking.toMonoidHom = translations
  span_map : (F.U.subgroupOf (factorBlock F L A)).map marking.toMonoidHom = canonicalCore
  point : normalizer (factorBlock F L A : Set G)
  mem_supplement : (point : G) ∈ F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G)
  centralizes_factor : (point : G) ∈ centralizer (A : Set G)
  outside_factor : (point : G) ∉ A
  point_order : orderOf (point : G) = 2
  point_action : MulAut.congr marking ((factorBlock F L A).normalizerMonoidHom point) =
    pointAutomorphism

namespace MarkedPoint
variable {F : InvariantFlag T V 2} {L A : Subgroup G} (P : MarkedPoint F L A)

abbrev element : G := P.point
abbrev globalCentralizer : Subgroup G := centralizer ({P.element} : Set G)
abbrev blockCentralizer : Subgroup G := factorBlock F L A ⊓ P.globalCentralizer
abbrev sylowCentralizer : Subgroup G := (T : Subgroup G) ⊓ P.globalCentralizer

theorem factor_le_blockCentralizer : A ≤ P.blockCentralizer := by
  intro a ha
  exact ⟨P.factor_le ha, mem_centralizer_singleton_iff.mpr (P.centralizes_factor a ha)⟩

theorem blockCentralizer_card : Nat.card P.blockCentralizer = 960 :=
  (Nat.card_congr (pointBlockCentralizerEquiv (factorBlock F L A) P.marking
    P.point P.point_action).toEquiv).trans pointAutomorphism_fixed_card

/-- The geometric input still needed for the global Sylow argument. -/
structure FourCenterGeometry (z : G) : Prop where
  center_eq : (center P.sylowCentralizer).map P.sylowCentralizer.subtype =
    closure ({z, P.element} : Set G)
  product_fusion : IsConj P.element (z * P.element)

end MarkedPoint

variable [Finite G]

theorem markedPoint_of_strict_centralizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAR : A ≤ (F.I₂ (sourceResidual M Mc)).pCoreIn 2)
    (hVA : rankTwoSeed T M ≤ A) (hAc : Nat.card A = 16)
    (hc8 : Nat.card (A ⊓ F.U : Subgroup G) = 8)
    (hAN : F.I₂ (sourceResidual M Mc) ⊔ F.H.pCoreIn 2 ≤ normalizer (A : Set G))
    (hlt : A < centralizer (A : Set G)) :
    Nonempty (MarkedPoint F (sourceResidual M Mc) A) := by
  obtain ⟨f, hA, hU, d, hdD, hdC, hdA, hd2, hmark, _, hAC, _⟩ :=
    source_factor_point_centralizers_of_strict_centralizer
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
      A hAR hVA hAc hc8 hAN hlt
  exact ⟨⟨f, hAC.trans inf_le_left, hA, hU, d, hdD, hdC, hdA, hd2, hmark⟩⟩

/-- Apply the marked geometry to the actual global centralizer, with its
five-divisibility and local Sylow premises discharged. -/
theorem global_sylow_of_fourCenterGeometry
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAR : A ≤ (F.I₂ (sourceResidual M Mc)).pCoreIn 2)
    (hVA : rankTwoSeed T M ≤ A) (hAc : Nat.card A = 16)
    (hc8 : Nat.card (A ⊓ F.U : Subgroup G) = 8)
    (hAN : F.I₂ (sourceResidual M Mc) ⊔ F.H.pCoreIn 2 ≤ normalizer (A : Set G))
    (hlt : A < centralizer (A : Set G))
    (P : MarkedPoint F (sourceResidual M Mc) A) (z : G) (hz : F.Vi 1 = zpowers z)
    (hgeom : P.FourCenterGeometry z) :
    normalizer (P.sylowCentralizer : Set G) ≤ F.H ∧
      Chapter1.IsSylowIn 2 P.sylowCentralizer P.globalCentralizer := by
  exact source_factor_supplement_centralizer_sylow_of_four_center
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
    A hAR hVA hAc hc8 hAN hlt P.element P.mem_supplement z hz P.point_order
    hgeom.center_eq hgeom.product_fusion P.blockCentralizer inf_le_right
    (by rw [P.blockCentralizer_card]; decide)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
