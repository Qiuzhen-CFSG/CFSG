module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.LocalStructure.KernelControl
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication.Intrinsic
public import Theory.SpecificGroups.Classical.BinaryDerivedCubicRank

/-!
# Intrinsic kernel control for the marked symplectic component

The literal epimorphism K → K⁺ ≃ Sp₄(F) forces three-rank at least two:
otherwise a cyclic Sylow three-subgroup would have a cyclic image, contrary
to the embedded binary symplectic cubic witness. Ambient SQTK supplies the
opposite bound. A.3.6 then gives quasisimplicity of K/O₂(K), and the source
reduced-family hypothesis gives central kernels for every intrinsic-to-plus
core comparison in K. This applies to both fixed parabolic preimages.

No intrinsic quotient is identified with a plus quotient. The universal
A.3.6 input and earlier ambient hypotheses retain their source owners.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.6 and
the paragraph preceding 13.6.14 and Lemma 13.6.19, printed pp.929–931.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction
open ComponentSelection Theory.SpecificGroups.SymplecticFour
open Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The actual plus marking forces three-rank at least two in K itself. -/
theorem two_le_three_rank
    (e : plusImage K L T z v hL hz K ≃* Sp F) : 2 ≤ primeRank 3 K := by
  by_contra hr
  have hr1 : primeRank 3 K ≤ 1 := by omega
  let P : Sylow 3 K := Classical.choice inferInstance
  have hu := P.primeRank_le_one_of_surjective
    (P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr1)
    (modelMap K L T z v hL hz e) (modelMap_surjective K L T z v hL hz e)
  have hl : 2 ≤ primeRank 3 (Sp F) :=
    Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic.trans
      (Theory.GroupTheory.primeRank_le_of_injective 3 (commutator (Sp F)).subtype Subtype.val_injective)
  omega

variable {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D], IsSQTK κ D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → A36Conclusion B)

include hG hA36 in
/-- A.3.6 applies to the actual C-component in KTᵥ and yields its intrinsic
quasisimple core quotient. No covering or kernel premise is imposed. -/
theorem source_intrinsic_quasisimple
    (hv : orderOf v = 2) (hK : K ∈ Yz L T z v)
    (e : plusImage K L T z v hL hz K ≃* Sp F) :
    IsQuasisimple (K ⧸ pCore 2 K) := by
  have hl := two_le_three_rank K L T z v hL hz e
  have hu : primeRank 3 K ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hK.1.1) (inclusion_injective hK.1.1)).trans
      ((hG.involution_centralizer_sqtk hv).stronglyQuasithin 3 (by decide) (by decide))
  exact (SourceContainment.RankTwo.LocalApplication.source_intrinsic_quasisimple
    hG hA36 K L T z v hv hK (le_antisymm hu hl)).1

include hG hA36 in
/-- Central kernel for the literal core comparison of any subgroup of K. -/
theorem source_coreComparison_ker_le_center
    (hv : orderOf v = 2) (hK : K ∈ Yz L T z v)
    (hW : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v))
    (e : plusImage K L T z v hL hz K ≃* Sp F)
    (H : Subgroup G) (hHK : H ≤ K) :
    (LinearThree.LocalStructure.coreComparison K L T H z v hL hz hHK).ker ≤
      center (H ⧸ pCore 2 H) := by
  let := source_intrinsic_quasisimple K L T z v hL hz hG hA36 hv hK e
  exact LinearThree.LocalStructure.coreComparison_ker_le_center_of_component_core
    K L T H z v hL hz hHK hK hW

include hG hA36 in
/-- Source kernel control for the published point-preimage residual. -/
theorem point_coreComparison_ker_le_center
    (hv : orderOf v = 2) (hK : K ∈ Yz L T z v)
    (hW : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v))
    (e : plusImage K L T z v hL hz K ≃* Sp F) :
    (LinearThree.LocalStructure.coreComparison K L T
      (residualIn (pointPreimage K L T z v hL hz e)) z v hL hz
      ((map_subtype_le _).trans (pointPreimage_le K L T z v hL hz e))).ker ≤
        center (residualIn (pointPreimage K L T z v hL hz e) ⧸
          pCore 2 (residualIn (pointPreimage K L T z v hL hz e))) :=
  source_coreComparison_ker_le_center K L T z v hL hz hG hA36 hv hK hW e _ _

include hG hA36 in
/-- Source kernel control for the published plane-preimage residual. -/
theorem plane_coreComparison_ker_le_center
    (hv : orderOf v = 2) (hK : K ∈ Yz L T z v)
    (hW : WK K L T z v ∈ Chapter6.Source.reducedFamily (plusActor K L T v))
    (e : plusImage K L T z v hL hz K ≃* Sp F) :
    (LinearThree.LocalStructure.coreComparison K L T
      (residualIn (planePreimage K L T z v hL hz e)) z v hL hz
      ((map_subtype_le _).trans (planePreimage_le K L T z v hL hz e))).ker ≤
        center (residualIn (planePreimage K L T z v hL hz e) ⧸
          pCore 2 (residualIn (planePreimage K L T z v hL hz e))) :=
  source_coreComparison_ker_le_center K L T z v hL hz hG hA36 hv hK hW e _ _

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.Assembly.SymplecticFour.MarkedAction
