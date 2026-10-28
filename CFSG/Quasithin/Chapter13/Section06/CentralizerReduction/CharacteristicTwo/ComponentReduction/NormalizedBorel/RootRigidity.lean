module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ActionFacts
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.RootRigidity.LinearThreeAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.RootRigidity.Transport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.RootRigidity.Catalogue
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.RootRigidity.Extensions
public import Theory.SpecificGroups.Suzuki.NormalizedRootCentralizers

/-!
# Model root centralizers in the literal component quotient

An injective model map identifies the center of the actual intersection
Tᵥ* ∩ K* with the model Sylow center. Uniform centralizers in the model
Borel then pass to X* = N(K)/C(K), retaining the specified Borel embedding.
`Catalogue` proves the full center identification and uniform Borel
centralizers for all seven nonsymplectic families, using the actual
compatible marking produced by Borel placement. `Extensions` does the same
for the PGL/PGU and nonsplit alternatives of case (iii), retaining their
parameter restrictions and compatible component embeddings. The source
identity Lᵥ = [Lᵥ,Tᵥ] removes field action before applying the coordinate
calculation throughout the actual relative Borel. Arbitrary semilinear
actors are not claimed to have this property.

The applications `exclude_nonsymplectic_catalogue` and `exclude_extensions`
feed these calculations to the marked a*/z* contradiction. The parent
supplies the earlier component and source alternatives and assembles the
final Sp₄ identification. This module proves the root calculations, not
the earlier classification or the whole of 13.6.6.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927; A.3.16–18.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
open Subgroup Theory.GroupTheory A5Module
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L V : Subgroup G}

/-- The actual Suzuki model gives the uniform calculation for every B ≤ K*.
The arrangement explicitly identifies the specified Sylow intersection. -/
theorem suzuki_root_centralizers (T : Subgroup G) {v : G} (K : Subgroup (Gv v))
    (m : ℕ) (hm : 0 < m) (e : SuzukiMatrixGroup m ≃* NormalizerAction.componentImage K)
    (hU : (SuzukiRootSubgroup m).map
      ((NormalizerAction.componentImage K).subtype.comp e.toMonoidHom) =
        NormalizerAction.sylowImage K (localT T v) ⊓ NormalizerAction.componentImage K)
    (B : Subgroup (XStar K)) (hBK : B ≤ NormalizerAction.componentImage K)
    (r : XStar K) (hr : r ∈ rootCenter T K) (hne : r ≠ 1) :
    B ⊓ centralizer ({r} : Set (XStar K)) =
      B ⊓ centralizer (rootCenter T K : Set (XStar K)) := by
  let f := (NormalizerAction.componentImage K).subtype.comp e.toMonoidHom
  apply root_centralizers_of_model T K f (Subtype.val_injective.comp e.injective)
    (SuzukiRootSubgroup m) ⊤ hU B
  · intro b hb
    refine ⟨e.symm ⟨b, hBK hb⟩, mem_top _, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply ⟨b, hBK hb⟩)
  · exact BenderSuzuki.MatrixGroups.NormalizedRootCentralizers.uniform m hm ⊤
  · exact hr
  · exact hne

/-- Actual application to the source a*/z* asymmetry. The parent supplies
Borel placement inside K*; no root-centralizer premise remains. -/
theorem exclude_suzuki [Finite G] (s : Marking L V)
    (T : Subgroup G) (K : Subgroup (Gv (markedV s)))
    (ha : aLocal s ∈ X K) (hz : zLocal s ∈ X K) (hDN : residual s ≤ X K)
    (hac : aLocal s ∈ centralizer (residual s : Set (Gv (markedV s))))
    (han : aLocal s ∉ centralizer (K : Set (Gv (markedV s))))
    (hzn : zLocal s ∉ centralizer (K : Set (Gv (markedV s))))
    (hER : EStar s K ha hz ≤ rootCenter T K)
    (m : ℕ) (hm : 0 < m) (e : SuzukiMatrixGroup m ≃* NormalizerAction.componentImage K)
    (hU : (SuzukiRootSubgroup m).map
      ((NormalizerAction.componentImage K).subtype.comp e.toMonoidHom) =
        NormalizerAction.sylowImage K (localT T (markedV s)) ⊓ NormalizerAction.componentImage K)
    (B : Subgroup (XStar K)) (hDB : residualStar s K ≤ B)
    (hBK : B ≤ NormalizerAction.componentImage K) : False :=
  exclude_of_root_centralizers s T K ha hz hDN hac han hzn hER B hDB
    (suzuki_root_centralizers T K m hm e hU B hBK)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
