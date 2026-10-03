module

public import Stellmacher.Recognition.NormalEightNormalImageTransport
public import Stellmacher.Recognition.NormalEightNormalFusion
public import Stellmacher.Recognition.NormalEightExoticRecognition
public import Stellmacher.Recognition.NormalEightExoticExclusion

/-!
# Exclusion of the normal quotient-image branch

Under the no-normal-eight hypothesis, normality of the actual odd-core
quotient image of the unique normal four forces its involutions to fuse and
provides a disjoint commuting conjugate inside the Sylow subgroup. Their
product is an elementary sixteen. Exotic recognition then identifies the
marked Sylow group, and transfer and Sylow enlargement exclude it.

The elementary sixteen is an input to recognition, not itself a contradiction:
the hypothesis bounds only normal elementary subgroups.

Source: Janko–Thompson, Math. Z. 113 (1970), §§3 and 6, pp.387–389 and
394–396, with the exceptional presentation in 1.4(c), p.386.
-/

namespace Stellmacher.Recognition.NormalEightNormalImage

open Subgroup NormalFourCentralOmegaTwo

/-- Normality of the four's actual image in the central-omega normalizer
modulo its odd core is impossible in the no-normal-eight configuration. -/
public theorem false_of_normal_fourImage
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(fourImage S W).Normal] : False := by
  have hfused := NormalEightNormalFusion.involutions_fused
    hns hN S A hA hnonab hZ hno W hW hunique
  obtain ⟨g, hVS, hdisjoint, hcommute⟩ :=
    NormalEightNormalFusion.exists_disjoint_commuting_conjugate
      hns hN S A hA hnonab hZ hno W hW hunique
  obtain ⟨B, hBe, hB, hWB⟩ :=
    elementary_sixteen_of_disjoint_commuting_conjugate S W hW g hVS hdisjoint hcommute
  let : IsElementaryAbelian 2 B := hBe
  obtain ⟨d, hWd⟩ := NormalEightExoticRecognition.exists_presentation
    hns hN S A hA hnonab hZ hno W hW hunique hfused B hB hWB
  exact NormalEightExoticExclusion.false_of_presentation
    hns hN S A hA hnonab hZ hno W hW hunique d hWd hfused g hVS hdisjoint hcommute

end Stellmacher.Recognition.NormalEightNormalImage
