module

public import Theory.SpecificGroups.G2.MultiplierThree.UpperBound.LocalReduction
public import Theory.SpecificGroups.G2.MultiplierThree.UpperBound.InvolutionLift.RankOne
public import Theory.SpecificGroups.G2.MultiplierThree.UpperBound.InvolutionLift.Geometry

/-!
# The two-primary multiplier exclusion for the actual G₂(3)

A central double cover splits over the concrete orthogonal local image.
The two SL₂(3) factors lift uniquely, and ternary involution fusion kills
the outer and diagonal defects. The image has odd index, so transfer
excludes any perfect central double cover. Taking a prime-order central
quotient excludes two from every finite perfect central kernel.

In particular the canonical universal kernel is odd. The full inverse
image of the marked involution centralizer therefore gives the requested
local lift with odd kernel. Its application to the shared local-reduction
consumer is explicit below. No local splitting is asserted for a cubic
kernel, and the three-primary calculation remains independent.

Source: Aschbacher–Smith I.1.4(2), printed p.408 (PDF p.419), GLS3 §6.1,
and the binary tetrahedral and actual octonion calculations cited in the
two imported local modules.
-/

public section

namespace Atlas.G2.FiniteCover.MultiplierThree
open PerfectCentralCovering

/-- Two does not divide any finite perfect central kernel over the actual
ternary octonion group. All local geometry and lifting premises are discharged. -/
theorem not_two_dvd_kernel {E : Type*} [Group E] [Finite E]
    (f : Cover E (Model (ZMod 3))) : ¬ 2 ∣ Nat.card f.toMonoidHom.ker := by
  intro hdiv
  obtain ⟨D,hD,hDf,g,hg⟩ := PrimaryReduction.exists_prime_order_quotient f hdiv
  let := hD
  let := hDf
  obtain ⟨s,hs⟩ := InvolutionLift.exists_section_of_double_kernel
    InvolutionLift.localModel InvolutionLift.outer_fusion InvolutionLift.paired_fusion
    g.toMonoidHom g.surjective g.ker_le_center hg
  exact not_dvd_card_kernel_of_section g InvolutionLift.localModel.inclusion.range
    InvolutionLift.localModel.odd_index.not_two_dvd_nat s hs (hg ▸ dvd_rfl)

/-- An unconditional odd-kernel lift of the literal marked involution centralizer. -/
theorem exists_involution_lift :
    ∃ H : Subgroup (CoverGroup (ZMod 3)),
      H.map (universalProjection (Model (ZMod 3))) = TernaryLocals.Involution.P ∧
      ¬ 2 ∣ Nat.card (H ⊓ (universalProjection (Model (ZMod 3))).ker :
        Subgroup (CoverGroup (ZMod 3))) := by
  let f := universalCover (Model (ZMod 3))
  let H := TernaryLocals.Involution.P.comap f.toMonoidHom
  refine ⟨H, ?_, ?_⟩
  · exact Subgroup.map_comap_eq_self_of_surjective f.surjective _
  · intro hdiv
    exact not_two_dvd_kernel f
      (hdiv.trans (Subgroup.card_dvd_of_le (show H ⊓ f.toMonoidHom.ker ≤ f.toMonoidHom.ker
        from inf_le_right)))

/-- The shared involution-local consumer now excludes two unconditionally
from the literal canonical universal kernel. -/
theorem universal_not_two_dvd_kernel :
    ¬ 2 ∣ Nat.card (universalProjection (Model (ZMod 3))).ker := by
  obtain ⟨H,hH,hodd⟩ := exists_involution_lift
  exact not_two_dvd_kernel_of_involution_lift (universalCover _) H hH hodd

end Atlas.G2.FiniteCover.MultiplierThree
