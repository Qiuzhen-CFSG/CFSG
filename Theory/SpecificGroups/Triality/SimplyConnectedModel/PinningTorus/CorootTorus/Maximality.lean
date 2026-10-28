module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.CorootTorus.Coordinates

/-!
# Maximality transfer for the Spin diagonal preimage

A torus containing the diagonal preimage is commutative. Surjectivity of the
Spin cover therefore makes its image centralize the full ordinary diagonal
torus. The ordinary centralizer calculation forces it back into the diagonal
preimage. Thus the preimage is maximal once its torus structure is proved.

The ordinary centralizer containment is an explicit input here. It is supplied
by `evenOrthogonalDiagonalTorus_centralizer_eq` in
`EvenOrthogonalTorusRootExhaustiveness`; no regular inverse to the cover is used.
Source: GLS3, §§1.9 and 1.12, `refs/KGroup/GLS3/Chapter1.tex`.
-/

public section
noncomputable section
namespace Triality.SimplyConnected.Pinning.CorootTorus
open Theory Theory.AlgebraicGroup
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

omit [CharP k 2] in
/-- Maximality of the closed diagonal preimage reduces to its torus structure
and the established ordinary diagonal centralizer calculation. -/
theorem isMaximal_of_isSubtorus
    (hcentral : Subgroup.centralizer
        ((evenOrthogonalDiagonalTorus (k := k) 4 (le_refl 4)).toSubgroup :
          Set _) ≤
      (evenOrthogonalDiagonalTorus (k := k) 4 (le_refl 4)).toSubgroup)
    (hT : IsSubtorus (closedSubgroup k)) :
    IsMaximalTorus (closedSubgroup k) := by
  let cover : AlgebraicGroup.Morphism (groupVariety k)
      (evenSpinActionImageClosedSubgroup (hyperbolicForm (k := k) 4)
        (standardHyperbolicSplit 4)).carrierVariety := (cliffordModel k).spinCover
  refine ⟨hT, ?_⟩
  intro S hS hTS
  let _ := S.carrierAlgebraicGroup
  apply SetLike.coe_injective
  apply Set.Subset.antisymm
  · intro g hg
    change cover.onPoints g ∈
      (evenOrthogonalDiagonalTorus (k := k) 4 (le_refl 4)).toSubgroup
    apply hcentral
    apply Subgroup.mem_centralizer_iff.mpr
    intro a ha
    have hsurj : Function.Surjective cover.onPoints :=
      (cliffordModel k).spinCoverIsogeny.1
    obtain ⟨b, hb⟩ := hsurj a
    have hbT : b ∈ closedSubgroup k := by
      change cover.onPoints b ∈
        (evenOrthogonalDiagonalTorus (k := k) 4 (le_refl 4)).toSubgroup
      rw [hb]
      exact ha
    let bS := S.pointEquiv.symm ⟨b, hTS hbT⟩
    let gS := S.pointEquiv.symm ⟨g, hg⟩
    have hbS : S.inclusion.onPoints bS = b :=
      congrArg Subtype.val (S.pointEquiv.apply_symm_apply _)
    have hgS : S.inclusion.onPoints gS = g :=
      congrArg Subtype.val (S.pointEquiv.apply_symm_apply _)
    have hc := (isMulCommutative_iff.mp hS.isMulCommutative) bS gS
    have hbg : b * g = g * b := by
      simpa only [map_mul, hbS, hgS] using congrArg S.inclusion.onPoints hc
    have him := congrArg cover.onPoints hbg
    simpa only [map_mul, hb] using him
  · exact hTS

end Triality.SimplyConnected.Pinning.CorootTorus
