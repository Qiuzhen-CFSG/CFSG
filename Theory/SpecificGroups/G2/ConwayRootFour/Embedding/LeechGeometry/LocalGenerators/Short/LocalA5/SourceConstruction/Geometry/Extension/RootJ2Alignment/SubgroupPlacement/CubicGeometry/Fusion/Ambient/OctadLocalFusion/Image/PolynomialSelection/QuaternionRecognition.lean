module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SourceClass
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.PolynomialSelection.KernelAction
public import Theory.GroupTheory.PGroup.ExtraspecialCubicFixedIndex
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Quaternion recognition for the literal octad cubic commutator

The central quotient of the order-512 extraspecial octad kernel has order 256.
Thus 64 fixed cosets give fixed index four. Apply the intrinsic extraspecial
recognition theorem to the conjugation action of the actual cyclic subgroup
in the integral centralizer. Its action commutator maps isomorphically onto
`kernelCommutator r`, with the exact ambient subgroup and quotient conventions
from `SourceClass` and `KernelAction`.

This discharges the group-theoretic recognition step of polynomial class
selection. The parent supplies the fixed-coset count from the independent
trace argument; no polynomial hypothesis is required here.

Source: Aschbacher, *Sporadic Groups* (1994), 25.1–25.5, §46, p.251,
and 49.3(2).
-/

namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction.PolynomialSelection

/-- Sixty-four fixed central cosets in the actual order-512 extraspecial octad
kernel force its commutator with the given cubic subgroup to be quaternion. -/
public theorem quaternionCubic_of_kernelQuotientFixed_card
    (hQ : IsExtraspecial 2 action.ker) (hcard : Nat.card action.ker = 512)
    {r : centralizer} (ho : orderOf r = 3)
    (hfixed : Nat.card (kernelQuotientFixed r) = 64) : QuaternionCubic r := by
  let R := Subgroup.zpowers r
  let : Subgroup.Normalizes R action.ker := ⟨Subgroup.le_normalizer_of_normal⟩
  let : MulDistribMulAction centralizer KernelQuotient :=
    MulDistribMulAction.compHom _ kernelQuotientAction
  have hR : Nat.card R = 3 := (Nat.card_zpowers r).trans ho
  have hF : fixedPointSubgroup R KernelQuotient = kernelQuotientFixed r := by
    ext x
    constructor
    · intro hx
      exact hx ⟨r, Subgroup.mem_zpowers r⟩
    · intro hx a
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp a.property
      have hx' : r • x = x := hx
      have he := MulAction.mem_fixedBy_zpow hx' n
      change (a : centralizer) • x = x
      rwa [hn] at he
  have hc : Nat.card KernelQuotient = Nat.card (fixedPointSubgroup R KernelQuotient) * 4 := by
    rw [hF, hfixed, kernelQuotient_card hQ hcard]
  obtain ⟨e⟩ :=
    hQ.nonempty_commutatorAction_equiv_quaternion_of_fixed_index_four (A := R) hR
    (fun a z => kernel_center_fixed hQ a.val z)
    (fun a x => (kernelQuotientAction_mk a.val x).symm) hc
  have hm : (commutatorAction R action.ker).map action.ker.subtype = kernelCommutator r :=
    commutatorAction_subgroup_conj_map_eq_commutator action.ker R
      Subgroup.le_normalizer_of_normal
  let ei := (commutatorAction R action.ker).equivMapOfInjective action.ker.subtype
    Subtype.val_injective
  exact ⟨((ei.trans (MulEquiv.subgroupCongr hm)).symm).trans e⟩

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction.PolynomialSelection
