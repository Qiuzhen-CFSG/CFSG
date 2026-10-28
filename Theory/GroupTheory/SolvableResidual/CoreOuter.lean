module
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.SolvableResidual.TwoSupplement
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.SolvableRadical.Transport

/-!
# Residuals from the outer action after removing the two-core

In a radical-free finite group the generalized Fitting subgroup lies in
its solvable residual. Self-centralization then places the centralizer of
that residual inside the residual, making it abelian and hence trivial.
The quotient therefore embeds in the residual's actual outer group.

If the radical of G is O₂(G) and the residual of G/O₂(G) has two-group
outer automorphisms, the induced quotient map has two-group kernel and
image. Thus G/G∞ is a two-group, and G∞ = O²(G). The lifting argument
retains the canonical two-core and solvable-residual quotient maps.

Source: the outer-action argument of Aschbacher--Smith 14.6.23(1),
printed p.1038, expressed independently of the source component models.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem centralizer_solvableResidual_eq_bot_of_radical_eq_bot
    (hR : solvableRadical G = ⊥) :
    centralizer (solvableResidual G : Set G) = ⊥ := by
  have hF : generalizedFitting G ≤ solvableResidual G := by
    apply sup_le
    · exact (le_solvableRadical (fittingSubgroup G) inferInstance inferInstance).trans
        (hR.le.trans bot_le)
    · apply sSup_le
      intro K hK
      let := hK.2
      exact le_solvableResidual_of_isPerfect K
  let C := centralizer (solvableResidual G : Set G)
  have hC : C ≤ solvableResidual G :=
    (centralizer_le hF).trans ((centralizer_generalizedFitting_le G).trans hF)
  have hcomm : IsMulCommutative C := le_centralizer_iff_isMulCommutative.mp
    (show C ≤ centralizer (C : Set G) from centralizer_le hC)
  let := hcomm
  let : Group.IsSolvable C := Group.isSolvable_of_comm hcomm.is_comm.comm
  exact le_bot_iff.mp ((le_solvableRadical C inferInstance inferInstance).trans hR.le)

theorem quotient_solvableResidual_isTwoGroup_of_core_outer
    (hR : solvableRadical G = pCore 2 G)
    (ho : IsPGroup 2 (MulAut.Outer (solvableResidual (G ⧸ pCore 2 G)))) :
    IsPGroup 2 (G ⧸ solvableResidual G) := by
  let Q := G ⧸ pCore 2 G
  let q := QuotientGroup.mk' (pCore 2 G)
  let D := solvableResidual G
  let E := solvableResidual Q
  have hQ : solvableRadical Q = ⊥ := by
    change solvableRadical (G ⧸ pCore 2 G) = ⊥
    have hh := map_solvableRadical_equiv (QuotientGroup.quotientMulEquivOfEq hR)
    rw [solvableRadical_quotient_solvableRadical,map_bot] at hh
    exact hh.symm
  have he : D.map q = E := map_solvableResidual_eq q (QuotientGroup.mk'_surjective _)
  have hq2 : IsPGroup 2 (Q ⧸ E) := ho.of_injective (MulAut.outerAction E)
    (MulAut.outerAction_injective E (centralizer_solvableResidual_eq_bot_of_radical_eq_bot hQ))
  let f : G ⧸ D →* Q ⧸ E := QuotientGroup.map D E q (map_le_iff_le_comap.mp he.le)
  have hk : f.ker = (pCore 2 G).map (QuotientGroup.mk' D) := by
    rw [QuotientGroup.ker_map,←he,comap_map_eq,show q.ker = pCore 2 G from QuotientGroup.ker_mk' _,map_sup,
      QuotientGroup.map_mk'_self,bot_sup_eq]
  have hf : IsPGroup 2 f.ker := hk ▸ pCore_isPGroup.map (QuotientGroup.mk' D)
  exact ((hq2.to_subgroup ⊤).comap_of_ker_isPGroup f hf).of_equiv
    ((MulEquiv.subgroupCongr (comap_top f)).trans topEquiv)

theorem residuals_eq_of_core_outer
    (hR : solvableRadical G = pCore 2 G)
    (ho : IsPGroup 2 (MulAut.Outer (solvableResidual (G ⧸ pCore 2 G)))) :
    solvableResidual G = pResidual 2 G := by
  apply le_antisymm
  · let : Group.IsNilpotent (G ⧸ pResidual 2 G) :=
      (isPGroup_quotient_pResidual 2).isNilpotent
    exact solvableResidual_le_of_solvable_quotient _
  · exact sInf_le ⟨inferInstance,quotient_solvableResidual_isTwoGroup_of_core_outer hR ho⟩

end Subgroup
