module

public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.GroupTheory.CComponent.FittingCentralizer

/-!
# Self-centralization of the generalized Fitting subgroup

For a finite group, the centralizer of F*(G) lies in F*(G). If that
centralizer were nonsolvable, one of its C-components would lift to G.
Since F(G) centralizes that C-component, it is quasisimple and hence lies
in F*(G), contradicting its nonabelian nature. The centralizer is therefore
solvable. Its own Fitting subgroup lies in F(G), and self-centralization
of the Fitting subgroup in a solvable group finishes the argument.

This uses the intrinsic component definition and the lower-layer C-component
and solvable Fitting theorems. Source: the standard generalized Fitting
centralizer theorem, Aschbacher, *Finite Group Theory*, 31.13, cited in
*Sporadic Groups*, proof of 8.12. The
Janko involution-centralizer action is an application.
-/

namespace Theory.GroupTheory
open Subgroup

/-- The generalized Fitting subgroup of a finite group contains its centralizer. -/
public theorem centralizer_generalizedFitting_le
    (G : Type*) [Group G] [Finite G] :
    centralizer (generalizedFitting G : Set G) ≤ generalizedFitting G := by
  let C := centralizer (generalizedFitting G : Set G)
  have hCsolv : Group.IsSolvable C := by
    by_contra hn
    obtain ⟨K, hK⟩ := exists_isCComponent_of_not_isSolvable hn
    let L := K.map C.subtype
    have hL : L.IsCComponent := hK.map_subtype (inferInstance : C.Normal).isSubnormal
    have hLC : L ≤ C := map_subtype_le K
    have hFL : fittingSubgroup G ≤ centralizer (L : Set G) := by
      intro f hf l hl
      exact (hLC hl f (fitting_le_generalizedFitting G hf)).symm
    let : IsQuasisimple L := hL.isQuasisimple_of_fitting_centralizes hFL
    have hLF : L ≤ generalizedFitting G :=
      component_le_generalizedFitting G L ⟨hL.subnormal, inferInstance⟩
    have hcomm : IsMulCommutative L :=
      le_centralizer_iff_isMulCommutative.mp (fun l hl k hk => hLC hl k (hLF hk))
    let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
    let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
    exact Group.IsPerfect.not_isMulCommutative L hcomm
  have hFC : (fittingSubgroup C).map C.subtype ≤ generalizedFitting G :=
    (fittingSubgroup_map_subtype_le_of_isSubnormal C
      (inferInstance : C.Normal).isSubnormal).trans (fitting_le_generalizedFitting G)
  intro c hc
  have hcf : (⟨c, hc⟩ : C) ∈ centralizer (fittingSubgroup C : Set C) := by
    intro f hf
    exact Subtype.ext (hc f (hFC (mem_map_of_mem C.subtype hf)))
  exact hFC (mem_map_of_mem C.subtype
    (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hCsolv hcf))

end Theory.GroupTheory
