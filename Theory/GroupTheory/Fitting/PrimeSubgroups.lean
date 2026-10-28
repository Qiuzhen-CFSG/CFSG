module

public import Theory.GroupTheory.Fitting.Core

/-!
# Prime subgroups inside the Fitting subgroup

A p-subgroup of F(G) lies in a Sylow p-subgroup of that normal nilpotent
group. The Sylow subgroup is characteristic there, so its ambient image
lies in O_p(G). Thus containment in F(G) suffices; no equality F(G)=O_p(G)
is needed. This is used for the canonical factors in Aschbacher--Smith
D.2.12 and its application in 3.2.13, printed pp.183--184 and584--585.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative

namespace Theory.GroupTheory
theorem IsPGroup.le_pCore_of_le_fitting
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {D : Subgroup H} (hD : IsPGroup p D) (hDF : D ≤ fittingSubgroup H) :
    D ≤ pCore p H := by
  let F := fittingSubgroup H
  obtain ⟨S, hS⟩ := (hD.comap_subtype : IsPGroup p (D.subgroupOf F)).exists_le_sylow
  have hm := map_mono (f := F.subtype) hS
  change (D.subgroupOf F).map F.subtype ≤ _ at hm
  rw [map_subgroupOf_eq_of_le (show D ≤ F from hDF)] at hm
  exact hm.trans (Sylow.map_le_pCore inferInstance inferInstance p S)
end Theory.GroupTheory
