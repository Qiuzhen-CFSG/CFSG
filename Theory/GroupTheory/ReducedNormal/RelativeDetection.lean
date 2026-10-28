module

public import Theory.GroupTheory.ReducedNormal.Detection
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.NormalClosureCentralizerCore
public import Theory.GroupTheory.SylowKernelCore

/-!
# Reduced detecting modules inside an actual overgroup

The Thompson detecting-witness theorem can be applied inside a specified
subgroup H without changing the ambient subgroups K and U. Transport
centralizers and intrinsic cores through H's inclusion, choose the reduced
module there, and transport its detecting identity back to G. Its reduced
quotient remains the literal H/C_H(W), not a quotient of a larger group.

Source: Aschbacher--Smith A.1.18--19, used in13.7.4(1), pp.24,938.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- An elementary detecting module inside H contains a module reduced for
H with the same ambient centralizer in the specified normal subgroup K. -/
theorem exists_relative_reduced_le_centralizer_eq_core
    (H K U : Subgroup G) (hKH : K ≤ H) (hUH : U ≤ H)
    (hKn : H ≤ normalizer (K : Set G)) (hUn : H ≤ normalizer (U : Set G))
    (hE : IsElementaryAbelian p U)
    (hc : K ⊓ centralizer (U : Set G) = K.pCoreIn p) :
    ∃ W : Subgroup H, W ≤ U.subgroupOf H ∧ IsPReduced p W ∧
      K ⊓ centralizer (W.map H.subtype : Set G) = K.pCoreIn p := by
  let J := K.subgroupOf H
  let V := U.subgroupOf H
  let : J.Normal := normal_subgroupOf_of_le_normalizer hKn
  let : V.Normal := normal_subgroupOf_of_le_normalizer hUn
  let : IsElementaryAbelian p U := hE
  let : IsElementaryAbelian p V := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hUH).toMonoidHom (subgroupOfEquivOfLe hUH).injective
  have hJ : J.map H.subtype = K := map_subgroupOf_eq_of_le hKH
  have hV : V.map H.subtype = U := map_subgroupOf_eq_of_le hUH
  have hcentral : J ⊓ centralizer (V : Set H) = J.pCoreIn p := by
    apply map_injective H.subtype_injective
    rw [map_inf _ _ _ H.subtype_injective, map_centralizer_subtype,
      map_pCoreIn_of_injective p J H.subtype H.subtype_injective, hJ, hV,
      ← inf_assoc, inf_eq_left.mpr hKH, hc]
  obtain ⟨W, hWV, hr, hw⟩ := exists_isPReduced_le_centralizer_eq_core J V hcentral
  refine ⟨W, hWV, hr, ?_⟩
  change J ⊓ centralizer (W : Set H) = J.pCoreIn p at hw
  have he := congrArg (map H.subtype) hw
  rw [map_inf _ _ _ H.subtype_injective, map_centralizer_subtype,
    map_pCoreIn_of_injective p J H.subtype H.subtype_injective, hJ,
    ← inf_assoc, inf_eq_left.mpr hKH] at he
  exact he

end Theory.GroupTheory
