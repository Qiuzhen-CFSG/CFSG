module
public import Stellmacher.ElementaryAbelianMaxPair.FactorFamily
public import Theory.ElementaryAbelian.Injective
/-! # Component and centralizer factors of maximum elementary subgroups
Restrict the original central quotient to the component Sylow intersection.
Its kernel is exactly the common central factor. Elementary full preimages
then give the two literal maximum-order intersections, including the full
Sylow centralizer rather than only its Thompson intersection.
Source: Aschbacher--Smith 2.5.7, printed p.555, the second claim.
-/
public section
open Subgroup
namespace Stellmacher
variable {G Y:Type*} [Group G] [Finite G] [Group Y]
theorem maxFamily_split_component (S K:Subgroup G) (α:K→*Y)
    (hker:α.ker=center K)
    (hlift:∀ W:Subgroup Y,IsElementaryAbelian 2 W→IsElementaryAbelian 2 (W.comap α))
    (hJ:elementaryAbelianMaxJ S≤(S⊓K)⊔(S⊓centralizer (K:Set G)))
    (A:Subgroup G) (hA:A∈elementaryAbelianMaxSubgroups S) :
    let C:=S⊓centralizer (K:Set G)
    A=(A⊓K)⊔(A⊓C) ∧
      A⊓K∈elementaryAbelianMaxSubgroups (S⊓K) ∧
      A⊓C∈elementaryAbelianMaxSubgroups C := by
  let R:=elementaryAbelianMaxJ S
  let SK:=S⊓K
  let C:=S⊓centralizer (K:Set G)
  have hc:SK≤centralizer (C:Set G):=
    le_centralizer_iff.mp (inf_le_right.trans (centralizer_le (show SK≤K from inf_le_right)))
  let q:SK→*Y:=α.comp (inclusion inf_le_right)
  have hk:q.ker=C.subgroupOf SK:=by
    ext k
    change α (inclusion inf_le_right k)=1 ↔ (k:G)∈C
    rw [←MonoidHom.mem_ker,hker]
    constructor
    · intro hk
      refine ⟨k.property.1,?_⟩
      intro a ha
      exact congrArg Subtype.val (mem_center_iff.mp hk ⟨a,ha⟩)
    · intro hk
      apply mem_center_iff.mpr
      intro a
      exact Subtype.ext (hk.2 a a.property)
  have hq (W:Subgroup Y) (hw:IsElementaryAbelian 2 W):IsElementaryAbelian 2 (W.comap q):=by
    let :=hlift W hw
    change IsElementaryAbelian 2 (W.comap (α.comp (inclusion inf_le_right)))
    rw [←comap_comap]
    exact IsElementaryAbelian.comap_of_injective (inclusion inf_le_right)
      (inclusion_injective inf_le_right) (W.comap α)
  have he:=maxFamily_split_central_cover_of_le S SK C q hk hq hc
    (sup_le inf_le_left inf_le_left) A hA ((le_sSup hA).trans hJ)
  have hAK:A⊓SK=A⊓K:=by
    dsimp only [SK]
    rw [←inf_assoc,inf_eq_left.mpr hA.1]
  simpa only [hAK] using he
end Stellmacher
