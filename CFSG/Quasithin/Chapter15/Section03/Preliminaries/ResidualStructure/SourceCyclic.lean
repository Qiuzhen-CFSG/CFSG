module
public import Theory.GroupTheory.OddPrimeSectionCentralizers.FaithfulTwo
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.ThompsonRank

/-!
# The actual faithful cyclic action in 14.1.17(4)

Quasithinness bounds the three-rank of the original local group M. The actual
intersection core has two-group image in M/O₂(M). For every nonidentity r in
this image, faithfulness of its cyclic action on the three-core gives a moved
involution. The full section-centralizer theorem makes every Sylow three-group
of C_{M/O₂(M)}(r) cyclic. The rank bound stays on M throughout.

This discharges exactly the faithful_cyclic source field used by 15.3.7.
Source: Aschbacher--Smith 14.1.17(4), printed p.980, using A.1.31(1).
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03
variable {G : Type*} [Group G] [Finite G]

theorem source_faithful_cyclic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {M Mc : Subgroup G}
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (r : ThreeAlternatives.StarGroup M)
    (hr : r ∈ ThreeAlternatives.star M ((M ⊓ Mc).pCoreIn 2)) (hne : r ≠ 1)
    (hfaith : Function.Injective
      ((MulAut.conjNormal : ThreeAlternatives.StarGroup M →*
        MulAut (pCore 3 (ThreeAlternatives.StarGroup M))).domRestrict (zpowers r)))
    (P : Sylow 3 (centralizer (zpowers r : Set (ThreeAlternatives.StarGroup M)))) :
    IsCyclic P := by
  let H := ThreeAlternatives.StarGroup M
  let C := centralizer (zpowers r : Set H)
  let R := (P : Subgroup C).map C.subtype
  have htwo : IsPGroup 2 (ThreeAlternatives.star M ((M ⊓ Mc).pCoreIn 2)) :=
    ((isPGroup_pCoreIn 2 (M ⊓ Mc)).comap_subtype (K := M)).map _
  have hcyc : IsCyclic R := cyclic_pSubgroup_in_two_centralizer_of_faithful
    (by decide : Odd 3) (QuotientGroup.mk' (pCore 2 M)) (QuotientGroup.mk'_surjective _)
    ((hG.twoLocal_sqtk hM.1.1).stronglyQuasithin 3 Nat.prime_three (by decide))
    (pCore 3 H) pCore_isPGroup (zpowers r) (htwo.to_le (zpowers_le.mpr hr))
    (fun he => hne (mem_bot.mp (he ▸ mem_zpowers r))) hfaith R
    (P.isPGroup'.map C.subtype) (map_subtype_le _)
  exact ((P : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective).isCyclic.mpr hcyc

end CFSG.Quasithin.Chapter15.Section03
