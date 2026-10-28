module
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent

/-! An ordinary involution-centralizer component remains a component in
any subgroup containing it and the involution. The literal inclusion
into the original centralizer restricts the subnormal chain.
Source application: Aschbacher–Smith 2.5.19, printed pp.563–564. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
variable {G : Type*} [Group G]

theorem component_in_subgroup_centralizer (P : Subgroup G) (i : G)
    (hP : IsComponentIn P (centralizer ({i} : Set G)))
    (J : Subgroup G) (hPJ : P ≤ J) (hiJ : i ∈ J) :
    IsComponentIn (P.subgroupOf J) (centralizer ({(⟨i,hiJ⟩ : J)} : Set J)) := by
  let C := centralizer ({(⟨i,hiJ⟩ : J)} : Set J)
  have hDC : P.subgroupOf J ≤ C := by
    intro p hp
    exact mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp (hP.1 hp)))
  let f : C →* centralizer ({i} : Set G) :=
    (J.subtype.comp C.subtype).codRestrict _ (fun x =>
      mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property)))
  refine ⟨hDC,hP.2.1.comap f,?_⟩
  let : IsQuasisimple P := hP.quasisimple
  exact IsQuasisimple.of_mulEquiv
    ((subgroupOfEquivOfLe hDC).trans (subgroupOfEquivOfLe hPJ)).symm

end CFSG.Quasithin.Chapter2.Section05.Overcomponents
