module

public import Theory.GroupTheory.PerfectNormalizerLift
public import Theory.GroupAction.PerfectCentralQuotient.FixedResidual
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import Theory.GroupTheory.PResidual.FiniteImage


/-!
# Components in fixed subgroups of perfect central covers

If the perfect residual of the quotient's fixed subgroup is quasisimple,
then every component of the original fixed subgroup maps onto that
residual. Lift the quotient residual to a perfect pointwise-fixed subgroup;
its central covering is quasisimple. Perfect image containment puts the
component inside this lift, and component maximality gives equality.
An element fixed in the quotient therefore normalizes the actual component.

The final lemma converts a quasisimple two-residual to the same perfect
residual. It preserves the distinction between O² and the solvable residual.
Application: Aschbacher–Smith, 16.3.9, printed p.1181, using the earlier
field-centralizer statement 16.1.4(4), printed p.1171.
-/

public section

open Subgroup Theory.GroupTheory
namespace MulAut
variable {K Q : Type*} [Group K] [Finite K] [Group Q]

theorem component_image_eq_fixedPerfectResidual
    (e : K ⧸ center K ≃* Q) (a : MulAut K)
    (L : Subgroup K) (hL : IsComponentIn L a.fixedSubgroup)
    [IsQuasisimple (fixedPerfectResidual (centralQuotientAction e a))] :
    L.map (e.toMonoidHom.comp (QuotientGroup.mk' (center K))) =
      fixedPerfectResidual (centralQuotientAction e a) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let b := centralQuotientAction e a
  have hker : q.ker ≤ center K := by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    apply e.injective
    exact hx.trans (map_one e).symm
  obtain ⟨P, hP, hPa, hPq⟩ := exists_perfect_fixed_lift e a
  let := hP
  let : IsQuasisimple (P.map q) := IsQuasisimple.of_mulEquiv
    (MulEquiv.subgroupCongr hPq).symm
  let c : PerfectCentralCovering.Cover P (P.map q) := {
    toMonoidHom := q.subgroupMap P
    surjective := q.subgroupMap_surjective P
    isPerfect := hP
    ker_le_center := by
      intro x hx
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      exact mem_center_iff.mp (hker (show (x : K) ∈ q.ker from
        congrArg Subtype.val (MonoidHom.mem_ker.mp hx))) y }
  let := c.isQuasisimple
  let := hL.quasisimple
  let : Group.IsPerfect (L.map q) := Group.IsPerfect.map q
  have hLb : L.map q ≤ b.fixedSubgroup := by
    rintro _ ⟨x,hx,rfl⟩
    apply (mem_fixedSubgroup _ _).mpr
    change b (e (QuotientGroup.mk' (center K) x)) = _
    rw [centralQuotientAction_apply]
    rw [(mem_fixedSubgroup _ _).mp (hL.1 hx)]
    rfl
  have hLD : L.map q ≤ P.map q := by
    rw [hPq]
    exact le_map_solvableResidual_of_isPerfect (L.map q) b.fixedSubgroup hLb
  have hLP : L ≤ P := le_of_map_le_of_perfect q hker L P hLD
  have hcomp := hL.restrict hLP hPa
  have htop : IsComponent P (⊤ : Subgroup P) :=
    ⟨.top, IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm⟩
  have hEq : L = P := le_antisymm hLP
    (subgroupOf_eq_top.mp (hcomp.2.eq_of_le htop le_top))
  exact hEq ▸ hPq

theorem fixed_quotient_normalizes_component
    (e : K ⧸ center K ≃* Q) (a : MulAut K)
    (L : Subgroup K) (hL : IsComponentIn L a.fixedSubgroup)
    [IsQuasisimple (fixedPerfectResidual (centralQuotientAction e a))]
    (x : K) (hx : e (QuotientGroup.mk' (center K) x) ∈
      (centralQuotientAction e a).fixedSubgroup) : x ∈ normalizer L := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hker : q.ker ≤ center K := by
    intro y hy
    apply (QuotientGroup.eq_one_iff y).mp
    apply e.injective
    exact hy.trans (map_one e).symm
  let := hL.quasisimple
  rw [← comap_normalizer_map_eq_of_perfect q hker L]
  change q x ∈ normalizer (L.map q)
  rw [component_image_eq_fixedPerfectResidual e a L hL]
  exact (solvableResidual (centralQuotientAction e a).fixedSubgroup).le_normalizer_map
    (centralQuotientAction e a).fixedSubgroup.subtype
    ⟨⟨q x, hx⟩, by rw [normalizer_eq_top]; trivial, rfl⟩

end MulAut

namespace MulAut
open Subgroup Theory.GroupTheory
variable {Q : Type*} [Group Q] [Finite Q]

theorem fixedPerfectResidual_quasisimple_of_twoResidual (a : MulAut Q)
    [IsQuasisimple (pResidual 2 a.fixedSubgroup)] :
    IsQuasisimple (fixedPerfectResidual a) := by
  have hle : pResidual 2 a.fixedSubgroup ≤ solvableResidual a.fixedSubgroup :=
    le_solvableResidual_of_isPerfect _
  have hge : solvableResidual a.fixedSubgroup ≤ pResidual 2 a.fixedSubgroup := by
    let : Group.IsNilpotent (a.fixedSubgroup ⧸ pResidual 2 a.fixedSubgroup) :=
      (isPGroup_quotient_pResidual (G := a.fixedSubgroup) 2).isNilpotent
    exact solvableResidual_le_of_solvable_quotient _
  have he : solvableResidual a.fixedSubgroup = pResidual 2 a.fixedSubgroup :=
    le_antisymm hge hle
  let e := (solvableResidual a.fixedSubgroup).equivMapOfInjective
    a.fixedSubgroup.subtype a.fixedSubgroup.subtype_injective
  let : IsQuasisimple (solvableResidual a.fixedSubgroup) :=
    IsQuasisimple.of_mulEquiv (MulEquiv.subgroupCongr he).symm
  exact IsQuasisimple.of_mulEquiv e

end MulAut
