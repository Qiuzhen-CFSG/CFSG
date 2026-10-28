module
public import Theory.GroupTheory.SolvableResidual.PerfectQuotient
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.SpecificGroups.BinaryComponentResidual

/-!
# A₆ residuals through a normal two-kernel

The solvable residual of a subgroup with A₆ two-core quotient still maps
onto that literal quotient. The residual is two-perfect and subnormal in
the specified overgroup, so it is a C-component there. The quotient
isomorphism is induced by inclusion of the residual.

Source: Aschbacher--Smith A.3.3, used in 15.1.25(5), printed p.1102.
-/

public section
open Subgroup Theory.GroupTheory
namespace AlternatingSix.TwoKernelResidual
variable {G : Type*} [Group G] [Finite G]

theorem twoCore_eq_bot : pCore 2 (alternatingGroup (Fin 6)) = ⊥ := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rcases (inferInstance : (pCore 2 (alternatingGroup (Fin 6))).Normal).eq_bot_or_eq_top with he | he
  · exact he
  · have hp : IsPGroup 2 (alternatingGroup (Fin 6)) := pCore_isPGroup.of_equiv
      ((MulEquiv.subgroupCongr he).trans topEquiv)
    let : Group.IsNilpotent (alternatingGroup (Fin 6)) := hp.isNilpotent
    exact False.elim (Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 6)) inferInstance)

/-- A normal intersection with A₆ two-core quotient has its actual perfect
residual as a C-component, retaining the original inclusion and quotient. -/
theorem residual_component (H C : Subgroup G)
    (hHC : H ≤ C) (hn : (H.subgroupOf C).Normal)
    (e : (H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 6)) :
    let K := (solvableResidual H).map H.subtype
    (K.subgroupOf C).IsCComponent ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) := by
  let : Group.IsPerfect (H ⧸ pCore 2 H) := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let R := solvableResidual H
  let K := R.map H.subtype
  let j : R ≃* K := R.equivMapOfInjective H.subtype H.subtype_injective
  let er : (R ⧸ pCore 2 R) ≃* alternatingGroup (Fin 6) :=
    (solvableResidualPCoreQuotientEquiv 2).trans e
  let ek : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.congr _ _ j.symm (pCore_map_iso 2 j.symm)).trans er
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple (R ⧸ pCore 2 R) := IsQuasisimple.of_mulEquiv er.symm
  have hp : IsPPerfect 2 R := by
    intro N hN hq
    let := hN
    by_contra hnt
    let : Nontrivial (R ⧸ N) := QuotientGroup.nontrivial_iff.mpr hnt
    let : Group.IsNilpotent (R ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (R ⧸ N) inferInstance
  have hR : R.IsCComponent := isCComponent_of_isPPerfect_of_quasisimple_core_quotient
    (inferInstance : R.Normal).isSubnormal hp
  have hmap := (hR.map_equiv (subgroupOfEquivOfLe hHC).symm).map_subtype hn.isSubnormal
  have heq : ((R.map (subgroupOfEquivOfLe hHC).symm.toMonoidHom).map
      (H.subgroupOf C).subtype) = K.subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [map_subgroupOf_eq_of_le ((map_subtype_le R).trans hHC),map_map,map_map]
    rfl
  exact ⟨heq ▸ hmap,⟨ek⟩⟩

end AlternatingSix.TwoKernelResidual
