module
public import Theory.SpecificGroups.Triality.SylowParabolicExtensions
public import Theory.SpecificGroups.Triality.StandardTwoRank.Derived
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
/-!
# Proper Borel overgroups in binary triality have solvable Fitting subgroup

Conjugate the prescribed Sylow to the original positive subgroup. The
rank-two Tits geometry gives either the Borel itself or a full root
parabolic; solvability of the Borel and the parabolic characteristic-two
calculation yield the intrinsic generalized Fitting bound.
Source: GLS3 2.3.4–8; Aschbacher–Smith A.3.12 and C.5.13.
-/
public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Triality.Standard.Parabolics
open ConcreteBruhat OuterOdd.Coverage.RootGeometry.SimpleRecognition
noncomputable section
theorem proper_borel_overgroup_fitting_isSolvable (n : ℕ) (hn : 0 < n)
    (S : Sylow 2 (Carrier (binaryParameters n hn)))
    (H : Subgroup (Carrier (binaryParameters n hn)))
    (hSH : normalizer (S : Set (Carrier (binaryParameters n hn))) ≤ H)
    (hH : H ≠ ⊤) : Group.IsSolvable (generalizedFitting H) := by
  let P := binaryParameters n hn
  let Q := unipotentSylow P rfl
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Carrier P) S Q
  let e := MulAut.conj g
  let X := H.map e.toMonoidHom
  have hX : X ≠ ⊤ := by
    intro he
    apply hH
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_top_of_surjective _ e.surjective]
    exact he
  have hS : (S : Subgroup (Carrier P)).map e.toMonoidHom = unipotent P := by
    change ((g • S : Sylow 2 (Carrier P)) : Subgroup (Carrier P)) = _
    rw [hg]
    rfl
  have hB : borel P ≤ X := by
    rw [← normalizer_unipotent_eq_borel P rfl,← hS,← map_normalizer_eq_of_bijective _ e.bijective]
    exact map_mono hSH
  have hf : Group.IsSolvable (generalizedFitting X) := by
    by_cases he : X = borel P
    · let : Group.IsSolvable X := he.symm ▸ TwoRank.Derived.borel_isSolvable n hn
      infer_instance
    · obtain ⟨a,ha⟩ := eq_parabolic_of_borel_lt n hn X (lt_of_le_of_ne hB (Ne.symm he)) hX
      have hc : centralizer (pCore 2 X : Set X) ≤ pCore 2 X :=
        ha.symm ▸ parabolic_centralizer_twoCore_le P rfl a
      rw [generalizedFitting_eq_pCore_of_selfCentralizing 2 hc]
      let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
      infer_instance
  let eH : H ≃* X := e.subgroupMap H
  let ef : generalizedFitting H ≃* generalizedFitting X :=
    ((generalizedFitting H).equivMapOfInjective eH.toMonoidHom eH.injective).trans
      (MulEquiv.subgroupCongr (map_generalizedFitting_equiv eH))
  exact Group.isSolvable_of_isSolvable_injective (f := ef.toMonoidHom) ef.injective
end
end Triality.Standard.Parabolics
