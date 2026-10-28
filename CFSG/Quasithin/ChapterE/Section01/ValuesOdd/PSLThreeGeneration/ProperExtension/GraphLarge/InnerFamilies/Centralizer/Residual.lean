module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Centralizer.LinearModel
public import Theory.GroupTheory.SolvableResidual.TwoSupplement
public import Theory.GroupTheory.SolvableResidual.Transport

/-!
# The perfect core in the graph-extension involution centralizer

The intersection with the marked inner subgroup is the projective involution
centralizer. Its quotient in the full centralizer is a two-group, so both
centralizers have the same embedded solvable residual. The linear calculation
identifies that residual with SL₂, retaining the projective scalar kernel.
The local supplement C^∞T has this same residual and satisfies O²(K) = K^∞.

Source: Aschbacher--Smith A.3.21(a), p.55, and E.1.2(E2), p.210.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge

variable (F : Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

/-- The actual inner part of the full centralizer, on its intrinsic carrier. -/
@[expose] def innerCentralizer (z : graphExtension F) :
    Subgroup (centralizer ({z} : Set (graphExtension F))) :=
  (innerPart F).subgroupOf (centralizer ({z} : Set (graphExtension F)))

instance innerCentralizer_normal (z : graphExtension F) : (innerCentralizer F z).Normal :=
  inferInstanceAs ((innerPart F).subgroupOf (centralizer ({z} : Set (graphExtension F)))).Normal

private noncomputable def elementCentralizerEquiv
    {U V : Type*} [Group U] [Group V] (e : U ≃* V) (x : U) :
    centralizer ({x} : Set U) ≃* centralizer ({e x} : Set V) where
  toFun y := ⟨e y, mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp y.property))⟩
  invFun y := ⟨e.symm y, mem_centralizer_singleton_iff.mpr (by
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp y.property)⟩
  left_inv y := Subtype.ext (e.symm_apply_apply y)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' y z := Subtype.ext (e.map_mul y z)

/-- The identification uses the marked PSL₃-to-inner-subgroup equivalence. -/
noncomputable def innerCentralizerEquiv (z : graphExtension F) (hzI : z ∈ innerPart F) :
    innerCentralizer F z ≃*
      centralizer ({(innerPartEquiv F).symm ⟨z, hzI⟩} : Set PSL(3,F)) := by
  let w : innerPart F := ⟨z, hzI⟩
  let e : innerCentralizer F z ≃* centralizer ({w} : Set (innerPart F)) :=
    { toFun := fun x => ⟨⟨x.val.val, x.property⟩,
        mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp x.val.property))⟩
      invFun := fun x => ⟨⟨x.val.val, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩, x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  exact e.trans (elementCentralizerEquiv (innerPartEquiv F).symm w)

omit [Finite F] [IsSimpleGroup PSL(3,F)] in
/-- The full centralizer has two-group quotient by its marked inner part. -/
theorem innerCentralizer_quotient (z : graphExtension F) :
    IsPGroup 2 (centralizer ({z} : Set (graphExtension F)) ⧸ innerCentralizer F z) := by
  let C := centralizer ({z} : Set (graphExtension F))
  let f := (QuotientGroup.mk' (innerPart F)).comp C.subtype
  have he : f.ker = innerCentralizer F z := by
    ext x
    exact QuotientGroup.eq_one_iff x.val
  exact ((innerPart_quotient F).to_subgroup f.range).of_equiv
    ((QuotientGroup.quotientMulEquivOfEq he.symm).trans (QuotientGroup.quotientKerEquivRange f)).symm

/-- The inner centralizer has cyclic centralizer of its own perfect core. -/
theorem innerCentralizer_residual_centralizer_cyclic
    (ho : Odd (Nat.card F)) (hlarge : 3 < Nat.card F)
    (z : graphExtension F) (hzI : z ∈ innerPart F) (hz : orderOf z = 2) :
    IsCyclic (centralizer (solvableResidual (innerCentralizer F z) : Set (innerCentralizer F z))) := by
  let e := innerCentralizerEquiv F z hzI
  have ht : orderOf ((innerPartEquiv F).symm ⟨z, hzI⟩) = 2 :=
    ((innerPartEquiv F).symm.orderOf_eq _).trans ((orderOf_submonoid _).symm.trans hz)
  let P := centralizer ({(innerPartEquiv F).symm ⟨z, hzI⟩} : Set PSL(3,F))
  let : IsCyclic (centralizer (solvableResidual P : Set P)) :=
    CentralizerLinearModel.projective_residual_centralizer_cyclic F ho hlarge _ ht
  have hm := map_centralizer_le_centralizer_image
    (solvableResidual (innerCentralizer F z) : Set _) e.toMonoidHom
  rw [← Subgroup.coe_map, map_solvableResidual_eq e.toMonoidHom e.surjective] at hm
  have hcyc : IsCyclic ((centralizer (solvableResidual (innerCentralizer F z) : Set _)).map
      e.toMonoidHom) := isCyclic_of_le hm
  exact (e.subgroupMap _).isCyclic.mpr hcyc

/-- The full centralizer residual is the actual SL₂, including the graph action. -/
theorem inner_centralizer_residual_equiv
    (ho : Odd (Nat.card F)) (hlarge : 3 < Nat.card F)
    (z : graphExtension F) (hzI : z ∈ innerPart F) (hz : orderOf z = 2) :
    Nonempty (solvableResidual (centralizer ({z} : Set (graphExtension F))) ≃* SL(2,F)) := by
  let N := innerCentralizer F z
  let : Group.IsNilpotent (centralizer ({z} : Set (graphExtension F)) ⧸ N) :=
    (innerCentralizer_quotient F z).isNilpotent
  have ht : orderOf ((innerPartEquiv F).symm ⟨z, hzI⟩) = 2 :=
    ((innerPartEquiv F).symm.orderOf_eq _).trans ((orderOf_submonoid _).symm.trans hz)
  obtain ⟨e⟩ := CentralizerLinearModel.projective_residual_equiv F ho hlarge _ ht
  exact ⟨(solvableResidualEquivOfSolvableQuotient N).symm.trans
    ((innerCentralizerEquiv F z hzI).solvableResidualEquiv.trans e)⟩

omit [Finite F] [IsSimpleGroup PSL(3,F)] in
/-- The residual supplement is a subgroup of the original centralizer. -/
theorem innerCentralizerSupplement_le {T : Sylow 2 (graphExtension F)} {z : graphExtension F}
    (hTz : (T : Subgroup (graphExtension F)) ≤ centralizer ({z} : Set (graphExtension F))) :
    innerCentralizerSupplement F T z ≤ centralizer ({z} : Set (graphExtension F)) :=
  sup_le (map_subtype_le _) hTz

omit [IsSimpleGroup PSL(3,F)] in
/-- Both residuals agree on the literal local supplement, not on the full centralizer. -/
theorem innerCentralizerSupplement_pResidual_eq {T : Sylow 2 (graphExtension F)} {z : graphExtension F}
    (hTz : (T : Subgroup (graphExtension F)) ≤ centralizer ({z} : Set (graphExtension F))) :
    pResidual 2 (innerCentralizerSupplement F T z) = solvableResidual (innerCentralizerSupplement F T z) := by
  let C := centralizer ({z} : Set (graphExtension F))
  let D := (solvableResidual C).map C.subtype
  let : Group.IsPerfect D := Group.IsPerfect.map C.subtype
  have hn : C ≤ normalizer (D : Set (graphExtension F)) := by
    have h := (solvableResidual C).le_normalizer_map C.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using h
  exact pResidual_eq_solvableResidual_of_perfect_sup_twoGroup D T T.isPGroup' (hTz.trans hn)

omit [IsSimpleGroup PSL(3,F)] in
/-- The full centralizer and its supplement have the same embedded residual. -/
theorem innerCentralizerSupplement_residual_map {T : Sylow 2 (graphExtension F)} {z : graphExtension F}
    (hTz : (T : Subgroup (graphExtension F)) ≤ centralizer ({z} : Set (graphExtension F))) :
    (solvableResidual (innerCentralizerSupplement F T z)).map (innerCentralizerSupplement F T z).subtype =
      (solvableResidual (centralizer ({z} : Set (graphExtension F)))).map
        (centralizer ({z} : Set (graphExtension F))).subtype := by
  let C := centralizer ({z} : Set (graphExtension F))
  let D := (solvableResidual C).map C.subtype
  let : Group.IsPerfect D := Group.IsPerfect.map C.subtype
  exact le_antisymm (map_solvableResidual_mono (innerCentralizerSupplement_le F hTz))
    (le_map_solvableResidual_of_isPerfect D _ le_sup_left)

omit [IsSimpleGroup PSL(3,F)] in
/-- The residual comparison is induced by the actual inclusions. -/
noncomputable def innerCentralizerSupplement_residualEquiv
    {T : Sylow 2 (graphExtension F)} {z : graphExtension F}
    (hTz : (T : Subgroup (graphExtension F)) ≤ centralizer ({z} : Set (graphExtension F))) :
    solvableResidual (innerCentralizerSupplement F T z) ≃*
      solvableResidual (centralizer ({z} : Set (graphExtension F))) :=
  ((solvableResidual _).equivMapOfInjective
    (innerCentralizerSupplement F T z).subtype (innerCentralizerSupplement F T z).subtype_injective).trans
    ((MulEquiv.subgroupCongr (innerCentralizerSupplement_residual_map F hTz)).trans
      ((solvableResidual _).equivMapOfInjective
        (centralizer ({z} : Set (graphExtension F))).subtype
        (centralizer ({z} : Set (graphExtension F))).subtype_injective).symm)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge
