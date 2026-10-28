module

public import Theory.AlgebraicGroup.Bor1.ChevalleyWeightDifferentialKernel
public import Theory.AlgebraicGroup.Bor1.DiagonalizableCentralizerTangent
public import Theory.AlgebraicGroup.Bor1.DiagonalizableFixedTangentLifting
public import Theory.AlgebraicGroup.Bor1.ExactKernelClosedImageSeparableProjection
public import Theory.AlgebraicGroup.Bor1.InvariantPullbackSurjective
public import Theory.AlgebraicGroup.Bor1.QuotientUniversal
public import Theory.AlgebraicGroup.ClosedSubgroup.FiniteIndex
public import Theory.AlgebraicGroup.Dimension.Strict
public import Theory.AlgebraicGroup.Tori.Power

/-!
# Surjectivity from diagonalizable centralizers

A point-surjective morphism onto a torus remains point-surjective when
restricted to the ambient identity component of the centralizer of a
diagonalizable closed subgroup.  This is the conjugation specialization of
Bor1, Chapter 3, Proposition 9.6 and supplies the centralizer-lifting step in
the solvable torus-complement argument.

The original morphism can be inseparable, so the proof first replaces it by
the exact-kernel quotient whose identity differential is surjective.  Exactness
of fixed tangents for the diagonalizable conjugation action and the tangent
formula for the closed centralizer make its centralizer image finite-index.
The point-bijective comparison with the original torus transfers finite index;
connectedness of a torus then gives surjectivity.  A final finite-index
argument restricts the source to the centralizer's identity component.
-/

universe u

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

open Bor1

variable {k : Type u} [Field k] [IsAlgClosed k]

private theorem image_finiteIndex_of_identityTangent_surjective
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (f : AlgebraicGroup.Morphism G Q)
    (hdf : Function.Surjective (Bor1.identityTangentMorphismLinearMap f)) :
    f.imageClosedSubgroup.toSubgroup.FiniteIndex := by
  let J := f.imageClosedSubgroup
  letI : AlgebraicGroup J.carrierVariety := J.carrierAlgebraicGroup
  obtain ⟨p, -, -, hp⟩ := f.closedImageProjection_exists
  have hfactor : J.inclusion.comp p = f := by
    apply AlgebraicGroup.Morphism.ext
    funext x
    exact hp x
  have hdInclusion : Function.Surjective
      (Bor1.identityTangentMorphismLinearMap J.inclusion) := by
    intro D
    obtain ⟨E, hE⟩ := hdf D
    refine ⟨Bor1.identityTangentMorphismLinearMap p E, ?_⟩
    have hcomp := Bor1.identityTangentMorphismLinearMap_comp p J.inclusion
    rw [hfactor] at hcomp
    exact (LinearMap.congr_fun hcomp E).symm.trans hE
  let e : Bor1.IdentityPointDerivation J.carrierVariety ≃ₗ[k]
      Bor1.IdentityPointDerivation Q :=
    LinearEquiv.ofBijective (Bor1.identityTangentMorphismLinearMap J.inclusion)
      ⟨Bor1.identityTangentMorphismLinearMap_inclusion_injective J, hdInclusion⟩
  have hdimNat : Cardinal.toNat (Variety.dimension J.carrierVariety) =
      Cardinal.toNat (Variety.dimension Q) := by
    rw [← Bor1.identityPointDerivation_finrank_eq_dimension,
      ← Bor1.identityPointDerivation_finrank_eq_dimension]
    exact e.finrank_eq
  have hdim : Variety.dimension J.carrierVariety = Variety.dimension Q :=
    (Cardinal.toNat_inj_of_lt_aleph0
      (variety_dimension_lt_aleph0 J.carrierVariety)
      (variety_dimension_lt_aleph0 Q)).mp hdimNat
  have hcontains : AlgebraicGroup.identityComponent Q ⊆
      (J.toSubgroup : Set (Variety.Point Q)) :=
    (closedSubgroup_dimension_eq_iff_contains_identityComponent Q J).mp hdim
  letI : (AlgebraicGroup.identityComponentSubgroup Q).FiniteIndex :=
    AlgebraicGroup.identityComponentSubgroup_finiteIndex Q
  have hcontains' : AlgebraicGroup.identityComponentSubgroup Q ≤ J.toSubgroup :=
    hcontains
  exact Subgroup.finiteIndex_of_le hcontains'

private theorem diagonalizableCentralizer_identityTangent_surjective
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (f : AlgebraicGroup.Morphism G Q)
    (S : ClosedSubgroup G)
    (hS : IsDiagonalizableClosedSubgroup S)
    (hdf : Function.Surjective (Bor1.identityTangentMorphismLinearMap f))
    (hQcomm : IsMulCommutative (Variety.Point Q)) :
    Function.Surjective
      (Bor1.identityTangentMorphismLinearMap
        (f.comp S.centralizer.inclusion)) := by
  intro x
  obtain ⟨y, hy, hfixed⟩ :=
    Bor1.identityTangentMorphismLinearMap_fixed_lift_of_commutative_target
      f S hS hdf hQcomm x
  obtain ⟨z, hz⟩ :=
    Bor1.identityTangent_fixed_mem_centralizer_range S hS y hfixed
  refine ⟨z, ?_⟩
  calc
    Bor1.identityTangentMorphismLinearMap
        (f.comp S.centralizer.inclusion) z =
        Bor1.identityTangentMorphismLinearMap f
          (Bor1.identityTangentMorphismLinearMap
            S.centralizer.inclusion z) := by
      rw [Bor1.identityTangentMorphismLinearMap_comp]
      rfl
    _ = Bor1.identityTangentMorphismLinearMap f y := by rw [hz]
    _ = x := hy

private theorem diagonalizableCentralizer_surjective
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (f : AlgebraicGroup.Morphism G Q)
    (hf : Function.Surjective f.onPoints)
    (hQ : IsTorus Q)
    (S : ClosedSubgroup G)
    (hS : IsDiagonalizableClosedSubgroup S) :
    Function.Surjective (f.comp S.centralizer.inclusion).onPoints := by
  let N := f.kernelClosedSubgroup
  have hN : N.toSubgroup.Normal := f.kernelClosedSubgroup_isNormal
  obtain ⟨P⟩ :=
    Bor1.ClosedSubgroup.chevalleyWeightBlockExactDifferentialKernel_nonempty N hN
  letI : AddCommGroup P.V := P.addCommGroup
  letI : Module k P.V := P.module
  letI : FiniteDimensional k P.V := P.finiteDimensional
  let Qbar := P.morphism.imageClosedSubgroup
  letI : AlgebraicGroup Qbar.carrierVariety := Qbar.carrierAlgebraicGroup
  obtain ⟨q, hqSurj, hqKer, -, hdq⟩ :=
    P.closedImageProjection_exactTangentKernel_surjective_exists N
  have hqPull : Function.Surjective
      (q.pullbackToRightInvariantCoordinateRing N (by rw [hqKer])) :=
    Bor1.pullbackToRightInvariantCoordinateRing_surjective
      N q hqSurj hqKer hdq
  obtain ⟨psi, hpsi, -⟩ :=
    Bor1.quotient_universal_of_surjective_invariant_pullback
      N hN q hqSurj hqKer hqPull
      (inferInstance : AlgebraicGroup Q) f (by rfl)
  have hpsiApply : ∀ x : Variety.Point G,
      psi.onPoints (q.onPoints x) = f.onPoints x := by
    intro x
    exact congrArg (fun g : AlgebraicGroup.Morphism G Q ↦ g.onPoints x) hpsi
  have hpsiSurj : Function.Surjective psi.onPoints := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨q.onPoints x, hpsiApply x⟩
  have hpsiInj : Function.Injective psi.onPoints := by
    intro a b hab
    obtain ⟨x, rfl⟩ := hqSurj a
    obtain ⟨y, rfl⟩ := hqSurj b
    have hfxy : f.onPoints x = f.onPoints y :=
      (hpsiApply x).symm.trans (hab.trans (hpsiApply y))
    have hfKer : x * y⁻¹ ∈ f.kernel := by
      change f.onPoints (x * y⁻¹) = 1
      rw [map_mul, map_inv, hfxy]
      simp
    have hqKer' : x * y⁻¹ ∈ q.kernel := by
      rw [hqKer]
      exact hfKer
    have hqOne := MonoidHom.mem_ker.mp hqKer'
    rw [map_mul, map_inv] at hqOne
    exact mul_inv_eq_one.mp hqOne
  have hQbarComm : IsMulCommutative (Variety.Point Qbar.carrierVariety) := by
    rw [isMulCommutative_iff]
    intro a b
    apply hpsiInj
    rw [map_mul, map_mul]
    have hQcomm := hQ.isMulCommutative
    rw [isMulCommutative_iff] at hQcomm
    exact hQcomm _ _
  let C := S.centralizer
  let qC : AlgebraicGroup.Morphism C.carrierVariety Qbar.carrierVariety :=
    q.comp C.inclusion
  have hdqC : Function.Surjective
      (Bor1.identityTangentMorphismLinearMap qC) :=
    diagonalizableCentralizer_identityTangent_surjective
      q S hS hdq hQbarComm
  let J := qC.imageClosedSubgroup
  letI : J.toSubgroup.FiniteIndex :=
    image_finiteIndex_of_identityTangent_surjective qC hdqC
  let fC : AlgebraicGroup.Morphism C.carrierVariety Q :=
    f.comp C.inclusion
  have hcompC : psi.comp qC = fC := by
    apply AlgebraicGroup.Morphism.ext
    funext c
    exact hpsiApply (C.includePoint c)
  have hcompCApply : ∀ c : Variety.Point C.carrierVariety,
      psi.onPoints (qC.onPoints c) = fC.onPoints c := by
    intro c
    exact congrArg
      (fun g : AlgebraicGroup.Morphism C.carrierVariety Q ↦ g.onPoints c) hcompC
  let K := fC.imageClosedSubgroup
  have hKmap : K.toSubgroup = J.toSubgroup.map psi.onPoints := by
    ext y
    constructor
    · intro hy
      change y ∈ fC.image at hy
      rcases hy with ⟨c, rfl⟩
      refine ⟨qC.onPoints c, ⟨c, rfl⟩, ?_⟩
      exact hcompCApply c
    · rintro ⟨z, hz, rfl⟩
      change psi.onPoints z ∈ fC.image
      change z ∈ qC.image at hz
      rcases hz with ⟨c, rfl⟩
      exact ⟨c, (hcompCApply c).symm⟩
  letI : K.toSubgroup.FiniteIndex := by
    rw [hKmap]
    refine ⟨?_⟩
    rw [Subgroup.index_map_of_bijective ⟨hpsiInj, hpsiSurj⟩ J.toSubgroup]
    exact Subgroup.FiniteIndex.index_ne_zero
  have hcontains : AlgebraicGroup.identityComponent Q ⊆
      (K.toSubgroup : Set (Variety.Point Q)) :=
    identityComponent_subset_of_finiteIndexSubgroup Q K
  have hQ0 : AlgebraicGroup.identityComponent Q = Set.univ :=
    (identityComponent_eq_univ_iff_isConnected Q).mpr hQ.isConnected
  intro y
  change y ∈ fC.image
  exact hcontains (by rw [hQ0]; trivial)

/-- The identity component of the centralizer of a diagonalizable closed
subgroup maps onto any torus target of a point-surjective morphism. -/
public theorem Morphism.diagonalizableCentralizer_identityComponent_surjective
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (f : AlgebraicGroup.Morphism G Q)
    (hf : Function.Surjective f.onPoints)
    (hQ : IsTorus Q)
    (S : ClosedSubgroup G)
    (hS : IsDiagonalizableClosedSubgroup S) :
    Function.Surjective
      (f.comp S.centralizer.identityComponentAmbient.inclusion).onPoints := by
  let C := S.centralizer
  let C0 := AlgebraicGroup.identityComponentClosedSubgroup C.carrierVariety
  letI : AlgebraicGroup C0.carrierVariety := C0.carrierAlgebraicGroup
  let R : ClosedSubgroup Q := ClosedSubgroup.top
  let fC : AlgebraicGroup.Morphism C.carrierVariety Q := f.comp C.inclusion
  let g : AlgebraicGroup.Morphism C.carrierVariety R.carrierVariety :=
    fC.codRestrictClosedSubgroup R (fun _ ↦ R.toSubgroup.one_mem)
  have hfC : Function.Surjective fC.onPoints :=
    diagonalizableCentralizer_surjective f hf hQ S hS
  have hg : Function.Surjective g.onPoints := by
    intro y
    obtain ⟨c, hc⟩ := hfC (R.includePoint y)
    refine ⟨c, R.inclusion_injective ?_⟩
    exact (AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply
      fC R (fun _ ↦ R.toSubgroup.one_mem) c).trans hc
  have hR : _root_.IsConnected (R : Set (Variety.Point Q)) := by
    change _root_.IsConnected (Set.univ : Set (Variety.Point Q))
    exact hQ.isConnected
  letI : C0.toSubgroup.FiniteIndex := by
    change (AlgebraicGroup.identityComponentSubgroup C.carrierVariety).FiniteIndex
    infer_instance
  have hC0 := finiteIndex_subgroup_surjective_of_connected_target
    C C0 R g hg hR
  intro y
  let yR : Variety.Point R.carrierVariety :=
    R.pointEquiv.symm ⟨y, R.toSubgroup.one_mem⟩
  obtain ⟨c0, hc0⟩ := hC0 yR
  let c : Variety.Point C.carrierVariety := C0.inclusion.onPoints c0
  let xG : Variety.Point G := C.inclusion.onPoints c
  have hx : xG ∈ C.identityComponentAmbient := by
    apply (ClosedSubgroup.mem_identityComponentAmbient_iff C xG).mpr
    exact ⟨c, (C0.pointEquiv c0).property, rfl⟩
  let x : Variety.Point C.identityComponentAmbient.carrierVariety :=
    C.identityComponentAmbient.pointEquiv.symm ⟨xG, hx⟩
  refine ⟨x, ?_⟩
  have hxval : C.identityComponentAmbient.inclusion.onPoints x = xG := by
    change (C.identityComponentAmbient.pointEquiv x).val = xG
    dsimp only [x]
    rw [C.identityComponentAmbient.pointEquiv.apply_symm_apply]
  change f.onPoints (C.identityComponentAmbient.inclusion.onPoints x) = y
  rw [hxval]
  have hc0' := congrArg R.inclusion.onPoints hc0
  change R.inclusion.onPoints (g.onPoints (C0.inclusion.onPoints c0)) =
    R.inclusion.onPoints yR at hc0'
  have hgval : R.inclusion.onPoints
      (g.onPoints (C0.inclusion.onPoints c0)) =
      fC.onPoints (C0.inclusion.onPoints c0) := by
    exact AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply
      fC R (fun _ ↦ R.toSubgroup.one_mem) (C0.inclusion.onPoints c0)
  rw [hgval] at hc0'
  calc
    f.onPoints xG = fC.onPoints (C0.inclusion.onPoints c0) := by rfl
    _ = R.inclusion.onPoints yR := hc0'
    _ = y := by
      change (R.pointEquiv yR).val = y
      dsimp only [yR]
      rw [R.pointEquiv.apply_symm_apply]

end Theory.AlgebraicGroup
