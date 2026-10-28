module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.RootDatumMorphismRealization
public import Theory.AlgebraicGroup.Connected

/-!
Integral root-datum realization of a commuting isogeny square.

For source and target root models on a prospective universal carrier and on
the base carrier, `RootDatumIsogenyLiftSquare` records the four integral
Chevalley realization certificates attached to the cover, the base isogeny,
and its proposed lift.  Its three compatibility conditions say that the
character/cocharacter map, the actual-root permutation, and the root-curve
parameters form commuting squares.  Distinct source and target root pairings
are allowed; this is needed when an inseparable isogeny sends a root to a
positive integral multiple of another root.

The lift certificate is realized by
`RootDatumMorphismRealizationData.rootDatumMorphism_of_realizationData`.
Compatibility on root generators and the source-cover presentation prove the
global square.  Uniqueness uses the geometric argument from Steinberg's proof
of GLS3, Chapter 2, Theorem 9.16: the regular pointwise difference of two lifts
has image in the finite kernel of the cover, hence is constant on the connected
semisimple source.  Thus this layer constructs the direct unique isogeny
without strengthening either root-version or semantic universality.
-/

universe u

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- Regard a semisimple carrier and one of its root-system models as a
`SemisimpleVersion`.  This is the adapter used to state root universality for
carrier-level lifting data. -/
public def RootSystemModel.toSemisimpleVersion
    {G : Variety k} [AlgebraicGroup G]
    {ι E E' : Type u} [Finite ι]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
    {P : RootPairing ι ℝ E E'} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (model : RootSystemModel P G) (hG : IsSemisimpleAlgebraicGroup G) :
    SemisimpleVersion (k := k) P where
  carrier := G
  group := inferInstance
  semisimple := hG
  rootModel := model

/-- Two morphisms from a connected variety agree if their postcompositions by
an isogeny agree.  The pointwise quotient is a regular map into the finite
kernel, so its connected image is the identity singleton. -/
private theorem morphism_eq_of_isogeny_postcomp_of_connected
    {G H K : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    [AlgebraicGroup K]
    (u : Morphism H K) (hu : IsIsogeny u)
    (hG : Variety.IsConnected G)
    (f g : Morphism G H) (hcomp : u.comp f = u.comp g) :
    f = g := by
  let delta : Variety.Morphism G H :=
    (AlgebraicGroup.mulMorphism H).comp
      (f.toVariety.pair
        ((AlgebraicGroup.invMorphism H).comp g.toVariety))
  have hdelta_apply (x : Variety.Point G) :
      delta.toFun x = f.onPoints x * (g.onPoints x)⁻¹ := by
    rfl
  have hrange : Set.range delta.toFun ⊆
      (u.kernel : Set (Variety.Point H)) := by
    rintro _ ⟨x, rfl⟩
    change u.onPoints (delta.toFun x) = 1
    rw [hdelta_apply, map_mul, map_inv]
    have hx : u.onPoints (f.onPoints x) = u.onPoints (g.onPoints x) := by
      have hx' := congrArg (fun q : Morphism G K => q.onPoints x) hcomp
      exact hx'
    rw [hx]
    simp
  let : Finite u.kernel := hu.2
  have hrangeFinite : (Set.range delta.toFun).Finite :=
    (Set.toFinite (u.kernel : Set (Variety.Point H))).subset hrange
  have hrangeSubsingleton :=
    connected_finite_morphism_range_subsingleton delta hG hrangeFinite
  apply Morphism.ext f g
  funext x
  have hx := hrangeSubsingleton
    (Set.mem_range_self x) (Set.mem_range_self (1 : Variety.Point G))
  rw [hdelta_apply, hdelta_apply] at hx
  have hx' : f.onPoints x * (g.onPoints x)⁻¹ = 1 := by
    simpa using hx
  exact mul_inv_eq_one.mp hx'

/-- Integral root, Weyl, and root-curve data for the square
`u ∘ lift = f ∘ u`.

The four `RootSystemModelMorphismRealizationData` fields include the integral
root maps, reflection/Weyl compatibility, positive root multiples, Chevalley
generator maps, and regular coordinate descent.  The final three fields are
the compatibility of those maps around the square. -/
public structure RootDatumIsogenyLiftSquare
    {Ku K : Variety k} [AlgebraicGroup Ku] [AlgebraicGroup K]
    {iu it ju jt Eu Eu' Et Et' Fu Fu' Ft Ft' : Type u}
    [Finite iu] [Finite it] [Finite ju] [Finite jt]
    [AddCommGroup Eu] [Module ℝ Eu] [AddCommGroup Eu'] [Module ℝ Eu']
    [AddCommGroup Et] [Module ℝ Et] [AddCommGroup Et'] [Module ℝ Et']
    [AddCommGroup Fu] [Module ℝ Fu] [AddCommGroup Fu'] [Module ℝ Fu']
    [AddCommGroup Ft] [Module ℝ Ft] [AddCommGroup Ft'] [Module ℝ Ft']
    (Pu : RootPairing iu ℝ Eu Eu') [Pu.IsRootSystem]
    [Pu.IsCrystallographic] [Pu.IsReduced]
    (Pt : RootPairing it ℝ Et Et') [Pt.IsRootSystem]
    [Pt.IsCrystallographic] [Pt.IsReduced]
    (Qu : RootPairing ju ℝ Fu Fu') [Qu.IsRootSystem]
    [Qu.IsCrystallographic] [Qu.IsReduced]
    (Qt : RootPairing jt ℝ Ft Ft') [Qt.IsRootSystem]
    [Qt.IsCrystallographic] [Qt.IsReduced]
    (KuSource : RootSystemModel Pu Ku) (KuTarget : RootSystemModel Pt Ku)
    (KSource : RootSystemModel Qu K) (KTarget : RootSystemModel Qt K)
    (CuSource : ChevalleyData Ku KuSource.rootData)
    (CuTarget : ChevalleyData Ku KuTarget.rootData)
    (CSource : ChevalleyData K KSource.rootData)
    (CTarget : ChevalleyData K KTarget.rootData)
    (u : Morphism Ku K) (f : Morphism K K) where
  sourceCover : RootSystemModelMorphismRealizationData Pu Qu
    KuSource KSource CuSource CSource
  targetCover : RootSystemModelMorphismRealizationData Pt Qt
    KuTarget KTarget CuTarget CTarget
  baseEndomorphism : RootSystemModelMorphismRealizationData Qu Qt
    KSource KTarget CSource CTarget
  lift : RootSystemModelMorphismRealizationData Pu Pt
    KuSource KuTarget CuSource CuTarget
  sourceCover_pointHom : u.onPoints = sourceCover.pointHom
  targetCover_pointHom : u.onPoints = targetCover.pointHom
  baseEndomorphism_pointHom : f.onPoints = baseEndomorphism.pointHom
  latticeMap_commutes :
    RootPairing.Hom.comp targetCover.latticeMap lift.latticeMap =
      RootPairing.Hom.comp baseEndomorphism.latticeMap sourceCover.latticeMap
  rootIndex_commutes : ∀ α,
    targetCover.rootIndex (lift.rootIndex α) =
      baseEndomorphism.rootIndex (sourceCover.rootIndex α)
  rootParameterMap_commutes : ∀ α t,
    targetCover.rootParameterMap (lift.rootIndex α)
        (lift.rootParameterMap α t) =
      baseEndomorphism.rootParameterMap (sourceCover.rootIndex α)
        (sourceCover.rootParameterMap α t)

namespace RootDatumIsogenyLiftSquare

variable {Ku K : Variety k} [AlgebraicGroup Ku] [AlgebraicGroup K]
variable {iu it ju jt Eu Eu' Et Et' Fu Fu' Ft Ft' : Type u}
variable [Finite iu] [Finite it] [Finite ju] [Finite jt]
variable [AddCommGroup Eu] [Module ℝ Eu] [AddCommGroup Eu'] [Module ℝ Eu']
variable [AddCommGroup Et] [Module ℝ Et] [AddCommGroup Et'] [Module ℝ Et']
variable [AddCommGroup Fu] [Module ℝ Fu] [AddCommGroup Fu'] [Module ℝ Fu']
variable [AddCommGroup Ft] [Module ℝ Ft] [AddCommGroup Ft'] [Module ℝ Ft']
variable {Pu : RootPairing iu ℝ Eu Eu'} [Pu.IsRootSystem]
variable [Pu.IsCrystallographic] [Pu.IsReduced]
variable {Pt : RootPairing it ℝ Et Et'} [Pt.IsRootSystem]
variable [Pt.IsCrystallographic] [Pt.IsReduced]
variable {Qu : RootPairing ju ℝ Fu Fu'} [Qu.IsRootSystem]
variable [Qu.IsCrystallographic] [Qu.IsReduced]
variable {Qt : RootPairing jt ℝ Ft Ft'} [Qt.IsRootSystem]
variable [Qt.IsCrystallographic] [Qt.IsReduced]
variable {KuSource : RootSystemModel Pu Ku} {KuTarget : RootSystemModel Pt Ku}
variable {KSource : RootSystemModel Qu K} {KTarget : RootSystemModel Qt K}
variable {CuSource : ChevalleyData Ku KuSource.rootData}
variable {CuTarget : ChevalleyData Ku KuTarget.rootData}
variable {CSource : ChevalleyData K KSource.rootData}
variable {CTarget : ChevalleyData K KTarget.rootData}
variable {u : Morphism Ku K} {f : Morphism K K}

/-- The source-cover certificate identifies the supplied cover with an
isogeny. -/
public theorem sourceCover_isogeny
    (S : RootDatumIsogenyLiftSquare Pu Pt Qu Qt KuSource KuTarget
      KSource KTarget CuSource CuTarget CSource CTarget u f) :
    IsIsogeny u := by
  constructor
  · simpa only [S.sourceCover_pointHom] using
      S.sourceCover.point_surjective
  · simpa only [Morphism.kernel, S.sourceCover_pointHom] using
      S.sourceCover.kernel_finite

/-- The base realization certificate identifies the supplied endomorphism
with an isogeny. -/
public theorem baseEndomorphism_isogeny
    (S : RootDatumIsogenyLiftSquare Pu Pt Qu Qt KuSource KuTarget
      KSource KTarget CuSource CuTarget CSource CTarget u f) :
    IsIsogeny f := by
  constructor
  · simpa only [S.baseEndomorphism_pointHom] using
      S.baseEndomorphism.point_surjective
  · simpa only [Morphism.kernel, S.baseEndomorphism_pointHom] using
      S.baseEndomorphism.kernel_finite

/-- Steinberg's universal-cover lifting conclusion from an integral
root-datum realization square.  The semisimple hypothesis supplies precisely
the connectedness needed for uniqueness. -/
public theorem existsUnique_isogeny_lift
    (S : RootDatumIsogenyLiftSquare Pu Pt Qu Qt KuSource KuTarget
      KSource KTarget CuSource CuTarget CSource CTarget u f)
    (hKu : IsSemisimpleAlgebraicGroup Ku) :
    ∃! fu : Morphism Ku Ku,
      IsIsogeny fu ∧ u.comp fu = f.comp u := by
  obtain ⟨fu, hfuPoint, hfuIsogeny, _⟩ :=
    S.lift.rootDatumMorphism_of_realizationData
  have hcomm : u.comp fu = f.comp u := by
    apply S.sourceCover.unique_of_generator_agreement
    intro α t
    change u.onPoints (fu.onPoints (CuSource.x α t)) =
      f.onPoints (u.onPoints (CuSource.x α t))
    calc
      u.onPoints (fu.onPoints (CuSource.x α t)) =
          S.targetCover.pointHom
            (S.lift.pointHom (CuSource.x α t)) := by
        rw [S.targetCover_pointHom, hfuPoint]
      _ = S.targetCover.pointHom
          (CuTarget.x (S.lift.rootIndex α)
            (S.lift.rootParameterMap α t)) := by
        rw [S.lift.rootGenerator_transport]
      _ = CTarget.x
          (S.targetCover.rootIndex (S.lift.rootIndex α))
          (S.targetCover.rootParameterMap (S.lift.rootIndex α)
            (S.lift.rootParameterMap α t)) :=
        S.targetCover.rootGenerator_transport _ _
      _ = CTarget.x
          (S.baseEndomorphism.rootIndex (S.sourceCover.rootIndex α))
          (S.baseEndomorphism.rootParameterMap (S.sourceCover.rootIndex α)
            (S.sourceCover.rootParameterMap α t)) := by
        rw [S.rootIndex_commutes, S.rootParameterMap_commutes]
      _ = S.baseEndomorphism.pointHom
          (CSource.x (S.sourceCover.rootIndex α)
            (S.sourceCover.rootParameterMap α t)) :=
        (S.baseEndomorphism.rootGenerator_transport _ _).symm
      _ = S.baseEndomorphism.pointHom
          (S.sourceCover.pointHom (CuSource.x α t)) := by
        rw [S.sourceCover.rootGenerator_transport]
      _ = f.onPoints (u.onPoints (CuSource.x α t)) := by
        rw [S.baseEndomorphism_pointHom, S.sourceCover_pointHom]
  refine ⟨fu, ⟨hfuIsogeny, hcomm⟩, ?_⟩
  intro g hg
  exact morphism_eq_of_isogeny_postcomp_of_connected u
    S.sourceCover_isogeny hKu.1 g fu
    (hg.2.trans hcomm.symm)

/-- The root-universal carrier form of `existsUnique_isogeny_lift`.  Root
universality identifies the source model as the universal version; the
realization square contains the integral data that constructs the lift. -/
public theorem existsUnique_isogeny_lift_of_universalRootVersion
    (S : RootDatumIsogenyLiftSquare Pu Pt Qu Qt KuSource KuTarget
      KSource KTarget CuSource CuTarget CSource CTarget u f)
    (hKu : IsSemisimpleAlgebraicGroup Ku)
    (_hK : IsSemisimpleAlgebraicGroup K)
    (_hUniversal :
      IsUniversalRootVersion (KuSource.toSemisimpleVersion hKu)) :
    ∃! fu : Morphism Ku Ku,
      IsIsogeny fu ∧ u.comp fu = f.comp u := by
  exact S.existsUnique_isogeny_lift hKu

end RootDatumIsogenyLiftSquare

end Theory.AlgebraicGroup
