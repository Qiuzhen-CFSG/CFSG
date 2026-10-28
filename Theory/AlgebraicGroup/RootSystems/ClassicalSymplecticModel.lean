module

public import Theory.AlgebraicGroup.RootSystems.SymplecticRootData
public import Theory.AlgebraicGroup.RootSystems.SymplecticSemisimpleCarrier
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.RootSystemType

/-!
# Direct symplectic type-C root model

For every rank, this module packages the standard symplectic matrix group,
its finite-center projective quotient, and the explicit diagonal-torus root
data as a type-C model.  The construction is characteristic-free over an
algebraically closed field.  Its geometric inputs are the concrete quotient,
the maximality and exhaustive-root calculation for the diagonal torus, and
the direct semisimplicity theorem for the carrier and its isogeny targets.

`RootSystemModel` requires its root and coroot spaces in the universe of the
ground field.  The first part therefore lifts the standard coordinate type-C
pairing into that universe and proves directly that the lift preserves the
finite reduced crystallographic root system and its Dynkin type, including
rank zero.  The realized symplectic root data are then identified with this
lift.  The final existence theorem builds the linked `SymplecticModel` from
the explicit central quotient and records semisimplicity on both sides.

This is the direct classical construction needed by type-C carrier assembly.
It does not use general Chevalley existence, version classification, or GLS3
Theorem 1.10.3(d).  The mathematical model is the standard type-C example in
GLS3, Theorem 1.10.7(c); all construction steps here come from the preceding
explicit symplectic modules.
-/

namespace Theory.AlgebraicGroup

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

set_option linter.style.haveILetI false

open StandardRootSystem

public section

noncomputable section

/-- The standard type-C root space lifted to the ground-field universe. -/
abbrev TypeCRootSpaceULift (m : ℕ) :=
  ULift.{u, 0} (typeCRootSpan m)

/-- The standard type-C coroot space lifted to the ground-field universe. -/
abbrev TypeCCorootSpaceULift (m : ℕ) :=
  ULift.{u, 0} (Module.Dual ℝ (typeCRootSpan m))

/-- The standard coordinate type-C pairing in the ground-field universe. -/
noncomputable def typeCRootPairingULift (m : ℕ) :
    RootPairing (SymplecticRootIndex.{u} m) ℝ
      (TypeCRootSpaceULift.{u} m)
      (TypeCCorootSpaceULift.{u} m) := by
  let P := typeCRootPairing m
  let p := P.toLinearMap.compl₁₂
    (ULift.moduleEquiv : TypeCRootSpaceULift.{u} m ≃ₗ[ℝ]
      typeCRootSpan m).toLinearMap
    (ULift.moduleEquiv : TypeCCorootSpaceULift.{u} m ≃ₗ[ℝ]
      Module.Dual ℝ (typeCRootSpan m)).toLinearMap
  let root : SymplecticRootIndex.{u} m ↪ TypeCRootSpaceULift.{u} m :=
    ⟨fun i => ⟨P.root i.down⟩, by
      intro i j h
      apply ULift.ext
      apply P.root.injective
      exact congrArg ULift.down h⟩
  let coroot : SymplecticRootIndex.{u} m ↪
      TypeCCorootSpaceULift.{u} m :=
    ⟨fun i => ⟨P.coroot i.down⟩, by
      intro i j h
      apply ULift.ext
      apply P.coroot.injective
      exact congrArg ULift.down h⟩
  let reflect (i : SymplecticRootIndex.{u} m) :
      SymplecticRootIndex.{u} m ≃ SymplecticRootIndex.{u} m :=
    Equiv.ulift.trans ((P.reflectionPerm i.down).trans Equiv.ulift.symm)
  letI : p.IsPerfPair := inferInstance
  exact RootPairing.mk p root coroot
    (by intro i; exact P.root_coroot_two i.down)
    reflect
    (by
      intro i j
      apply ULift.ext
      exact P.reflectionPerm_root i.down j.down)
    (by
      intro i j
      apply ULift.ext
      exact P.reflectionPerm_coroot i.down j.down)

/-- Forgetting the universe lift recovers the standard type-C pairing. -/
noncomputable def typeCRootPairingULiftEquiv (m : ℕ) :
    RootPairing.Equiv
      (typeCRootPairingULift m :
        RootPairing (SymplecticRootIndex.{u} m) ℝ
          (TypeCRootSpaceULift.{u} m)
          (TypeCCorootSpaceULift.{u} m))
      (typeCRootPairing m) where
  weightMap := ULift.moduleEquiv.toLinearMap
  coweightMap := ULift.moduleEquiv.symm.toLinearMap
  indexEquiv := Equiv.ulift
  weight_coweight_transpose := by
    ext n x
    rfl
  root_weightMap := by
    ext i
    rfl
  coroot_coweightMap := by
    ext i
    rfl
  bijective_weightMap := ULift.moduleEquiv.bijective
  bijective_coweightMap := ULift.moduleEquiv.symm.bijective

@[simp] private lemma typeCRootPairingULiftEquiv_indexEquiv_apply
    (m : ℕ) (r : SymplecticRootIndex.{u} m) :
    (typeCRootPairingULiftEquiv m).indexEquiv r = r.down := rfl

/-- The universe lift retains the root-system spanning properties. -/
noncomputable instance (m : ℕ) :
    (typeCRootPairingULift m :
      RootPairing (SymplecticRootIndex.{u} m) ℝ
        (TypeCRootSpaceULift.{u} m)
        (TypeCCorootSpaceULift.{u} m)).IsRootSystem where
  span_root_eq_top := by
    change Submodule.span ℝ (Set.range
      (fun i : SymplecticRootIndex.{u} m =>
        (⟨(typeCRootPairing m).root i.down⟩ :
          TypeCRootSpaceULift.{u} m))) = ⊤
    let e : TypeCRootSpaceULift.{u} m ≃ₗ[ℝ] typeCRootSpan m :=
      ULift.moduleEquiv
    apply Submodule.map_injective_of_injective e.injective
    rw [Submodule.map_span]
    have himage : e.toLinearMap '' Set.range
        (fun i : SymplecticRootIndex.{u} m =>
          (⟨(typeCRootPairing m).root i.down⟩ :
            TypeCRootSpaceULift.{u} m)) =
        Set.range (typeCRootPairing m).root := by
      ext y
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i.down, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨⟨(typeCRootPairing m).root i⟩, ⟨⟨i⟩, rfl⟩, rfl⟩
    rw [himage, RootPairing.IsRootSystem.span_root_eq_top,
      Submodule.map_top]
    exact (LinearMap.range_eq_top.mpr e.surjective).symm
  span_coroot_eq_top := by
    change Submodule.span ℝ (Set.range
      (fun i : SymplecticRootIndex.{u} m =>
        (⟨(typeCRootPairing m).coroot i.down⟩ :
          TypeCCorootSpaceULift.{u} m))) = ⊤
    let e : TypeCCorootSpaceULift.{u} m ≃ₗ[ℝ]
        Module.Dual ℝ (typeCRootSpan m) := ULift.moduleEquiv
    apply Submodule.map_injective_of_injective e.injective
    rw [Submodule.map_span]
    have himage : e.toLinearMap '' Set.range
        (fun i : SymplecticRootIndex.{u} m =>
          (⟨(typeCRootPairing m).coroot i.down⟩ :
            TypeCCorootSpaceULift.{u} m)) =
        Set.range (typeCRootPairing m).coroot := by
      ext y
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i.down, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨⟨(typeCRootPairing m).coroot i⟩, ⟨⟨i⟩, rfl⟩, rfl⟩
    rw [himage, RootPairing.IsRootSystem.span_coroot_eq_top,
      Submodule.map_top]
    exact (LinearMap.range_eq_top.mpr e.surjective).symm

/-- The universe lift retains the integral Cartan pairing. -/
noncomputable instance (m : ℕ) :
    (typeCRootPairingULift m :
      RootPairing (SymplecticRootIndex.{u} m) ℝ
        (TypeCRootSpaceULift.{u} m)
        (TypeCCorootSpaceULift.{u} m)).IsCrystallographic where
  exists_value i j := by
    change ∃ z : ℤ, (z : ℝ) = (typeCRootPairing m).pairing i.down j.down
    exact (typeCRootPairing m).exists_value (S := ℤ) i.down j.down

/-- The universe lift retains reducedness. -/
noncomputable instance (m : ℕ) :
    (typeCRootPairingULift m :
      RootPairing (SymplecticRootIndex.{u} m) ℝ
        (TypeCRootSpaceULift.{u} m)
        (TypeCCorootSpaceULift.{u} m)).IsReduced where
  eq_or_eq_neg i j h := by
    change ¬ LinearIndependent ℝ
      ![(⟨(typeCRootPairing m).root i.down⟩ :
          TypeCRootSpaceULift.{u} m),
        (⟨(typeCRootPairing m).root j.down⟩ :
          TypeCRootSpaceULift.{u} m)] at h
    have hdown : ¬ LinearIndependent ℝ
        ![(typeCRootPairing m).root i.down,
          (typeCRootPairing m).root j.down] := by
      intro hli
      apply h
      have hmapped := hli.map'
        (ULift.moduleEquiv.symm : typeCRootSpan m ≃ₗ[ℝ]
          TypeCRootSpaceULift.{u} m).toLinearMap
        (LinearMap.ker_eq_bot.mpr
          (ULift.moduleEquiv.symm : typeCRootSpan m ≃ₗ[ℝ]
            TypeCRootSpaceULift.{u} m).injective)
      have hvectors :
          (![(⟨(typeCRootPairing m).root i.down⟩ :
                TypeCRootSpaceULift.{u} m),
            (⟨(typeCRootPairing m).root j.down⟩ :
                TypeCRootSpaceULift.{u} m)] :
              Fin 2 → TypeCRootSpaceULift.{u} m) =
            (ULift.moduleEquiv.symm : typeCRootSpan m ≃ₗ[ℝ]
              TypeCRootSpaceULift.{u} m) ∘
              ![(typeCRootPairing m).root i.down,
                (typeCRootPairing m).root j.down] := by
        funext x
        fin_cases x <;> rfl
      rw [hvectors]
      exact hmapped
    rcases RootPairing.IsReduced.eq_or_eq_neg i.down j.down hdown with hij | hij
    · left
      apply ULift.ext
      exact hij
    · right
      apply ULift.ext
      exact hij

/-- The realized symplectic base transported to the lifted type-C pairing. -/
noncomputable def typeCRootPairingULiftBase (m : ℕ) :
    (typeCRootPairingULift m :
      RootPairing (SymplecticRootIndex.{u} m) ℝ
        (TypeCRootSpaceULift.{u} m)
        (TypeCCorootSpaceULift.{u} m)).Base :=
  RootPairing.Base.mapEquiv
    (RootPairing.Equiv.symm _ _ (typeCRootPairingULiftEquiv m))
    (symplecticSeed m).base

/-- In positive rank, the lifted pairing has the standard type-C Cartan matrix. -/
theorem typeCRootPairingULift_hasDynkinType_of_pos
    (m : ℕ) (hm : 0 < m) :
    HasDynkinType
      (typeCRootPairingULift m :
        RootPairing (SymplecticRootIndex.{u} m) ℝ
          (TypeCRootSpaceULift.{u} m)
          (TypeCCorootSpaceULift.{u} m)) ⟨.C, m⟩ := by
  let P : RootPairing (SymplecticRootIndex.{u} m) ℝ
      (TypeCRootSpaceULift.{u} m)
      (TypeCCorootSpaceULift.{u} m) := typeCRootPairingULift m
  let e := typeCRootPairingULiftEquiv m
  obtain ⟨b, s, hs⟩ := typeCRootPairing_hasDynkinType_of_pos m hm
  let bu : P.Base := RootPairing.Base.mapEquiv
    (RootPairing.Equiv.symm _ _ e) b
  let su : bu.support ≃ b.support :=
    Equiv.subtypeEquiv e.indexEquiv (fun i => by
      change i ∈ bu.support ↔ e.indexEquiv i ∈ b.support
      rw [show bu = RootPairing.Base.mapEquiv
          (RootPairing.Equiv.symm _ _ e) b by rfl]
      rw [RootPairing.Base.mem_mapEquiv_support]
      simp)
  refine ⟨bu, su.trans s, ?_⟩
  intro i j
  have hcartan : bu.cartanMatrixIn ℤ i j =
      b.cartanMatrixIn ℤ (su i) (su j) := by
    rw [RootPairing.Base.cartanMatrixIn_def,
      RootPairing.Base.cartanMatrixIn_def]
    apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℝ)))
    change algebraMap ℤ ℝ (P.pairingIn ℤ i j) =
      algebraMap ℤ ℝ ((typeCRootPairing m).pairingIn ℤ (su i) (su j))
    rw [P.algebraMap_pairingIn, (typeCRootPairing m).algebraMap_pairingIn]
    exact (e.pairing_eq i j).symm
  rw [hcartan]
  exact hs (su i) (su j)

private theorem typeCRootPairingULift_hasDynkinType_zero :
    HasDynkinType
      (typeCRootPairingULift 0 :
        RootPairing (SymplecticRootIndex.{u} 0) ℝ
          (TypeCRootSpaceULift.{u} 0)
          (TypeCCorootSpaceULift.{u} 0)) ⟨.C, 0⟩ := by
  let b :
      (typeCRootPairingULift 0 :
        RootPairing (SymplecticRootIndex.{u} 0) ℝ
          (TypeCRootSpaceULift.{u} 0)
          (TypeCCorootSpaceULift.{u} 0)).Base :=
    typeCRootPairingULiftBase 0
  letI : IsEmpty b.support := ⟨fun r => by
    rcases r.1.down with r | r
    · exact Fin.elim0 r.1.1.1
    · exact Fin.elim0 r.1⟩
  refine ⟨b, Equiv.equivOfIsEmpty b.support (Fin 0), ?_⟩
  intro i
  exact isEmptyElim i

/-- The lifted coordinate pairing has type `C_m` in every rank. -/
theorem typeCRootPairingULift_hasDynkinType (m : ℕ) :
    HasDynkinType
      (typeCRootPairingULift m :
        RootPairing (SymplecticRootIndex.{u} m) ℝ
          (TypeCRootSpaceULift.{u} m)
          (TypeCCorootSpaceULift.{u} m)) ⟨.C, m⟩ := by
  rcases m with _ | m
  · exact typeCRootPairingULift_hasDynkinType_zero
  · exact typeCRootPairingULift_hasDynkinType_of_pos
      (m + 1) (by omega)

/-- The exhaustive symplectic root datum realizes the lifted based pairing. -/
theorem symplecticRootData_isActualBasedRootPairingULift (m : ℕ) :
    IsActualBasedRootPairing
      (symplecticRootData (k := k) m)
      (typeCRootPairingULift m :
        RootPairing (SymplecticRootIndex.{u} m) ℝ
          (TypeCRootSpaceULift.{u} m)
          (TypeCCorootSpaceULift.{u} m))
      (typeCRootPairingULiftBase m)
      (Equiv.refl (SymplecticRootIndex.{u} m)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r s
    change (symplecticRootPairingInt m r.down s.down : ℝ) = _
    rw [symplecticRootPairingInt_cast]
    rfl
  · intro r s
    rfl
  · intro r
    change ULift.up (symplecticRootNeg m r.down) = _
    apply ULift.ext
    rw [symplecticRootNeg_eq_seed_neg]
    rfl
  · intro r
    change r.down ∈ (symplecticSeed m).base.support ↔
      r ∈ (typeCRootPairingULiftBase m).support
    have hmem := RootPairing.Base.mem_mapEquiv_support
      (RootPairing.Equiv.symm _ _ (typeCRootPairingULiftEquiv m))
      (symplecticSeed m).base r
    have heq :
        (RootPairing.Equiv.symm _ _
          (typeCRootPairingULiftEquiv m)).indexEquiv.symm r = r.down := rfl
    rw [heq] at hmem
    change r ∈ (typeCRootPairingULiftBase m).support ↔
      r.down ∈ (symplecticSeed m).base.support at hmem
    exact hmem.symm

/-- The standard symplectic carrier with its explicit maximal-torus root model. -/
noncomputable def standardSymplecticCarrierRootSystemModel (m : ℕ) :
    RootSystemModel
      (typeCRootPairingULift m :
        RootPairing (SymplecticRootIndex.{u} m) ℝ
          (TypeCRootSpaceULift.{u} m)
          (TypeCCorootSpaceULift.{u} m))
      (standardSymplecticClosedSubgroup (k := k) m).carrierVariety where
  torus := symplecticDiagonalTorus (k := k) m
  maximalTorus := symplecticDiagonalTorus_isMaximalTorus (k := k) m
  rootData := symplecticRootData (k := k) m
  realization := symplecticRootData_isRealization (k := k) m
  base := typeCRootPairingULiftBase m
  rootEquiv := Equiv.refl (SymplecticRootIndex.{u} m)
  actual := symplecticRootData_isActualBasedRootPairingULift (k := k) m

/-- The semisimple standard symplectic carrier as a type-C version. -/
noncomputable def standardSymplecticCarrierVersion (m : ℕ) :
    SemisimpleVersion (k := k)
      (typeCRootPairingULift m :
        RootPairing (SymplecticRootIndex.{u} m) ℝ
          (TypeCRootSpaceULift.{u} m)
          (TypeCCorootSpaceULift.{u} m)) where
  carrier :=
    (standardSymplecticClosedSubgroup (k := k) m).carrierVariety
  group :=
    (standardSymplecticClosedSubgroup (k := k) m).carrierAlgebraicGroup
  semisimple := standardSymplecticClosedSubgroup_isSemisimple (k := k) m
  rootModel := standardSymplecticCarrierRootSystemModel (k := k) m

/-- The standard symplectic carrier has root-system type `C_m` in every rank. -/
theorem standardSymplecticCarrier_hasRootSystemType (m : ℕ) :
    HasRootSystemType
      (standardSymplecticClosedSubgroup (k := k) m).carrierVariety
      ⟨.C, m⟩ :=
  HasRootSystemType.of_rootSystemModel ⟨.C, m⟩
    (typeCRootPairingULift m :
      RootPairing (SymplecticRootIndex.{u} m) ℝ
        (TypeCRootSpaceULift.{u} m)
        (TypeCCorootSpaceULift.{u} m))
    (standardSymplecticCarrierRootSystemModel (k := k) m)
    (typeCRootPairingULift_hasDynkinType m)

/-- A linked standard symplectic carrier/root model and its projective quotient.

The `SymplecticModel` fields record the quotient isogeny, its central kernel,
the quotient universal property, and the point-group quotient equivalence.
The remaining fields identify the source with the explicit type-C root model
and record direct semisimplicity for both source and target. -/
structure StandardSymplecticRootModel (m : ℕ) where
  model : SymplecticModel (standardSymplecticBilinForm (k := k) m)
  symplectic_eq : model.symplectic =
    standardSymplecticClosedSubgroup (k := k) m
  carrierRootModel : RootSystemModel
    (typeCRootPairingULift m :
      RootPairing (SymplecticRootIndex.{u} m) ℝ
        (TypeCRootSpaceULift.{u} m)
        (TypeCCorootSpaceULift.{u} m))
    (standardSymplecticClosedSubgroup (k := k) m).carrierVariety
  carrierSemisimple : IsSemisimpleAlgebraicGroup
    (standardSymplecticClosedSubgroup (k := k) m).carrierVariety
  dynkinType : HasDynkinType
    (typeCRootPairingULift m :
      RootPairing (SymplecticRootIndex.{u} m) ℝ
        (TypeCRootSpaceULift.{u} m)
        (TypeCCorootSpaceULift.{u} m)) ⟨.C, m⟩
  projectiveSemisimple : letI := model.projectiveSymplecticAlgebraicGroup
    IsSemisimpleAlgebraicGroup model.projectiveSymplectic

/-- The direct standard symplectic type-C root model exists in every rank. -/
theorem exists_standard_symplectic_root_model (m : ℕ) :
    Nonempty (StandardSymplecticRootModel (k := k) m) := by
  let S := standardSymplecticClosedSubgroup (k := k) m
  letI : AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup
  let B := standardSymplecticBilinForm (k := k) m
  obtain ⟨Q, hQ, q, hqiso, hqker, hfactor, ⟨eQ, heQ⟩⟩ :=
    standardSymplecticQuotient_exists (k := k) m
  letI : AlgebraicGroup Q := hQ
  let eS : Variety.Point S.carrierVariety ≃* bilinearIsometrySubgroup B :=
    standardSymplecticClosedSubgroupPoints (k := k) m
  let M : SymplecticModel (standardSymplecticBilinForm (k := k) m) := {
    basis := symplecticStandardBasis (k := k) m
    symplectic := S
    symplectic_carrier := fun g => standardSymplecticClosedSubgroup_carrier m g
    projectiveSymplectic := Q
    projectiveSymplecticAlgebraicGroup := hQ
    symplecticPoints := eS
    symplecticLinear_points := by
      intro x
      exact standardSymplecticClosedSubgroup_linear_points (k := k) m x
    quotient := q
    quotientIsogeny := hqiso
    quotientKernel := hqker
    quotientUniversal := hfactor
    projectiveSymplecticPoints := eQ
    projectiveSymplecticQuotient := heQ
  }
  refine ⟨{
    model := M
    symplectic_eq := rfl
    carrierRootModel :=
      standardSymplecticCarrierRootSystemModel (k := k) m
    carrierSemisimple :=
      standardSymplecticClosedSubgroup_isSemisimple (k := k) m
    dynkinType := typeCRootPairingULift_hasDynkinType m
    projectiveSemisimple := ?_
  }⟩
  exact standardSymplectic_isogenyTarget_isSemisimple (k := k) m q hqiso

end

end

end Theory.AlgebraicGroup
