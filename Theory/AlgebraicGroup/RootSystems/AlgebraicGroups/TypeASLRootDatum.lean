module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.TypeASLTorusRootClassification
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.RootSystemType
public import Theory.AlgebraicGroup.RootSystems.Weyl

/-!
# The type-A root datum of the special linear group

This module identifies the explicit diagonal-torus root realization of
`SL_(m+1)` with the standard type-`A_m` root pairing.  The geometric input is
the determinant-one diagonal maximal torus, its elementary matrix root
subgroups, and the exhaustive torus-root classification proved in the
preceding modules.  The comparison sends an ordered pair of distinct matrix
coordinates to the corresponding standard type-A root; the reflection,
negation, and simple-root assertions then reduce to coordinate calculations.

`RootSystemModel` stores its linear spaces in the universe of the ground
field.  We therefore also construct a universe-lifted copy of the standard
pairing, prove it is a finite reduced crystallographic root system, and
transport the standard adjacent-root base to it.  This technical lift is
explicitly equivalent to `StandardRootSystem.typeARootPairing`; the actual
root datum is separately identified with that standard pairing itself.  The
resulting model yields `HasRootSystemType` directly from the concrete SL
geometry, without any isogeny-classification or version theorem.
-/

open Set

namespace Theory.AlgebraicGroup

open StandardRootSystem

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

public section

noncomputable section

/-- The explicit SL root datum, indexed by ordered pairs of distinct diagonal
coordinates, is the standard based type-A root pairing. -/
public theorem typeASLRootData_isActualBasedRootPairing (m : ℕ) :
    IsActualBasedRootPairing
      (typeASLTorusRootData (k := k) m)
      (typeARootPairing m)
      (typeARootPairing_base m)
      (typeASLTorusRootIndexEquiv m) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α β
    exact typeASLTorusRootData_pairing_cast (k := k) m α β
  · intro α β
    apply (typeARootPairing m).root.injective
    rw [(typeARootPairing m).root_reflectionPerm]
    change typeARootInSpan m (typeASLRootReflect m α.down β.down) =
      (typeARootPairing m).reflection α.down
        ((typeARootPairing m).root β.down)
    rw [(typeARootPairing m).reflection_apply_root,
      typeARootPairing_pairing]
    apply Subtype.ext
    simpa [typeASLRootReflect, typeARootEmbedding_apply, dot_comm] using
      (typeARoot_reflection_eq_swap
        α.down.1.1 α.down.1.2 β.down.1.1 β.down.1.2 α.down.2).symm
  · intro α
    apply (typeARootPairing m).root.injective
    rw [(typeARootPairing m).root_reflectionPerm,
      (typeARootPairing m).reflection_apply_self]
    change typeARootInSpan m (typeASLRootNeg m α.down) =
      -typeARootInSpan m α.down
    apply Subtype.ext
    change basisVector α.down.1.2 - basisVector α.down.1.1 =
      -(basisVector α.down.1.1 - basisVector α.down.1.2)
    module
  · change ∀ α : TypeASLTorusRoot.{u} m,
      α ∈ typeASLTorusSimpleRoots m ↔
      typeASLTorusRootIndexEquiv m α ∈
        (typeARootPairing_base m).support
    intro α
    change (∃ i : Fin m, (⟨typeASimpleRootIndex m i⟩ :
      TypeASLTorusRoot.{u} m) = α) ↔
      α.down ∈ (typeARootPairing_base m).support
    rw [show α.down ∈ (typeARootPairing_base m).support ↔
        α.down ∈ Set.range (typeASimpleRootIndex m) by
      exact Set.ext_iff.mp (typeARootPairing_base_support m) α.down]
    simp only [Set.mem_range]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply ULift.ext
      exact hi

/-- A universe-lifted index type for the standard type-A roots. -/
public abbrev TypeARootIndexULift (m : ℕ) :=
  ULift.{u, 0} (TypeARootIndex m)

/-- A universe-lifted copy of the standard type-A root space. -/
public abbrev TypeARootSpaceULift (m : ℕ) :=
  ULift.{u, 0} (typeARootSpan m)

/-- A universe-lifted copy of the standard type-A coroot space. -/
public abbrev TypeACorootSpaceULift (m : ℕ) :=
  ULift.{u, 0} (Module.Dual ℝ (typeARootSpan m))

/-- The standard type-A pairing lifted into an arbitrary universe. -/
public noncomputable def typeARootPairingULift (m : ℕ) :
    RootPairing (TypeARootIndexULift.{u} m) ℝ
      (TypeARootSpaceULift.{u} m) (TypeACorootSpaceULift.{u} m) := by
  let P := typeARootPairing m
  let p := P.toLinearMap.compl₁₂
    (ULift.moduleEquiv : TypeARootSpaceULift.{u} m ≃ₗ[ℝ]
      typeARootSpan m).toLinearMap
    (ULift.moduleEquiv : TypeACorootSpaceULift.{u} m ≃ₗ[ℝ]
      Module.Dual ℝ (typeARootSpan m)).toLinearMap
  let root : TypeARootIndexULift.{u} m ↪ TypeARootSpaceULift.{u} m :=
    ⟨fun i => ⟨P.root i.down⟩, by
      intro i j h
      apply ULift.ext
      apply P.root.injective
      exact congrArg ULift.down h⟩
  let coroot : TypeARootIndexULift.{u} m ↪
      TypeACorootSpaceULift.{u} m :=
    ⟨fun i => ⟨P.coroot i.down⟩, by
      intro i j h
      apply ULift.ext
      apply P.coroot.injective
      exact congrArg ULift.down h⟩
  let reflect (i : TypeARootIndexULift.{u} m) :
      TypeARootIndexULift.{u} m ≃ TypeARootIndexULift.{u} m :=
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

/-- Forgetting the universe lift identifies the lifted pairing with the
standard type-A pairing. -/
public noncomputable def typeARootPairingULiftEquiv (m : ℕ) :
    RootPairing.Equiv
      (typeARootPairingULift m :
        RootPairing (TypeARootIndexULift.{u} m) ℝ
          (TypeARootSpaceULift.{u} m) (TypeACorootSpaceULift.{u} m))
      (typeARootPairing m) where
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

public noncomputable instance (m : ℕ) :
    (typeARootPairingULift m :
      RootPairing (TypeARootIndexULift.{u} m) ℝ
        (TypeARootSpaceULift.{u} m)
        (TypeACorootSpaceULift.{u} m)).IsRootSystem where
  span_root_eq_top := by
    change Submodule.span ℝ (Set.range
      (fun i : TypeARootIndexULift.{u} m =>
        (⟨(typeARootPairing m).root i.down⟩ :
          TypeARootSpaceULift.{u} m))) = ⊤
    let e : TypeARootSpaceULift.{u} m ≃ₗ[ℝ] typeARootSpan m :=
      ULift.moduleEquiv
    apply Submodule.map_injective_of_injective e.injective
    rw [Submodule.map_span]
    have himage : e.toLinearMap '' Set.range
        (fun i : TypeARootIndexULift.{u} m =>
          (⟨(typeARootPairing m).root i.down⟩ :
            TypeARootSpaceULift.{u} m)) =
        Set.range (typeARootPairing m).root := by
      ext y
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i.down, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨⟨(typeARootPairing m).root i⟩, ⟨⟨i⟩, rfl⟩, rfl⟩
    rw [himage, RootPairing.IsRootSystem.span_root_eq_top,
      Submodule.map_top]
    exact (LinearMap.range_eq_top.mpr e.surjective).symm
  span_coroot_eq_top := by
    change Submodule.span ℝ (Set.range
      (fun i : TypeARootIndexULift.{u} m =>
        (⟨(typeARootPairing m).coroot i.down⟩ :
          TypeACorootSpaceULift.{u} m))) = ⊤
    let e : TypeACorootSpaceULift.{u} m ≃ₗ[ℝ]
        Module.Dual ℝ (typeARootSpan m) := ULift.moduleEquiv
    apply Submodule.map_injective_of_injective e.injective
    rw [Submodule.map_span]
    have himage : e.toLinearMap '' Set.range
        (fun i : TypeARootIndexULift.{u} m =>
          (⟨(typeARootPairing m).coroot i.down⟩ :
            TypeACorootSpaceULift.{u} m)) =
        Set.range (typeARootPairing m).coroot := by
      ext y
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i.down, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨⟨(typeARootPairing m).coroot i⟩, ⟨⟨i⟩, rfl⟩, rfl⟩
    rw [himage, RootPairing.IsRootSystem.span_coroot_eq_top,
      Submodule.map_top]
    exact (LinearMap.range_eq_top.mpr e.surjective).symm

public noncomputable instance (m : ℕ) :
    (typeARootPairingULift m :
      RootPairing (TypeARootIndexULift.{u} m) ℝ
        (TypeARootSpaceULift.{u} m)
        (TypeACorootSpaceULift.{u} m)).IsCrystallographic where
  exists_value i j := by
    change ∃ z : ℤ, (z : ℝ) =
      (typeARootPairing m).pairing i.down j.down
    exact (typeARootPairing m).exists_value (S := ℤ) i.down j.down

public noncomputable instance (m : ℕ) :
    (typeARootPairingULift m :
      RootPairing (TypeARootIndexULift.{u} m) ℝ
        (TypeARootSpaceULift.{u} m)
        (TypeACorootSpaceULift.{u} m)).IsReduced where
  eq_or_eq_neg i j h := by
    change ¬ LinearIndependent ℝ
      ![(⟨(typeARootPairing m).root i.down⟩ :
          TypeARootSpaceULift.{u} m),
        (⟨(typeARootPairing m).root j.down⟩ :
          TypeARootSpaceULift.{u} m)] at h
    have hdown : ¬ LinearIndependent ℝ
        ![(typeARootPairing m).root i.down,
          (typeARootPairing m).root j.down] := by
      intro hli
      apply h
      have hmapped := hli.map'
        (ULift.moduleEquiv.symm : typeARootSpan m ≃ₗ[ℝ]
          TypeARootSpaceULift.{u} m).toLinearMap
        (LinearMap.ker_eq_bot.mpr
          (ULift.moduleEquiv.symm : typeARootSpan m ≃ₗ[ℝ]
            TypeARootSpaceULift.{u} m).injective)
      have hvectors :
          (![(⟨(typeARootPairing m).root i.down⟩ :
                TypeARootSpaceULift.{u} m),
            (⟨(typeARootPairing m).root j.down⟩ :
                TypeARootSpaceULift.{u} m)] :
              Fin 2 → TypeARootSpaceULift.{u} m) =
            (ULift.moduleEquiv.symm : typeARootSpan m ≃ₗ[ℝ]
              TypeARootSpaceULift.{u} m) ∘
              ![(typeARootPairing m).root i.down,
                (typeARootPairing m).root j.down] := by
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

private lemma typeACartanMatrix_eq_dynkinCartanEntry_A
    (m : ℕ) (i j : Fin m) :
    typeACartanMatrix m i j = dynkinCartanEntry ⟨.A, m⟩ i j := by
  by_cases hij : i = j
  · subst j
    simp [typeACartanMatrix, dynkinCartanEntry]
  · by_cases hforward : i.succ = j.castSucc
    · have hval : i.val + 1 = j.val := by
        simpa using congrArg Fin.val hforward
      simp [typeACartanMatrix, dynkinCartanEntry, hij, hforward, hval]
    · by_cases hreverse : j.succ = i.castSucc
      · have hval : j.val + 1 = i.val := by
          simpa using congrArg Fin.val hreverse
        simp [typeACartanMatrix, dynkinCartanEntry, hij, hforward,
          hreverse, hval]
      · have hforwardVal : i.val + 1 ≠ j.val := by
          intro h
          exact hforward (Fin.ext (by simpa using h))
        have hreverseVal : j.val + 1 ≠ i.val := by
          intro h
          exact hreverse (Fin.ext (by simpa using h))
        simp [typeACartanMatrix, dynkinCartanEntry, hij, hforward,
          hreverse, hforwardVal, hreverseVal]

/-- The standard type-A pairing has Dynkin classification `A_m`. -/
public theorem typeARootPairing_hasDynkinType (m : ℕ) :
    HasDynkinType (typeARootPairing m) ⟨.A, m⟩ := by
  refine ⟨typeARootPairing_base m,
    (typeARootPairing_baseEquiv m).symm, ?_⟩
  intro i j
  change (typeARootPairing_base m).cartanMatrix i j = _
  have h := typeARootPairing_base_cartanMatrix m
    ((typeARootPairing_baseEquiv m).symm i)
    ((typeARootPairing_baseEquiv m).symm j)
  have h' : (typeARootPairing_base m).cartanMatrix i j =
      typeACartanMatrix m
        ((typeARootPairing_baseEquiv m).symm i)
        ((typeARootPairing_baseEquiv m).symm j) := by
    simpa using h
  rw [h']
  exact typeACartanMatrix_eq_dynkinCartanEntry_A m _ _

/-- The adjacent-root base transported to the universe-lifted pairing. -/
public noncomputable def typeARootPairingULiftBase (m : ℕ) :
    (typeARootPairingULift m :
      RootPairing (TypeARootIndexULift.{u} m) ℝ
        (TypeARootSpaceULift.{u} m)
        (TypeACorootSpaceULift.{u} m)).Base :=
  RootPairing.Base.mapEquiv
    (RootPairing.Equiv.symm _ _ (typeARootPairingULiftEquiv m))
    (typeARootPairing_base m)

noncomputable def typeARootPairingULiftSupportEquiv (m : ℕ) :
    (typeARootPairingULiftBase m).support ≃
      (typeARootPairing_base m).support :=
  Equiv.subtypeEquiv (typeARootPairingULiftEquiv m).indexEquiv (fun i => by
    change i ∈ (typeARootPairingULiftBase m).support ↔
      (typeARootPairingULiftEquiv m).indexEquiv i ∈
        (typeARootPairing_base m).support
    rw [show typeARootPairingULiftBase m = RootPairing.Base.mapEquiv
        (RootPairing.Equiv.symm _ _ (typeARootPairingULiftEquiv m))
        (typeARootPairing_base m) by rfl]
    rw [RootPairing.Base.mem_mapEquiv_support]
    simp)

/-- The universe-lifted standard pairing retains Dynkin classification
`A_m`. -/
public theorem typeARootPairingULift_hasDynkinType (m : ℕ) :
    HasDynkinType
      (typeARootPairingULift m :
        RootPairing (TypeARootIndexULift.{u} m) ℝ
          (TypeARootSpaceULift.{u} m)
          (TypeACorootSpaceULift.{u} m)) ⟨.A, m⟩ := by
  let P : RootPairing (TypeARootIndexULift.{u} m) ℝ
      (TypeARootSpaceULift.{u} m) (TypeACorootSpaceULift.{u} m) :=
    typeARootPairingULift m
  let e := typeARootPairingULiftEquiv m
  let b := typeARootPairingULiftBase m
  let s := typeARootPairingULiftSupportEquiv m
  refine ⟨b, s.trans (typeARootPairing_baseEquiv m).symm, ?_⟩
  intro i j
  have hcartan : b.cartanMatrixIn ℤ i j =
      (typeARootPairing_base m).cartanMatrixIn ℤ (s i) (s j) := by
    rw [RootPairing.Base.cartanMatrixIn_def,
      RootPairing.Base.cartanMatrixIn_def]
    apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℝ)))
    change algebraMap ℤ ℝ ((typeARootPairingULift m).pairingIn ℤ i j) =
      algebraMap ℤ ℝ ((typeARootPairing m).pairingIn ℤ (s i) (s j))
    rw [(typeARootPairingULift m).algebraMap_pairingIn,
      (typeARootPairing m).algebraMap_pairingIn]
    change P.pairing i j =
      (typeARootPairing m).pairing (s i) (s j)
    exact (e.pairing_eq i j).symm
  rw [hcartan]
  change (typeARootPairing_base m).cartanMatrix (s i) (s j) = _
  have h := typeARootPairing_base_cartanMatrix m
    ((typeARootPairing_baseEquiv m).symm (s i))
    ((typeARootPairing_baseEquiv m).symm (s j))
  have h' : (typeARootPairing_base m).cartanMatrix (s i) (s j) =
      typeACartanMatrix m
        ((typeARootPairing_baseEquiv m).symm (s i))
        ((typeARootPairing_baseEquiv m).symm (s j)) := by
    simpa using h
  rw [h']
  exact typeACartanMatrix_eq_dynkinCartanEntry_A m _ _

/-- The concrete SL root datum also realizes the universe-lifted standard
pairing, with the identity equivalence on its already-lifted root index. -/
public theorem typeASLRootData_isActualBasedRootPairingULift (m : ℕ) :
    IsActualBasedRootPairing
      (typeASLTorusRootData (k := k) m)
      (typeARootPairingULift m :
        RootPairing (TypeARootIndexULift.{u} m) ℝ
          (TypeARootSpaceULift.{u} m)
          (TypeACorootSpaceULift.{u} m))
      (typeARootPairingULiftBase m)
      (Equiv.refl (TypeASLTorusRoot.{u} m)) := by
  let P : RootPairing (TypeARootIndexULift.{u} m) ℝ
      (TypeARootSpaceULift.{u} m) (TypeACorootSpaceULift.{u} m) :=
    typeARootPairingULift m
  let e := typeARootPairingULiftEquiv m
  have hstandard := typeASLRootData_isActualBasedRootPairing (k := k) m
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α β
    rw [hstandard.1 α β]
    exact e.pairing_eq α β
  · intro α β
    apply ULift.ext
    change typeASLTorusRootIndexEquiv m
        ((typeASLTorusRootData (k := k) m).reflect α β) =
      (typeARootPairing m).reflectionPerm
        (typeASLTorusRootIndexEquiv m α)
        (typeASLTorusRootIndexEquiv m β)
    exact hstandard.2.1 α β
  · intro α
    apply ULift.ext
    change typeASLTorusRootIndexEquiv m
        ((typeASLTorusRootData (k := k) m).neg α) =
      (typeARootPairing m).reflectionPerm
        (typeASLTorusRootIndexEquiv m α)
        (typeASLTorusRootIndexEquiv m α)
    exact hstandard.2.2.1 α
  · intro α
    rw [hstandard.2.2.2 α]
    have hmem := RootPairing.Base.mem_mapEquiv_support
      (RootPairing.Equiv.symm _ _ (typeARootPairingULiftEquiv m))
      (typeARootPairing_base m)
      (show TypeARootIndexULift.{u} m from α)
    change α ∈ (typeARootPairingULiftBase m).support ↔
      typeASLTorusRootIndexEquiv m α ∈
        (typeARootPairing_base m).support at hmem
    exact hmem.symm

/-- The explicit maximal torus and root subgroups form a type-A root-system
model for `SL_(m+1)`. -/
public noncomputable def typeASLRootSystemModel (m : ℕ) :
    RootSystemModel
      (typeARootPairingULift m :
        RootPairing (TypeARootIndexULift.{u} m) ℝ
          (TypeARootSpaceULift.{u} m)
          (TypeACorootSpaceULift.{u} m))
      (slVariety k (m + 1)) where
  torus := typeASLTorus (k := k) m
  maximalTorus := typeASLDiagonalTorus_isMaximalTorus (k := k) m
  rootData := typeASLTorusRootData (k := k) m
  realization := typeASLTorusRootData_isRealization (k := k) m
  base := typeARootPairingULiftBase m
  rootEquiv := Equiv.refl (TypeASLTorusRoot.{u} m)
  actual := typeASLRootData_isActualBasedRootPairingULift (k := k) m

/-- The special linear group `SL_(m+1)` has root-system type `A_m`. -/
public theorem slVariety_hasRootSystemType_typeA (m : ℕ) :
    HasRootSystemType (slVariety k (m + 1)) ⟨.A, m⟩ := by
  exact HasRootSystemType.of_rootSystemModel ⟨.A, m⟩
    (typeARootPairingULift m :
      RootPairing (TypeARootIndexULift.{u} m) ℝ
        (TypeARootSpaceULift.{u} m)
        (TypeACorootSpaceULift.{u} m))
    (typeASLRootSystemModel (k := k) m)
    (typeARootPairingULift_hasDynkinType m)

end

end

end Theory.AlgebraicGroup
