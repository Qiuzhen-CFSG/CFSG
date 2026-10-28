module

public import Theory.AlgebraicGroup.RootSystems.F4RootPairing
public import Theory.AlgebraicGroup.RootSystems.Weyl

/-!
# Universe lift of the standard F4 root pairing

This module lifts the finite root index and both real coordinate spaces of the
canonical F4 pairing into an arbitrary universe. The lifted pairing is explicitly
equivalent to the standard coordinate pairing, so the integral, reduced root-system
structure and the displayed base can be transported without classification.

The source data are the direct coordinate construction and displayed Bourbaki base in
F4RootPairing.lean. Pointwise lifting of roots, coroots, and reflections supplies the
pairing; linear equivalences prove spanning and preserve two-root dependence. The
result places the pairing data in the ground-field universe required by RootSystemModel
while retaining the standard Fin 4 support and Cartan matrix.
-/

namespace Theory.AlgebraicGroup.StandardRootSystem

universe u

public section

noncomputable section

/-- The standard F4 root index lifted into an arbitrary universe. -/
public abbrev TypeF4RootIndexULift :=
  ULift.{u, 0} typeF4Roots

/-- The standard F4 root space lifted into an arbitrary universe. -/
public abbrev TypeF4RootSpaceULift :=
  ULift.{u, 0} (Vec 4)

/-- The standard F4 coroot space lifted into an arbitrary universe. -/
public abbrev TypeF4CorootSpaceULift :=
  ULift.{u, 0} (Vec 4)

/-- The lifted root index remains finite. -/
public instance typeF4RootIndexULift_finite :
    Finite (TypeF4RootIndexULift.{u}) :=
  inferInstance

/-- The canonical F4 pairing lifted into an arbitrary universe. -/
public noncomputable def typeF4RootPairingULift :
    RootPairing (TypeF4RootIndexULift.{u}) ℝ
      (TypeF4RootSpaceULift.{u}) (TypeF4CorootSpaceULift.{u}) := by
  let P := typeF4RootPairing
  let p := P.toLinearMap.compl₁₂
    (ULift.moduleEquiv : TypeF4RootSpaceULift.{u} ≃ₗ[ℝ] Vec 4).toLinearMap
    (ULift.moduleEquiv : TypeF4CorootSpaceULift.{u} ≃ₗ[ℝ] Vec 4).toLinearMap
  let root : TypeF4RootIndexULift.{u} ↪ TypeF4RootSpaceULift.{u} :=
    ⟨fun i => ⟨P.root i.down⟩, by
      intro i j h
      apply ULift.ext
      apply P.root.injective
      exact congrArg ULift.down h⟩
  let coroot : TypeF4RootIndexULift.{u} ↪ TypeF4CorootSpaceULift.{u} :=
    ⟨fun i => ⟨P.coroot i.down⟩, by
      intro i j h
      apply ULift.ext
      apply P.coroot.injective
      exact congrArg ULift.down h⟩
  let reflect (i : TypeF4RootIndexULift.{u}) :
      TypeF4RootIndexULift.{u} ≃ TypeF4RootIndexULift.{u} :=
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

/-- Forgetting the universe lift recovers the canonical F4 pairing. -/
public noncomputable def typeF4RootPairingULiftEquiv :
    RootPairing.Equiv
      (typeF4RootPairingULift :
        RootPairing (TypeF4RootIndexULift.{u}) ℝ
          (TypeF4RootSpaceULift.{u}) (TypeF4CorootSpaceULift.{u}))
      typeF4RootPairing where
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

/-- The universe lift retains both root and coroot spanning properties. -/
public noncomputable instance typeF4RootPairingULift_isRootSystem :
    (typeF4RootPairingULift :
      RootPairing (TypeF4RootIndexULift.{u}) ℝ
        (TypeF4RootSpaceULift.{u}) (TypeF4CorootSpaceULift.{u})).IsRootSystem where
  span_root_eq_top := by
    change Submodule.span ℝ (Set.range
      (fun i : TypeF4RootIndexULift.{u} =>
        (⟨typeF4RootPairing.root i.down⟩ : TypeF4RootSpaceULift.{u}))) = ⊤
    let e : TypeF4RootSpaceULift.{u} ≃ₗ[ℝ] Vec 4 := ULift.moduleEquiv
    apply Submodule.map_injective_of_injective e.injective
    rw [Submodule.map_span]
    have himage : e.toLinearMap '' Set.range
        (fun i : TypeF4RootIndexULift.{u} =>
          (⟨typeF4RootPairing.root i.down⟩ : TypeF4RootSpaceULift.{u})) =
        Set.range typeF4RootPairing.root := by
      ext y
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i.down, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨⟨typeF4RootPairing.root i⟩, ⟨⟨i⟩, rfl⟩, rfl⟩
    rw [himage, RootPairing.IsRootSystem.span_root_eq_top,
      Submodule.map_top]
    exact (LinearMap.range_eq_top.mpr e.surjective).symm
  span_coroot_eq_top := by
    change Submodule.span ℝ (Set.range
      (fun i : TypeF4RootIndexULift.{u} =>
        (⟨typeF4RootPairing.coroot i.down⟩ : TypeF4CorootSpaceULift.{u}))) = ⊤
    let e : TypeF4CorootSpaceULift.{u} ≃ₗ[ℝ] Vec 4 := ULift.moduleEquiv
    apply Submodule.map_injective_of_injective e.injective
    rw [Submodule.map_span]
    have himage : e.toLinearMap '' Set.range
        (fun i : TypeF4RootIndexULift.{u} =>
          (⟨typeF4RootPairing.coroot i.down⟩ : TypeF4CorootSpaceULift.{u})) =
        Set.range typeF4RootPairing.coroot := by
      ext y
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i.down, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨⟨typeF4RootPairing.coroot i⟩, ⟨⟨i⟩, rfl⟩, rfl⟩
    rw [himage, RootPairing.IsRootSystem.span_coroot_eq_top,
      Submodule.map_top]
    exact (LinearMap.range_eq_top.mpr e.surjective).symm

/-- The universe lift retains the integral Cartan pairing. -/
public noncomputable instance typeF4RootPairingULift_isCrystallographic :
    (typeF4RootPairingULift :
      RootPairing (TypeF4RootIndexULift.{u}) ℝ
        (TypeF4RootSpaceULift.{u})
        (TypeF4CorootSpaceULift.{u})).IsCrystallographic where
  exists_value i j := by
    change ∃ z : ℤ, (z : ℝ) = typeF4RootPairing.pairing i.down j.down
    exact typeF4RootPairing.exists_value (S := ℤ) i.down j.down

/-- The universe lift retains reducedness. -/
public noncomputable instance typeF4RootPairingULift_isReduced :
    (typeF4RootPairingULift :
      RootPairing (TypeF4RootIndexULift.{u}) ℝ
        (TypeF4RootSpaceULift.{u}) (TypeF4CorootSpaceULift.{u})).IsReduced where
  eq_or_eq_neg i j h := by
    change ¬ LinearIndependent ℝ
      ![(⟨typeF4RootPairing.root i.down⟩ : TypeF4RootSpaceULift.{u}),
        (⟨typeF4RootPairing.root j.down⟩ : TypeF4RootSpaceULift.{u})] at h
    have hdown : ¬ LinearIndependent ℝ
        ![typeF4RootPairing.root i.down, typeF4RootPairing.root j.down] := by
      intro hli
      apply h
      have hmapped := hli.map'
        (ULift.moduleEquiv.symm : Vec 4 ≃ₗ[ℝ] TypeF4RootSpaceULift.{u}).toLinearMap
        (LinearMap.ker_eq_bot.mpr
          (ULift.moduleEquiv.symm : Vec 4 ≃ₗ[ℝ]
            TypeF4RootSpaceULift.{u}).injective)
      have hvectors :
          (![(⟨typeF4RootPairing.root i.down⟩ : TypeF4RootSpaceULift.{u}),
            (⟨typeF4RootPairing.root j.down⟩ : TypeF4RootSpaceULift.{u})] :
              Fin 2 → TypeF4RootSpaceULift.{u}) =
            (ULift.moduleEquiv.symm : Vec 4 ≃ₗ[ℝ]
              TypeF4RootSpaceULift.{u}) ∘
              ![typeF4RootPairing.root i.down,
                typeF4RootPairing.root j.down] := by
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

/-- The displayed standard base transported to the universe-lifted pairing. -/
public noncomputable def typeF4RootPairingULift_base :
    (typeF4RootPairingULift :
      RootPairing (TypeF4RootIndexULift.{u}) ℝ
        (TypeF4RootSpaceULift.{u}) (TypeF4CorootSpaceULift.{u})).Base :=
  RootPairing.Base.mapEquiv
    (RootPairing.Equiv.symm _ _ typeF4RootPairingULiftEquiv)
    typeF4RootPairing_base

/-- The transported support identified with the support of the standard base. -/
public noncomputable def typeF4RootPairingULift_supportEquiv :
    typeF4RootPairingULift_base.support ≃ typeF4RootPairing_base.support :=
  Equiv.subtypeEquiv typeF4RootPairingULiftEquiv.indexEquiv (fun i => by
    change i ∈ typeF4RootPairingULift_base.support ↔
      typeF4RootPairingULiftEquiv.indexEquiv i ∈ typeF4RootPairing_base.support
    rw [show typeF4RootPairingULift_base = RootPairing.Base.mapEquiv
        (RootPairing.Equiv.symm _ _ typeF4RootPairingULiftEquiv)
        typeF4RootPairing_base by rfl]
    rw [RootPairing.Base.mem_mapEquiv_support]
    simp)

/-- The four displayed simple roots identify Fin 4 with the lifted base support. -/
public noncomputable def typeF4RootPairingULift_baseEquiv :
    Fin 4 ≃ typeF4RootPairingULift_base.support :=
  typeF4RootPairing_baseEquiv.trans typeF4RootPairingULift_supportEquiv.symm

private lemma typeF4RootPairingULift_cartan_supportEquiv
    (i j : typeF4RootPairingULift_base.support) :
    typeF4RootPairingULift_base.cartanMatrixIn ℤ i j =
      typeF4RootPairing_base.cartanMatrixIn ℤ
        (typeF4RootPairingULift_supportEquiv i)
        (typeF4RootPairingULift_supportEquiv j) := by
  rw [RootPairing.Base.cartanMatrixIn_def,
    RootPairing.Base.cartanMatrixIn_def]
  apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℝ)))
  change algebraMap ℤ ℝ (typeF4RootPairingULift.pairingIn ℤ i j) =
    algebraMap ℤ ℝ (typeF4RootPairing.pairingIn ℤ
      (typeF4RootPairingULift_supportEquiv i)
      (typeF4RootPairingULift_supportEquiv j))
  rw [typeF4RootPairingULift.algebraMap_pairingIn,
    typeF4RootPairing.algebraMap_pairingIn]
  exact (typeF4RootPairingULiftEquiv.pairing_eq i j).symm

/-- The lifted base has the standard F4 Cartan entries in displayed order. -/
public lemma typeF4RootPairingULift_base_cartan_apply (i j : Fin 4) :
    typeF4RootPairingULift_base.cartanMatrix
        (typeF4RootPairingULift_baseEquiv i)
        (typeF4RootPairingULift_baseEquiv j) =
      typeF4CartanMatrix i j := by
  change typeF4RootPairingULift_base.cartanMatrixIn ℤ
      (typeF4RootPairingULift_baseEquiv i)
      (typeF4RootPairingULift_baseEquiv j) =
    typeF4CartanMatrix i j
  rw [typeF4RootPairingULift_cartan_supportEquiv]
  simpa [typeF4RootPairingULift_baseEquiv] using
    typeF4RootPairing_base_cartan_apply i j

/-- Reindexing the lifted base by Fin 4 gives the standard F4 Cartan matrix. -/
public theorem typeF4RootPairingULift_base_cartan :
    typeF4RootPairingULift_base.cartanMatrix.reindex
        typeF4RootPairingULift_baseEquiv.symm
        typeF4RootPairingULift_baseEquiv.symm =
      typeF4CartanMatrix := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  exact typeF4RootPairingULift_base_cartan_apply i j

private lemma typeF4RootPairingULift_base_cartan_connected
    (s t : typeF4RootPairingULift_base.support) :
    Relation.ReflTransGen
      (fun u v : typeF4RootPairingULift_base.support =>
        typeF4RootPairingULift_base.cartanMatrix u v ≠ 0) s t := by
  rw [← typeF4RootPairingULift_baseEquiv.apply_symm_apply s,
    ← typeF4RootPairingULift_baseEquiv.apply_symm_apply t]
  exact Relation.ReflTransGen.lift typeF4RootPairingULift_baseEquiv
    (fun i j h => by
      change typeF4RootPairingULift_base.cartanMatrix
        (typeF4RootPairingULift_baseEquiv i)
        (typeF4RootPairingULift_baseEquiv j) ≠ 0
      rw [typeF4RootPairingULift_base_cartan_apply]
      exact h)
    _ _ (typeF4Cartan_connected _ _)

/-- The universe-lifted F4 pairing remains irreducible. -/
public noncomputable instance typeF4RootPairingULift_isIrreducible :
    (typeF4RootPairingULift :
      RootPairing (TypeF4RootIndexULift.{u}) ℝ
        (TypeF4RootSpaceULift.{u})
        (TypeF4CorootSpaceULift.{u})).IsIrreducible :=
  isIrreducible_of_cartan_connected
    (typeF4RootPairingULift :
      RootPairing (TypeF4RootIndexULift.{u}) ℝ
        (TypeF4RootSpaceULift.{u}) (TypeF4CorootSpaceULift.{u}))
    typeF4RootPairingULift_base
    ⟨(typeF4RootPairingULift_baseEquiv 0 : TypeF4RootIndexULift.{u}),
      (typeF4RootPairingULift_baseEquiv 0).property⟩
    typeF4RootPairingULift_base_cartan_connected

end

end

end Theory.AlgebraicGroup.StandardRootSystem
