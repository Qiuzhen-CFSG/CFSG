module

public import Theory.AlgebraicGroup.RootSystems.G2RootPairing
public import Theory.AlgebraicGroup.RootSystems.Weyl

/-!
# Universe lift of the standard G2 root pairing

This module lifts the twelve-root index and both real coordinate planes of the
canonical G2 pairing into an arbitrary universe. The lifted pairing is explicitly
equivalent to the standard coordinate pairing, so its finite, crystallographic,
reduced root-system structure and displayed base transport without classification.

The source data are the direct coordinate construction and displayed short-long base
in G2RootPairing.lean. Pointwise lifting of roots, coroots, and reflections supplies
the pairing; linear equivalences prove spanning and preserve two-root dependence. The
result places the pairing data in the ground-field universe required by RootSystemModel
while retaining the standard Fin 2 support and G2 Cartan matrix.
-/

namespace Theory.AlgebraicGroup.StandardRootSystem

universe u

public section

noncomputable section

/-- The standard G2 root index lifted into an arbitrary universe. -/
public abbrev TypeG2RootIndexULift :=
  ULift.{u, 0} typeG2Root

/-- The standard G2 root space lifted into an arbitrary universe. -/
public abbrev TypeG2RootSpaceULift :=
  ULift.{u, 0} (Vec 2)

/-- The standard G2 coroot space lifted into an arbitrary universe. -/
public abbrev TypeG2CorootSpaceULift :=
  ULift.{u, 0} (Vec 2)

/-- The lifted root index remains finite. -/
public instance typeG2RootIndexULift_finite :
    Finite (TypeG2RootIndexULift.{u}) :=
  inferInstance

/-- The canonical G2 pairing lifted into an arbitrary universe. -/
public noncomputable def typeG2RootPairingULift :
    RootPairing (TypeG2RootIndexULift.{u}) ℝ
      (TypeG2RootSpaceULift.{u}) (TypeG2CorootSpaceULift.{u}) := by
  let P := typeG2RootPairing
  let p := P.toLinearMap.compl₁₂
    (ULift.moduleEquiv : TypeG2RootSpaceULift.{u} ≃ₗ[ℝ] Vec 2).toLinearMap
    (ULift.moduleEquiv : TypeG2CorootSpaceULift.{u} ≃ₗ[ℝ] Vec 2).toLinearMap
  let root : TypeG2RootIndexULift.{u} ↪ TypeG2RootSpaceULift.{u} :=
    ⟨fun i => ⟨P.root i.down⟩, by
      intro i j h
      apply ULift.ext
      apply P.root.injective
      exact congrArg ULift.down h⟩
  let coroot : TypeG2RootIndexULift.{u} ↪ TypeG2CorootSpaceULift.{u} :=
    ⟨fun i => ⟨P.coroot i.down⟩, by
      intro i j h
      apply ULift.ext
      apply P.coroot.injective
      exact congrArg ULift.down h⟩
  let reflect (i : TypeG2RootIndexULift.{u}) :
      TypeG2RootIndexULift.{u} ≃ TypeG2RootIndexULift.{u} :=
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

/-- Forgetting the universe lift recovers the canonical G2 pairing. -/
public noncomputable def typeG2RootPairingULiftEquiv :
    RootPairing.Equiv
      (typeG2RootPairingULift :
        RootPairing (TypeG2RootIndexULift.{u}) ℝ
          (TypeG2RootSpaceULift.{u}) (TypeG2CorootSpaceULift.{u}))
      typeG2RootPairing where
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
public noncomputable instance typeG2RootPairingULift_isRootSystem :
    (typeG2RootPairingULift :
      RootPairing (TypeG2RootIndexULift.{u}) ℝ
        (TypeG2RootSpaceULift.{u}) (TypeG2CorootSpaceULift.{u})).IsRootSystem where
  span_root_eq_top := by
    change Submodule.span ℝ (Set.range
      (fun i : TypeG2RootIndexULift.{u} =>
        (⟨typeG2RootPairing.root i.down⟩ : TypeG2RootSpaceULift.{u}))) = ⊤
    let e : TypeG2RootSpaceULift.{u} ≃ₗ[ℝ] Vec 2 := ULift.moduleEquiv
    apply Submodule.map_injective_of_injective e.injective
    rw [Submodule.map_span]
    have himage : e.toLinearMap '' Set.range
        (fun i : TypeG2RootIndexULift.{u} =>
          (⟨typeG2RootPairing.root i.down⟩ : TypeG2RootSpaceULift.{u})) =
        Set.range typeG2RootPairing.root := by
      ext y
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i.down, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨⟨typeG2RootPairing.root i⟩, ⟨⟨i⟩, rfl⟩, rfl⟩
    rw [himage, RootPairing.IsRootSystem.span_root_eq_top,
      Submodule.map_top]
    exact (LinearMap.range_eq_top.mpr e.surjective).symm
  span_coroot_eq_top := by
    change Submodule.span ℝ (Set.range
      (fun i : TypeG2RootIndexULift.{u} =>
        (⟨typeG2RootPairing.coroot i.down⟩ : TypeG2CorootSpaceULift.{u}))) = ⊤
    let e : TypeG2CorootSpaceULift.{u} ≃ₗ[ℝ] Vec 2 := ULift.moduleEquiv
    apply Submodule.map_injective_of_injective e.injective
    rw [Submodule.map_span]
    have himage : e.toLinearMap '' Set.range
        (fun i : TypeG2RootIndexULift.{u} =>
          (⟨typeG2RootPairing.coroot i.down⟩ : TypeG2CorootSpaceULift.{u})) =
        Set.range typeG2RootPairing.coroot := by
      ext y
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i.down, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨⟨typeG2RootPairing.coroot i⟩, ⟨⟨i⟩, rfl⟩, rfl⟩
    rw [himage, RootPairing.IsRootSystem.span_coroot_eq_top,
      Submodule.map_top]
    exact (LinearMap.range_eq_top.mpr e.surjective).symm

/-- The universe lift retains the integral Cartan pairing. -/
public noncomputable instance typeG2RootPairingULift_isCrystallographic :
    (typeG2RootPairingULift :
      RootPairing (TypeG2RootIndexULift.{u}) ℝ
        (TypeG2RootSpaceULift.{u})
        (TypeG2CorootSpaceULift.{u})).IsCrystallographic where
  exists_value i j := by
    change ∃ z : ℤ, (z : ℝ) = typeG2RootPairing.pairing i.down j.down
    exact typeG2RootPairing.exists_value (S := ℤ) i.down j.down

/-- The universe lift retains reducedness. -/
public noncomputable instance typeG2RootPairingULift_isReduced :
    (typeG2RootPairingULift :
      RootPairing (TypeG2RootIndexULift.{u}) ℝ
        (TypeG2RootSpaceULift.{u}) (TypeG2CorootSpaceULift.{u})).IsReduced where
  eq_or_eq_neg i j h := by
    change ¬ LinearIndependent ℝ
      ![(⟨typeG2RootPairing.root i.down⟩ : TypeG2RootSpaceULift.{u}),
        (⟨typeG2RootPairing.root j.down⟩ : TypeG2RootSpaceULift.{u})] at h
    have hdown : ¬ LinearIndependent ℝ
        ![typeG2RootPairing.root i.down, typeG2RootPairing.root j.down] := by
      intro hli
      apply h
      have hmapped := hli.map'
        (ULift.moduleEquiv.symm : Vec 2 ≃ₗ[ℝ] TypeG2RootSpaceULift.{u}).toLinearMap
        (LinearMap.ker_eq_bot.mpr
          (ULift.moduleEquiv.symm : Vec 2 ≃ₗ[ℝ]
            TypeG2RootSpaceULift.{u}).injective)
      have hvectors :
          (![(⟨typeG2RootPairing.root i.down⟩ : TypeG2RootSpaceULift.{u}),
            (⟨typeG2RootPairing.root j.down⟩ : TypeG2RootSpaceULift.{u})] :
              Fin 2 → TypeG2RootSpaceULift.{u}) =
            (ULift.moduleEquiv.symm : Vec 2 ≃ₗ[ℝ]
              TypeG2RootSpaceULift.{u}) ∘
              ![typeG2RootPairing.root i.down,
                typeG2RootPairing.root j.down] := by
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
public noncomputable def typeG2RootPairingULift_base :
    (typeG2RootPairingULift :
      RootPairing (TypeG2RootIndexULift.{u}) ℝ
        (TypeG2RootSpaceULift.{u}) (TypeG2CorootSpaceULift.{u})).Base :=
  RootPairing.Base.mapEquiv
    (RootPairing.Equiv.symm _ _ typeG2RootPairingULiftEquiv)
    typeG2RootPairing_base

/-- The transported support identified with the support of the standard base. -/
public noncomputable def typeG2RootPairingULift_supportEquiv :
    typeG2RootPairingULift_base.support ≃ typeG2RootPairing_base.support :=
  Equiv.subtypeEquiv typeG2RootPairingULiftEquiv.indexEquiv (fun i => by
    change i ∈ typeG2RootPairingULift_base.support ↔
      typeG2RootPairingULiftEquiv.indexEquiv i ∈ typeG2RootPairing_base.support
    rw [show typeG2RootPairingULift_base = RootPairing.Base.mapEquiv
        (RootPairing.Equiv.symm _ _ typeG2RootPairingULiftEquiv)
        typeG2RootPairing_base by rfl]
    rw [RootPairing.Base.mem_mapEquiv_support]
    simp)

/-- The short and long simple roots identify Fin 2 with the lifted base support. -/
public noncomputable def typeG2RootPairingULift_baseEquiv :
    Fin 2 ≃ typeG2RootPairingULift_base.support :=
  typeG2RootPairing_baseEquiv.trans typeG2RootPairingULift_supportEquiv.symm

private lemma typeG2RootPairingULift_cartan_supportEquiv
    (i j : typeG2RootPairingULift_base.support) :
    typeG2RootPairingULift_base.cartanMatrixIn ℤ i j =
      typeG2RootPairing_base.cartanMatrixIn ℤ
        (typeG2RootPairingULift_supportEquiv i)
        (typeG2RootPairingULift_supportEquiv j) := by
  rw [RootPairing.Base.cartanMatrixIn_def,
    RootPairing.Base.cartanMatrixIn_def]
  apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℝ)))
  change algebraMap ℤ ℝ (typeG2RootPairingULift.pairingIn ℤ i j) =
    algebraMap ℤ ℝ (typeG2RootPairing.pairingIn ℤ
      (typeG2RootPairingULift_supportEquiv i)
      (typeG2RootPairingULift_supportEquiv j))
  rw [typeG2RootPairingULift.algebraMap_pairingIn,
    typeG2RootPairing.algebraMap_pairingIn]
  exact (typeG2RootPairingULiftEquiv.pairing_eq i j).symm

/-- The lifted base has the standard G2 Cartan entries in displayed order. -/
public lemma typeG2RootPairingULift_base_cartan_apply (i j : Fin 2) :
    typeG2RootPairingULift_base.cartanMatrix
        (typeG2RootPairingULift_baseEquiv i)
        (typeG2RootPairingULift_baseEquiv j) =
      typeG2CartanMatrix i j := by
  change typeG2RootPairingULift_base.cartanMatrixIn ℤ
      (typeG2RootPairingULift_baseEquiv i)
      (typeG2RootPairingULift_baseEquiv j) =
    typeG2CartanMatrix i j
  rw [typeG2RootPairingULift_cartan_supportEquiv]
  simpa [typeG2RootPairingULift_baseEquiv] using
    typeG2RootPairing_base_cartan_apply i j

/-- Reindexing the lifted base by Fin 2 gives the standard G2 Cartan matrix. -/
public theorem typeG2RootPairingULift_base_cartan :
    typeG2RootPairingULift_base.cartanMatrix.reindex
        typeG2RootPairingULift_baseEquiv.symm
        typeG2RootPairingULift_baseEquiv.symm =
      typeG2CartanMatrix := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  exact typeG2RootPairingULift_base_cartan_apply i j

private lemma typeG2RootPairingULift_base_cartan_connected
    (s t : typeG2RootPairingULift_base.support) :
    Relation.ReflTransGen
      (fun u v : typeG2RootPairingULift_base.support =>
        typeG2RootPairingULift_base.cartanMatrix u v ≠ 0) s t := by
  rw [← typeG2RootPairingULift_baseEquiv.apply_symm_apply s,
    ← typeG2RootPairingULift_baseEquiv.apply_symm_apply t]
  exact Relation.ReflTransGen.lift typeG2RootPairingULift_baseEquiv
    (fun i j h => by
      change typeG2RootPairingULift_base.cartanMatrix
        (typeG2RootPairingULift_baseEquiv i)
        (typeG2RootPairingULift_baseEquiv j) ≠ 0
      rw [typeG2RootPairingULift_base_cartan_apply]
      exact h)
    _ _ (typeG2Cartan_connected _ _)

/-- The universe-lifted G2 pairing remains irreducible. -/
public noncomputable instance typeG2RootPairingULift_isIrreducible :
    (typeG2RootPairingULift :
      RootPairing (TypeG2RootIndexULift.{u}) ℝ
        (TypeG2RootSpaceULift.{u})
        (TypeG2CorootSpaceULift.{u})).IsIrreducible :=
  isIrreducible_of_cartan_connected
    (typeG2RootPairingULift :
      RootPairing (TypeG2RootIndexULift.{u}) ℝ
        (TypeG2RootSpaceULift.{u}) (TypeG2CorootSpaceULift.{u}))
    typeG2RootPairingULift_base
    ⟨(typeG2RootPairingULift_baseEquiv 0 : TypeG2RootIndexULift.{u}),
      (typeG2RootPairingULift_baseEquiv 0).property⟩
    typeG2RootPairingULift_base_cartan_connected

end

end

end Theory.AlgebraicGroup.StandardRootSystem
