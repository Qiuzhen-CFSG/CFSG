module

public import Theory.AlgebraicGroup.ClosedSubgroup.Conjugation
public import Theory.AlgebraicGroup.RootSubgroups.Defs

universe u

/-! Conjugation and reparametrization of torus root subgroups. -/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def rootConjugationIso
    {K : Variety k} [AlgebraicGroup K] (T X : ClosedSubgroup K)
    (hInv : IsClosedSubgroupInvariant T X)
    (s : Variety.Point T.carrierVariety) :
    AlgebraicGroup.Iso X.carrierVariety X.carrierVariety := by
  let g : Variety.Point K := T.includePoint s
  have hg : g ∈ T := (T.pointEquiv s).property
  have hinc (x : Variety.Point X.carrierVariety) :
      X.inclusion.onPoints x = X.inclusion.toVariety.toFun x := rfl
  let forwardAmbient : AlgebraicGroup.Morphism X.carrierVariety K :=
    { toVariety :=
        (AlgebraicGroup.conjugationByMorphism K g⁻¹).comp X.inclusion.toVariety
      map_one := by
        change g⁻¹ * X.inclusion.onPoints 1 * (g⁻¹)⁻¹ = 1
        rw [X.inclusion.onPoints.map_one]
        group
      map_mul := by
        intro x y
        change g⁻¹ * X.inclusion.onPoints (x * y) * (g⁻¹)⁻¹ =
          (g⁻¹ * X.inclusion.onPoints x * (g⁻¹)⁻¹) *
            (g⁻¹ * X.inclusion.onPoints y * (g⁻¹)⁻¹)
        rw [X.inclusion.onPoints.map_mul]
        group }
  have hforwardAmbient (x) : forwardAmbient.onPoints x =
      g⁻¹ * X.inclusion.onPoints x * g := by
    change (AlgebraicGroup.conjugationByMorphism K g⁻¹).toFun
      (X.inclusion.onPoints x) = _
    simpa only [inv_inv] using
      (AlgebraicGroup.conjugationByMorphism_apply K g⁻¹
        (X.inclusion.onPoints x))
  have hforward : ∀ x, forwardAmbient.onPoints x ∈ X := by
    intro x
    rw [hforwardAmbient]
    simpa only [inv_inv, hinc] using
      hInv g hg (X.inclusion.onPoints x) (X.pointEquiv x).property
  let backwardAmbient : AlgebraicGroup.Morphism X.carrierVariety K :=
    { toVariety :=
        (AlgebraicGroup.conjugationByMorphism K g).comp X.inclusion.toVariety
      map_one := by
        change g * X.inclusion.onPoints 1 * g⁻¹ = 1
        rw [X.inclusion.onPoints.map_one]
        group
      map_mul := by
        intro x y
        change g * X.inclusion.onPoints (x * y) * g⁻¹ =
          (g * X.inclusion.onPoints x * g⁻¹) *
            (g * X.inclusion.onPoints y * g⁻¹)
        rw [X.inclusion.onPoints.map_mul]
        group }
  have hbackwardAmbient (x) : backwardAmbient.onPoints x =
      g * X.inclusion.onPoints x * g⁻¹ := by
    exact AlgebraicGroup.conjugationByMorphism_apply K g _
  have hbackward : ∀ x, backwardAmbient.onPoints x ∈ X := by
    intro x
    rw [hbackwardAmbient]
    have hginv : g⁻¹ ∈ T := T.toSubgroup.inv_mem hg
    simpa only [inv_inv, hinc] using
      hInv g⁻¹ hginv (X.inclusion.onPoints x) (X.pointEquiv x).property
  let forward := forwardAmbient.codRestrictClosedSubgroup X hforward
  let backward := backwardAmbient.codRestrictClosedSubgroup X hbackward
  have hforward_apply (x) : X.inclusion.onPoints (forward.onPoints x) =
      g⁻¹ * X.inclusion.onPoints x * g := by
    rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
    exact hforwardAmbient x
  have hbackward_apply (x) : X.inclusion.onPoints (backward.onPoints x) =
      g * X.inclusion.onPoints x * g⁻¹ := by
    rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
    exact hbackwardAmbient x
  exact
    { hom := forward
      inv := backward
      hom_inv_id := by
        intro x
        apply X.inclusion_injective
        rw [hbackward_apply, hforward_apply]
        group
      inv_hom_id := by
        intro x
        apply X.inclusion_injective
        rw [hforward_apply, hbackward_apply]
        group }

omit [IsAlgClosed k] in
public lemma rootConjugationIso_inclusion_apply
    {K : Variety k} [AlgebraicGroup K] (T X : ClosedSubgroup K)
    (hInv : IsClosedSubgroupInvariant T X)
    (s : Variety.Point T.carrierVariety) (x : Variety.Point X.carrierVariety) :
    X.inclusion.onPoints ((rootConjugationIso T X hInv s).hom.onPoints x) =
      (T.includePoint s)⁻¹ * X.inclusion.onPoints x * T.includePoint s := by
  change X.inclusion.onPoints
      ((AlgebraicGroup.Morphism.codRestrictClosedSubgroup _ X _).onPoints x) = _
  rw [AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
  change (AlgebraicGroup.conjugationByMorphism K (T.includePoint s)⁻¹).toFun
    (X.inclusion.onPoints x) = _
  simpa only [inv_inv] using
    (AlgebraicGroup.conjugationByMorphism_apply K (T.includePoint s)⁻¹
      (X.inclusion.onPoints x))

omit [IsAlgClosed k] in
/-- Two one-parameter closed subgroups are equal when their parametrizations
agree in the ambient group up to a nonzero scalar. -/
public theorem rootSubgroup_eq_of_parametrization_rescale
    {K : Variety k} [AlgebraicGroup K]
    {X Y : ClosedSubgroup K}
    (x : OneParameterParametrization X.carrierVariety)
    (y : OneParameterParametrization Y.carrierVariety)
    (c : k) (hc : c ≠ 0)
    (hxy : ∀ t,
      X.includePoint (x.value t) = Y.includePoint (y.value (c * t))) :
    X = Y := by
  apply SetLike.coe_injective
  ext g
  constructor
  · intro hg
    let gx : Variety.Point X.carrierVariety := X.pointEquiv.symm ⟨g, hg⟩
    let q : Variety.Point (KPlus k) := x.inv.onPoints gx
    let t : k := Multiplicative.toAdd (additiveGroupPointEquiv k q)
    have hq : kPlusPoint t = q := by
      apply (additiveGroupPointEquiv k).injective
      exact Multiplicative.ofAdd.apply_symm_apply (additiveGroupPointEquiv k q)
    have hxg : X.includePoint (x.value t) = g := by
      change (X.pointEquiv (x.hom.onPoints (kPlusPoint t))).val = g
      rw [hq, x.inv_hom_id]
      exact congrArg Subtype.val (X.pointEquiv.apply_symm_apply ⟨g, hg⟩)
    have hymem : Y.includePoint (y.value (c * t)) ∈ Y :=
      (Y.pointEquiv (y.value (c * t))).property
    rw [← hxy t, hxg] at hymem
    exact hymem
  · intro hg
    let gy : Variety.Point Y.carrierVariety := Y.pointEquiv.symm ⟨g, hg⟩
    let q : Variety.Point (KPlus k) := y.inv.onPoints gy
    let t : k := Multiplicative.toAdd (additiveGroupPointEquiv k q)
    have hq : kPlusPoint t = q := by
      apply (additiveGroupPointEquiv k).injective
      exact Multiplicative.ofAdd.apply_symm_apply (additiveGroupPointEquiv k q)
    have hyg : Y.includePoint (y.value t) = g := by
      change (Y.pointEquiv (y.hom.onPoints (kPlusPoint t))).val = g
      rw [hq, y.inv_hom_id]
      exact congrArg Subtype.val (Y.pointEquiv.apply_symm_apply ⟨g, hg⟩)
    have hxmem : X.includePoint (x.value (c⁻¹ * t)) ∈ X :=
      (X.pointEquiv (x.value (c⁻¹ * t))).property
    have hrescale : c * (c⁻¹ * t) = t := by field_simp
    rw [hxy (c⁻¹ * t), hrescale, hyg] at hxmem
    exact hxmem

omit [IsAlgClosed k] in
public lemma rootWeightEquation_unique
    {K : Variety k} [AlgebraicGroup K] (T X : ClosedSubgroup K)
    (hOne : IsOneParameterGroup X.carrierVariety)
    {χ ψ : TorusWeight T}
    (hχ : RootWeightEquation T X χ) (hψ : RootWeightEquation T X ψ) :
    χ = ψ := by
  apply TorusCharacter.pointCharacter_injective
  ext s
  let x : OneParameterParametrization X.carrierVariety := Classical.choice hOne
  have hχs := hχ x 1 s
  have hψs := hψ x 1 s
  simp only [mul_one] at hχs hψs
  have hamb : X.includePoint (x.value (χ.pointCharacter s)) =
      X.includePoint (x.value (ψ.pointCharacter s)) := hχs.symm.trans hψs
  have hxval : x.value (χ.pointCharacter s) = x.value (ψ.pointCharacter s) := by
    apply X.inclusion_injective
    exact hamb
  have hkplus : kPlusPoint (χ.pointCharacter s) = kPlusPoint (ψ.pointCharacter s) := by
    have h := congrArg x.inv.onPoints hxval
    change x.inv.onPoints (x.hom.onPoints (kPlusPoint (χ.pointCharacter s))) =
      x.inv.onPoints (x.hom.onPoints (kPlusPoint (ψ.pointCharacter s))) at h
    simpa only [x.hom_inv_id] using h
  exact congrArg (fun z : Variety.Point (KPlus k) => z.val PUnit.unit) hkplus

/-- Transport torus weights across conjugation of the torus. -/
@[expose]
public noncomputable def torusWeightConjugateEquiv
    {G : Variety k} [AlgebraicGroup G]
    (T : ClosedSubgroup G) (g : Variety.Point G) :
    TorusWeight T ≃ TorusWeight (T.conjugate g) where
  toFun χ := χ.comp (T.conjugateIso g).inv
  invFun ψ := ψ.comp (T.conjugateIso g).hom
  left_inv χ := by
    apply AlgebraicGroup.Morphism.ext
    funext z
    change χ.onPoints ((T.conjugateIso g).inv.onPoints
      ((T.conjugateIso g).hom.onPoints z)) = χ.onPoints z
    rw [(T.conjugateIso g).hom_inv_id]
  right_inv ψ := by
    apply AlgebraicGroup.Morphism.ext
    funext z
    change ψ.onPoints ((T.conjugateIso g).hom.onPoints
      ((T.conjugateIso g).inv.onPoints z)) = ψ.onPoints z
    rw [(T.conjugateIso g).inv_hom_id]

omit [IsAlgClosed k] in
public lemma torusWeightConjugateEquiv_pointCharacter
    {G : Variety k} [AlgebraicGroup G]
    (T : ClosedSubgroup G) (g : Variety.Point G)
    (χ : TorusWeight T)
    (s : Variety.Point (T.conjugate g).carrierVariety) :
    (torusWeightConjugateEquiv T g χ).pointCharacter s =
      χ.pointCharacter ((T.conjugateIso g).inv.onPoints s) := by
  rfl

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def rootConjugationScalar
    {K : Variety k} [AlgebraicGroup K] (T X : ClosedSubgroup K)
    (x : OneParameterParametrization X.carrierVariety)
    (hInv : IsClosedSubgroupInvariant T X)
    (s : Variety.Point T.carrierVariety) : k :=
  (x.inv.onPoints
    ((rootConjugationIso T X hInv s).hom.onPoints (x.value 1))).val PUnit.unit

/-- The scalar describing conjugation on a one-parameter root subgroup is
nonzero. -/
public lemma rootConjugationScalar_ne_zero
    {K : Variety k} [AlgebraicGroup K] (T X : ClosedSubgroup K)
    (x : OneParameterParametrization X.carrierVariety)
    (hInv : IsClosedSubgroupInvariant T X)
    (s : Variety.Point T.carrierVariety) :
    rootConjugationScalar T X x hInv s ≠ 0 := by
  let r := rootConjugationIso T X hInv s
  let xSymm : AlgebraicGroup.Iso X.carrierVariety (KPlus k) :=
    { hom := x.inv
      inv := x.hom
      hom_inv_id := x.inv_hom_id
      inv_hom_id := x.hom_inv_id }
  let e : AlgebraicGroup.Iso (KPlus k) (KPlus k) := xSymm.comp (r.comp x)
  rcases kPlus_automorphism_eq_scalar e with ⟨c, hc, -⟩
  have hcscalar : rootConjugationScalar T X x hInv s = c := by
    have h := congrArg (fun z : Variety.Point (KPlus k) => z.val PUnit.unit) (hc.2 1)
    change rootConjugationScalar T X x hInv s = c * 1 at h
    simpa only [mul_one] using h
  rw [hcscalar]
  exact hc.1

/-- Conjugation by a torus point rescales the chosen parametrization. -/
public lemma rootConjugation_preserves_parametrization
    {K : Variety k} [AlgebraicGroup K] (T X : ClosedSubgroup K)
    (x : OneParameterParametrization X.carrierVariety)
    (hInv : IsClosedSubgroupInvariant T X)
    (s : Variety.Point T.carrierVariety) :
    ∀ t, (rootConjugationIso T X hInv s).hom.onPoints (x.value t) =
      x.value (rootConjugationScalar T X x hInv s * t) := by
  let r := rootConjugationIso T X hInv s
  let xSymm : AlgebraicGroup.Iso X.carrierVariety (KPlus k) :=
    { hom := x.inv
      inv := x.hom
      hom_inv_id := x.inv_hom_id
      inv_hom_id := x.hom_inv_id }
  let e : AlgebraicGroup.Iso (KPlus k) (KPlus k) := xSymm.comp (r.comp x)
  rcases kPlus_automorphism_eq_scalar e with ⟨c, hc, -⟩
  have hcscalar : rootConjugationScalar T X x hInv s = c := by
    have h := congrArg (fun z : Variety.Point (KPlus k) => z.val PUnit.unit) (hc.2 1)
    change rootConjugationScalar T X x hInv s = c * 1 at h
    simpa only [mul_one] using h
  intro t
  have ht := hc.2 t
  have ht' := congrArg x.hom.onPoints ht
  change x.hom.onPoints
      (x.inv.onPoints (r.hom.onPoints (x.hom.onPoints (kPlusPoint t)))) =
    x.hom.onPoints (kPlusPoint (c * t)) at ht'
  rw [x.inv_hom_id] at ht'
  change r.hom.onPoints (x.value t) = x.value (c * t) at ht'
  rwa [hcscalar]

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private lemma parameter_eq_of_value_eq
    {X : Variety k} [AlgebraicGroup X]
    (x : OneParameterParametrization X) {a b : k}
    (h : x.value a = x.value b) : a = b := by
  have h' := congrArg x.inv.onPoints h
  change x.inv.onPoints (x.hom.onPoints (kPlusPoint a)) =
    x.inv.onPoints (x.hom.onPoints (kPlusPoint b)) at h'
  rw [x.hom_inv_id, x.hom_inv_id] at h'
  exact congrArg (fun z : Variety.Point (KPlus k) => z.val PUnit.unit) h'

/-- The root-conjugation scalar describes the ambient conjugation action. -/
public lemma rootConjugationScalar_ambient_action
    {K : Variety k} [AlgebraicGroup K] (T X : ClosedSubgroup K)
    (x : OneParameterParametrization X.carrierVariety)
    (hInv : IsClosedSubgroupInvariant T X)
    (s : Variety.Point T.carrierVariety) (t : k) :
    X.inclusion.onPoints (x.value (rootConjugationScalar T X x hInv s * t)) =
      (T.inclusion.onPoints s)⁻¹ * X.inclusion.onPoints (x.value t) *
        T.inclusion.onPoints s := by
  calc
    _ = X.inclusion.onPoints
        ((rootConjugationIso T X hInv s).hom.onPoints (x.value t)) :=
      congrArg X.inclusion.onPoints
        (rootConjugation_preserves_parametrization T X x hInv s t).symm
    _ = _ := rootConjugationIso_inclusion_apply T X hInv s (x.value t)

/-- The root-conjugation scalar of the identity is one. -/
public lemma rootConjugationScalar_one
    {K : Variety k} [AlgebraicGroup K] (T X : ClosedSubgroup K)
    (x : OneParameterParametrization X.carrierVariety)
    (hInv : IsClosedSubgroupInvariant T X) :
    rootConjugationScalar T X x hInv 1 = 1 := by
  apply parameter_eq_of_value_eq x
  apply X.inclusion_injective
  have h := rootConjugationScalar_ambient_action T X x hInv 1 1
  simp only [mul_one, T.inclusion.onPoints.map_one] at h
  simpa only [inv_one, one_mul, mul_one] using h

/-- Root-conjugation scalars are multiplicative in the torus point. -/
public lemma rootConjugationScalar_mul
    {K : Variety k} [AlgebraicGroup K] (T X : ClosedSubgroup K)
    (x : OneParameterParametrization X.carrierVariety)
    (hInv : IsClosedSubgroupInvariant T X)
    (s t : Variety.Point T.carrierVariety) :
    rootConjugationScalar T X x hInv (s * t) =
      rootConjugationScalar T X x hInv s *
        rootConjugationScalar T X x hInv t := by
  apply parameter_eq_of_value_eq x
  apply X.inclusion_injective
  have hst := rootConjugationScalar_ambient_action T X x hInv (s * t) 1
  have hs := rootConjugationScalar_ambient_action T X x hInv s 1
  have ht := rootConjugationScalar_ambient_action T X x hInv t
      (rootConjugationScalar T X x hInv s)
  simp only [mul_one] at hst hs
  calc
    X.inclusion.onPoints
        (x.value (rootConjugationScalar T X x hInv (s * t))) =
      (T.inclusion.onPoints (s * t))⁻¹ * X.inclusion.onPoints (x.value 1) *
        T.inclusion.onPoints (s * t) := hst
    _ = (T.inclusion.onPoints t)⁻¹ *
          ((T.inclusion.onPoints s)⁻¹ * X.inclusion.onPoints (x.value 1) *
            T.inclusion.onPoints s) * T.inclusion.onPoints t := by
      rw [T.inclusion.onPoints.map_mul]
      group
    _ = (T.inclusion.onPoints t)⁻¹ *
          X.inclusion.onPoints
            (x.value (rootConjugationScalar T X x hInv s)) *
          T.inclusion.onPoints t := by rw [hs]
    _ = X.inclusion.onPoints
          (x.value (rootConjugationScalar T X x hInv t *
            rootConjugationScalar T X x hInv s)) := ht.symm
    _ = X.inclusion.onPoints
          (x.value (rootConjugationScalar T X x hInv s *
            rootConjugationScalar T X x hInv t)) := by rw [mul_comm]

public noncomputable def rootConjugationOrbitMorphism
    {K : Variety k} [AlgebraicGroup K] (T X : ClosedSubgroup K)
    (x : OneParameterParametrization X.carrierVariety)
    (hInv : IsClosedSubgroupInvariant T X) :
    Variety.Morphism T.carrierVariety (KPlus k) := by
  let a : Variety.Point K := X.inclusion.onPoints (x.value 1)
  let ambient : Variety.Morphism T.carrierVariety K :=
    (AlgebraicGroup.inverseConjugateMorphism K a).comp T.inclusion.toVariety
  have hmap : ∀ s, ambient.toFun s ∈ X := by
    intro s
    dsimp [ambient, Variety.Morphism.comp]
    rw [AlgebraicGroup.inverseConjugateMorphism_apply]
    exact hInv (T.inclusion.onPoints s) (T.pointEquiv s).property a
      (X.pointEquiv (x.value 1)).property
  let orbitX : Variety.Morphism T.carrierVariety X.carrierVariety :=
    { toFun := fun s => X.pointEquiv.symm ⟨ambient.toFun s, hmap s⟩
      regular := by
        intro i
        obtain ⟨p, hp⟩ := ambient.regular i
        refine ⟨p, ?_⟩
        intro s
        change (X.pointEquiv
          (X.pointEquiv.symm ⟨ambient.toFun s, hmap s⟩)).val.val i =
          evalPolynomial s.val p
        rw [X.pointEquiv.apply_symm_apply]
        exact hp s }
  exact x.inv.toVariety.comp orbitX

omit [IsAlgClosed k] in
public lemma rootConjugationOrbitMorphism_apply
    {K : Variety k} [AlgebraicGroup K] (T X : ClosedSubgroup K)
    (x : OneParameterParametrization X.carrierVariety)
    (hInv : IsClosedSubgroupInvariant T X)
    (s : Variety.Point T.carrierVariety) :
    (rootConjugationOrbitMorphism T X x hInv).toFun s =
      kPlusPoint (rootConjugationScalar T X x hInv s) := by
  let a : Variety.Point K := X.inclusion.onPoints (x.value 1)
  let ambient : Variety.Morphism T.carrierVariety K :=
    (AlgebraicGroup.inverseConjugateMorphism K a).comp T.inclusion.toVariety
  have hmap : ∀ z, ambient.toFun z ∈ X := by
    intro z
    dsimp [ambient, Variety.Morphism.comp]
    rw [AlgebraicGroup.inverseConjugateMorphism_apply]
    exact hInv (T.inclusion.onPoints z) (T.pointEquiv z).property a
      (X.pointEquiv (x.value 1)).property
  let orbitX : Variety.Morphism T.carrierVariety X.carrierVariety :=
    { toFun := fun z => X.pointEquiv.symm ⟨ambient.toFun z, hmap z⟩
      regular := by
        intro i
        obtain ⟨p, hp⟩ := ambient.regular i
        refine ⟨p, ?_⟩
        intro z
        change (X.pointEquiv
          (X.pointEquiv.symm ⟨ambient.toFun z, hmap z⟩)).val.val i =
          evalPolynomial z.val p
        rw [X.pointEquiv.apply_symm_apply]
        exact hp z }
  change x.inv.toVariety.toFun (orbitX.toFun s) = _
  have horbitX (z : Variety.Point T.carrierVariety) :
      X.inclusion.onPoints (orbitX.toFun z) = ambient.toFun z := by
    change (X.pointEquiv
      (X.pointEquiv.symm ⟨ambient.toFun z, hmap z⟩)).val = ambient.toFun z
    rw [X.pointEquiv.apply_symm_apply]
  have horbit : orbitX.toFun s =
      (rootConjugationIso T X hInv s).hom.onPoints (x.value 1) := by
    apply X.inclusion_injective
    rw [horbitX, rootConjugationIso_inclusion_apply]
    dsimp [ambient, Variety.Morphism.comp]
    rw [AlgebraicGroup.inverseConjugateMorphism_apply]
    rfl
  rw [horbit]
  change x.inv.onPoints
      ((rootConjugationIso T X hInv s).hom.onPoints (x.value 1)) = _
  apply Variety.Point.ext
  funext i
  cases i
  rfl

@[expose]
public noncomputable def rootConjugationCharacter
    {K : Variety k} [AlgebraicGroup K] (T X : ClosedSubgroup K)
    (x : OneParameterParametrization X.carrierVariety)
    (hInv : IsClosedSubgroupInvariant T X) : TorusWeight T := by
  let orbit := rootConjugationOrbitMorphism T X x hInv
  let orbitInv := orbit.comp (AlgebraicGroup.invMorphism T.carrierVariety)
  let c : Variety.Point T.carrierVariety → k :=
    rootConjugationScalar T X x hInv
  have hc : ∀ s, c s ≠ 0 := fun s =>
    rootConjugationScalar_ne_zero T X x hInv s
  have hinv : ∀ s, (c s)⁻¹ = c s⁻¹ := by
    intro s
    apply inv_eq_of_mul_eq_one_right
    rw [← rootConjugationScalar_mul, mul_inv_cancel,
      rootConjugationScalar_one]
  let F : Variety.Morphism T.carrierVariety (KMult k) :=
    { toFun := fun s => (dPointEquiv 1).symm fun _ => Units.mk0 (c s) (hc s)
      regular := by
        intro i
        cases i with
        | inl _ =>
            obtain ⟨p, hp⟩ := orbit.regular PUnit.unit
            refine ⟨p, ?_⟩
            intro s
            change (c s : k) = evalPolynomial s.val p
            rw [← hp s]
            have h := congrArg
              (fun z : Variety.Point (KPlus k) => z.val PUnit.unit)
              (rootConjugationOrbitMorphism_apply T X x hInv s)
            change (orbit.toFun s).val PUnit.unit = c s at h
            exact h.symm
        | inr _ =>
            obtain ⟨p, hp⟩ := orbitInv.regular PUnit.unit
            refine ⟨p, ?_⟩
            intro s
            change (c s)⁻¹ = evalPolynomial s.val p
            rw [hinv s, ← hp s]
            have h := congrArg
              (fun z : Variety.Point (KPlus k) => z.val PUnit.unit)
              (rootConjugationOrbitMorphism_apply T X x hInv (s⁻¹))
            change (orbitInv.toFun s).val PUnit.unit = c s⁻¹ at h
            exact h.symm }
  exact
    { toVariety := F
      map_one := by
        apply (dPointEquiv 1).injective
        rw [dPointEquiv_one]
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        simp [F, c, rootConjugationScalar_one T X x hInv]
      map_mul := by
        intro s t
        apply (dPointEquiv 1).injective
        rw [dPointEquiv_mul]
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        change Units.mk0 (c (s * t)) (hc (s * t)) =
          Units.mk0 (c s) (hc s) * Units.mk0 (c t) (hc t)
        apply Units.ext
        exact rootConjugationScalar_mul T X x hInv s t }

omit [IsAlgClosed k] in
/-- Conjugation transports torus root subgroups. -/
public lemma IsTorusRootSubgroup.conjugate
    {G : Variety k} [AlgebraicGroup G]
    {T X : ClosedSubgroup G} (g : Variety.Point G)
    (hX : IsTorusRootSubgroup T X) :
    IsTorusRootSubgroup (T.conjugate g) (X.conjugate g) := by
  constructor
  · intro t ht x hx
    rw [X.mem_conjugate_iff] at hx ⊢
    rw [T.mem_conjugate_iff] at ht
    have hinv := hX.1 (g⁻¹ * t * g) ht (g⁻¹ * x * g) hx
    have heq : g⁻¹ * (t⁻¹ * x * t) * g =
        (g⁻¹ * t * g)⁻¹ * (g⁻¹ * x * g) * (g⁻¹ * t * g) := by
      group
    rw [heq]
    exact hinv
  · let x : OneParameterParametrization X.carrierVariety :=
      Classical.choice hX.2
    exact ⟨(X.conjugateIso g).comp x⟩

omit [IsAlgClosed k] in
/-- Conjugation transports the root-weight equation. -/
public lemma RootWeightEquation.conjugate
    {G : Variety k} [AlgebraicGroup G]
    {T X : ClosedSubgroup G} {χ : TorusWeight T}
    (g : Variety.Point G) (hχ : RootWeightEquation T X χ) :
    RootWeightEquation (T.conjugate g) (X.conjugate g)
      (torusWeightConjugateEquiv T g χ) := by
  intro y t s
  let xIso := X.conjugateIso g
  let x : OneParameterParametrization X.carrierVariety :=
    { hom := xIso.inv.comp y.hom
      inv := y.inv.comp xIso.hom
      hom_inv_id := by
        intro z
        change y.inv.onPoints (xIso.hom.onPoints
          (xIso.inv.onPoints (y.hom.onPoints z))) = z
        rw [xIso.inv_hom_id, y.hom_inv_id]
      inv_hom_id := by
        intro z
        change xIso.inv.onPoints (y.hom.onPoints
          (y.inv.onPoints (xIso.hom.onPoints z))) = z
        rw [y.inv_hom_id, xIso.hom_inv_id] }
  let s₀ := (T.conjugateIso g).inv.onPoints s
  have h := hχ x t s₀
  have hs : T.includePoint s₀ =
      g⁻¹ * (T.conjugate g).includePoint s * g :=
    T.conjugateIso_inv_inclusion_apply g s
  have hy (a : k) : X.includePoint (x.value a) =
      g⁻¹ * (X.conjugate g).includePoint (y.value a) * g :=
    X.conjugateIso_inv_inclusion_apply g (y.value a)
  apply (MulAut.conj g⁻¹).injective
  rw [MulAut.conj_apply, MulAut.conj_apply, inv_inv]
  calc
    _ = (T.includePoint s₀)⁻¹ * X.includePoint (x.value t) *
        T.includePoint s₀ := by
      rw [hs, hy]
      group
    _ = X.includePoint (x.value (χ.pointCharacter s₀ * t)) := h
    _ = g⁻¹ * (X.conjugate g).includePoint
        (y.value (χ.pointCharacter s₀ * t)) * g := hy _
    _ = _ := by rw [torusWeightConjugateEquiv_pointCharacter]

omit [IsAlgClosed k] in
/-- Conjugation transports torus roots. -/
public lemma IsTorusRoot.conjugate
    {G : Variety k} [AlgebraicGroup G]
    {T : ClosedSubgroup G} {χ : TorusWeight T}
    (g : Variety.Point G) (hχ : IsTorusRoot T χ) :
    IsTorusRoot (T.conjugate g) (torusWeightConjugateEquiv T g χ) := by
  obtain ⟨X, hX, hEq⟩ := hχ
  exact ⟨X.conjugate g, hX.conjugate g, hEq.conjugate g⟩

omit [IsAlgClosed k] in
/-- A character is a torus root exactly when its conjugate transport is. -/
public theorem isTorusRoot_conjugate_iff
    {G : Variety k} [AlgebraicGroup G]
    (T : ClosedSubgroup G) (g : Variety.Point G) (χ : TorusWeight T) :
    IsTorusRoot T χ ↔
      IsTorusRoot (T.conjugate g) (torusWeightConjugateEquiv T g χ) := by
  constructor
  · exact IsTorusRoot.conjugate g
  · rintro ⟨Y, hY, hEq⟩
    let X := Y.conjugate g⁻¹
    have hTback : (T.conjugate g).conjugate g⁻¹ = T := by
      rw [ClosedSubgroup.conjugate_conjugate]
      rw [show g⁻¹ * g = 1 by group, ClosedSubgroup.conjugate_one]
    have hX : IsTorusRootSubgroup T X := by
      rw [← hTback]
      exact hY.conjugate g⁻¹
    refine ⟨X, hX, ?_⟩
    intro x t s
    let yIso := Y.conjugateIso g⁻¹
    let y : OneParameterParametrization Y.carrierVariety :=
      { hom := yIso.inv.comp x.hom
        inv := x.inv.comp yIso.hom
        hom_inv_id := by
          intro z
          change x.inv.onPoints (yIso.hom.onPoints
            (yIso.inv.onPoints (x.hom.onPoints z))) = z
          rw [yIso.inv_hom_id, x.hom_inv_id]
        inv_hom_id := by
          intro z
          change yIso.inv.onPoints (x.hom.onPoints
            (x.inv.onPoints (yIso.hom.onPoints z))) = z
          rw [x.inv_hom_id, yIso.hom_inv_id] }
    let s₁ := (T.conjugateIso g).hom.onPoints s
    have h := hEq y t s₁
    have hs : (T.conjugate g).includePoint s₁ =
        g * T.includePoint s * g⁻¹ :=
      T.conjugateIso_hom_inclusion_apply g s
    have hy (a : k) : Y.includePoint (y.value a) =
        g * X.includePoint (x.value a) * g⁻¹ := by
      change Y.inclusion.onPoints (yIso.inv.onPoints (x.value a)) =
        g * (Y.conjugate g⁻¹).inclusion.onPoints (x.value a) * g⁻¹
      simpa only [inv_inv] using
        Y.conjugateIso_inv_inclusion_apply g⁻¹ (x.value a)
    have hweight :
        (torusWeightConjugateEquiv T g χ).pointCharacter s₁ =
          χ.pointCharacter s := by
      rw [torusWeightConjugateEquiv_pointCharacter]
      change χ.pointCharacter ((T.conjugateIso g).inv.onPoints
        ((T.conjugateIso g).hom.onPoints s)) = χ.pointCharacter s
      rw [(T.conjugateIso g).hom_inv_id]
    apply (MulAut.conj g).injective
    rw [MulAut.conj_apply, MulAut.conj_apply]
    calc
      _ = ((T.conjugate g).includePoint s₁)⁻¹ *
          Y.includePoint (y.value t) * (T.conjugate g).includePoint s₁ := by
        rw [hs, hy]
        group
      _ = Y.includePoint (y.value
          ((torusWeightConjugateEquiv T g χ).pointCharacter s₁ * t)) := h
      _ = g * X.includePoint (x.value (χ.pointCharacter s * t)) * g⁻¹ := by
        rw [hweight, hy]

omit [IsAlgClosed k] in
/-- A normalizer element preserves the torus-root-subgroup predicate. -/
public lemma IsTorusRootSubgroup.conjugate_of_mem_normalizer
    {K : Variety k} [AlgebraicGroup K]
    {T X : ClosedSubgroup K} (g : Variety.Point K)
    (hg : g ∈ T.normalizer.toSubgroup)
    (hX : IsTorusRootSubgroup T X) :
    IsTorusRootSubgroup T (X.conjugate g) := by
  have hT : T.conjugate g = T := by
    apply SetLike.coe_injective
    ext y
    change y ∈ T.conjugate g ↔ y ∈ T.toSubgroup
    rw [T.mem_conjugate_iff]
    have hy := Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * y * g)
    simpa [mul_assoc] using hy
  rw [← hT]
  exact hX.conjugate g

/-- A root weight evaluates to its root-conjugation scalar. -/
public lemma rootWeightEquation_pointCharacter_eq_rootConjugationScalar
    {K : Variety k} [AlgebraicGroup K] (T X : ClosedSubgroup K)
    (x : OneParameterParametrization X.carrierVariety)
    (hInv : IsClosedSubgroupInvariant T X)
    (χ : TorusWeight T) (hχ : RootWeightEquation T X χ)
    (s : Variety.Point T.carrierVariety) :
    χ.pointCharacter s = rootConjugationScalar T X x hInv s := by
  have hroot := hχ x 1 s
  have hact := rootConjugationScalar_ambient_action T X x hInv s 1
  have hX (y : Variety.Point X.carrierVariety) :
      X.includePoint y = X.inclusion.onPoints y := by
    apply Variety.Point.ext
    funext i
    rfl
  have hT (y : Variety.Point T.carrierVariety) :
      T.includePoint y = T.inclusion.onPoints y := by
    apply Variety.Point.ext
    funext i
    rfl
  have hact' :
      X.includePoint (x.value (rootConjugationScalar T X x hInv s)) =
        (T.includePoint s)⁻¹ * X.includePoint (x.value 1) * T.includePoint s := by
    calc
      X.includePoint (x.value (rootConjugationScalar T X x hInv s)) =
          X.inclusion.onPoints (x.value (rootConjugationScalar T X x hInv s)) := hX _
      _ = (T.inclusion.onPoints s)⁻¹ * X.inclusion.onPoints (x.value 1) *
          T.inclusion.onPoints s := by simpa only [mul_one] using hact
      _ = (T.includePoint s)⁻¹ * X.includePoint (x.value 1) * T.includePoint s := by
        simp only [← hT, ← hX]
  have hvalue :
      X.includePoint (x.value (χ.pointCharacter s)) =
        X.includePoint (x.value (rootConjugationScalar T X x hInv s)) := by
    simpa only [mul_one] using hroot.symm.trans hact'.symm
  have hparam :
      x.value (χ.pointCharacter s) =
        x.value (rootConjugationScalar T X x hInv s) :=
    X.inclusion_injective hvalue
  have hinv := congrArg x.inv.onPoints hparam
  change x.inv.onPoints (x.hom.onPoints (kPlusPoint (χ.pointCharacter s))) =
      x.inv.onPoints (x.hom.onPoints
        (kPlusPoint (rootConjugationScalar T X x hInv s))) at hinv
  rw [x.hom_inv_id, x.hom_inv_id] at hinv
  exact congrArg (fun z : Variety.Point (KPlus k) => z.val PUnit.unit) hinv

end

end Theory.AlgebraicGroup
