module

public import Theory.AlgebraicGroup.Irreducible.Product

universe u

/-! Normalization of regular sections of algebraic-group morphisms. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- A regular section of a finite-kernel morphism over a connected target can
be normalized to a pointwise group-homomorphism section. -/
public theorem Morphism.exists_normalized_sectionPointHom_of_finiteKernel_of_connected
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H)
    (hker : Finite f.kernel)
    (hH : Variety.IsConnected H)
    (s : Variety.Morphism H G)
    (hsection : ∀ x, f.onPoints (s.toFun x) = x) :
    ∃ qv : Variety.Morphism H G,
      (∀ x, f.onPoints (qv.toFun x) = x) ∧
      qv.toFun 1 = 1 ∧
      ∀ x y, qv.toFun (x * y) = qv.toFun x * qv.toFun y := by
  let qv : Variety.Morphism H G :=
    (AlgebraicGroup.rightMulMorphism G (s.toFun 1)⁻¹).comp s
  have hqv_apply (x : Variety.Point H) :
      qv.toFun x = s.toFun x * (s.toFun 1)⁻¹ := by
    simp [qv, Variety.Morphism.comp,
      AlgebraicGroup.rightMulMorphism_apply]
  have hqsection (x : Variety.Point H) :
      f.onPoints (qv.toFun x) = x := by
    rw [hqv_apply, MonoidHom.map_mul f.onPoints,
      MonoidHom.map_inv f.onPoints, hsection, hsection]
    simp
  have hqone : qv.toFun 1 = 1 := by
    rw [hqv_apply]
    simp
  let qxy : Variety.Morphism (Variety.prod H H) G :=
    qv.comp (AlgebraicGroup.mulMorphism H)
  let qx : Variety.Morphism (Variety.prod H H) G :=
    qv.comp (Variety.Morphism.fst H H)
  let qy : Variety.Morphism (Variety.prod H H) G :=
    qv.comp (Variety.Morphism.snd H H)
  let defect : Variety.Morphism (Variety.prod H H) G :=
    (AlgebraicGroup.mulMorphism G).comp
      (((AlgebraicGroup.mulMorphism G).comp
        (qxy.pair ((AlgebraicGroup.invMorphism G).comp qy))).pair
          ((AlgebraicGroup.invMorphism G).comp qx))
  have hdefect_apply (x y : Variety.Point H) :
      defect.toFun ((Variety.prodPointEquiv H H).symm (x, y)) =
        qv.toFun (x * y) * (qv.toFun y)⁻¹ * (qv.toFun x)⁻¹ := rfl
  have hdefect_range : Set.range defect.toFun ⊆
      (f.kernel : Set (Variety.Point G)) := by
    rintro z ⟨w, rfl⟩
    obtain ⟨⟨x, y⟩, rfl⟩ :=
      (Variety.prodPointEquiv H H).symm.surjective w
    change f.onPoints
      (defect.toFun ((Variety.prodPointEquiv H H).symm (x, y))) = 1
    rw [hdefect_apply, MonoidHom.map_mul f.onPoints,
      MonoidHom.map_mul f.onPoints, MonoidHom.map_inv f.onPoints,
      MonoidHom.map_inv f.onPoints, hqsection, hqsection, hqsection]
    simp
  let : Finite f.kernel := hker
  have hdefect_finite : (Set.range defect.toFun).Finite :=
    (Set.toFinite (f.kernel : Set (Variety.Point G))).subset hdefect_range
  have hprodConnected : Variety.IsConnected (Variety.prod H H) := by
    have hI := prodSet_irreducible_of_irreducible
      (connectedAlgebraicGroup_irreducible H hH)
      (connectedAlgebraicGroup_irreducible H hH)
    have hprod : Variety.prodSet
        (Set.univ : Set (Variety.Point H))
        (Set.univ : Set (Variety.Point H)) =
        (Set.univ : Set (Variety.Point (Variety.prod H H))) := by
      ext z
      simp [Variety.prodSet]
    rw [hprod] at hI
    exact hI.isConnected
  have hsubsingleton :=
    connected_finite_morphism_range_subsingleton defect hprodConnected
      hdefect_finite
  have hdefect_one (x y : Variety.Point H) :
      defect.toFun ((Variety.prodPointEquiv H H).symm (x, y)) = 1 := by
    have heq := hsubsingleton
      (Set.mem_range_self ((Variety.prodPointEquiv H H).symm (x, y)))
      (Set.mem_range_self ((Variety.prodPointEquiv H H).symm (1, 1)))
    rw [hdefect_apply, hdefect_apply] at heq
    calc
      defect.toFun ((Variety.prodPointEquiv H H).symm (x, y)) =
          qv.toFun (x * y) * (qv.toFun y)⁻¹ * (qv.toFun x)⁻¹ :=
        hdefect_apply x y
      _ = (qv.toFun 1)⁻¹ := by simpa using heq
      _ = 1 := by rw [hqone]; simp
  have hqmul (x y : Variety.Point H) :
      qv.toFun (x * y) = qv.toFun x * qv.toFun y := by
    have h := hdefect_one x y
    rw [hdefect_apply] at h
    apply mul_right_cancel (b := (qv.toFun y)⁻¹ * (qv.toFun x)⁻¹)
    simpa [mul_assoc] using h
  exact ⟨qv, hqsection, hqone, hqmul⟩

/-- A regular section of a finite-kernel morphism onto a connected target can
be normalized to an algebraic-group section. -/
public theorem Morphism.exists_sectionMorphism_of_finiteKernel_of_connected
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H)
    (hker : Finite f.kernel)
    (hH : Variety.IsConnected H)
    (s : Variety.Morphism H G)
    (hsection : ∀ x, f.onPoints (s.toFun x) = x) :
    ∃ q : AlgebraicGroup.Morphism H G,
      ∀ x, f.onPoints (q.onPoints x) = x := by
  obtain ⟨qv, hqsection, hqone, hqmul⟩ :=
    f.exists_normalized_sectionPointHom_of_finiteKernel_of_connected
      hker hH s hsection
  exact ⟨{ toVariety := qv, map_one := hqone, map_mul := hqmul }, hqsection⟩

/-- An injective algebraic-group morphism with a regular section has
surjective pullback on polynomial functions. -/
public lemma Morphism.pullbackRingHom_surjective_of_injective_of_section
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H)
    (hinjective : Function.Injective f.onPoints)
    (s : AlgebraicGroup.Morphism H G)
    (hsection : ∀ y, f.onPoints (s.onPoints y) = y) :
    Function.Surjective f.toVariety.pullbackRingHom := by
  have hleft : ∀ x, s.onPoints (f.onPoints x) = x := by
    intro x
    apply hinjective
    rw [hsection]
  intro q
  refine ⟨s.toVariety.pullbackRingHom q, ?_⟩
  apply Variety.PolynomialFunction.ext
  intro x
  change q (s.onPoints (f.onPoints x)) = q x
  rw [hleft]

/-- A split algebraic-group morphism from a connected source has connected
kernel. -/
public theorem Morphism.kernel_isConnected_of_section
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H) (s : AlgebraicGroup.Morphism H G)
    (hsection : ∀ y, f.onPoints (s.onPoints y) = y)
    (hG : Variety.IsConnected G) :
    Variety.IsConnected f.kernelClosedSubgroup.carrierVariety := by
  let K := f.kernelClosedSubgroup
  let r₀ : Variety.Morphism G G :=
    (AlgebraicGroup.mulMorphism G).comp
      ((Variety.Morphism.id G).pair
        ((AlgebraicGroup.invMorphism G).comp
          (s.toVariety.comp f.toVariety)))
  have r₀_apply (x : Variety.Point G) :
      r₀.toFun x = x * (s.onPoints (f.onPoints x))⁻¹ := by
    rfl
  have hr₀ (x : Variety.Point G) : r₀.toFun x ∈ K.toSubgroup := by
    change f.onPoints (r₀.toFun x) = 1
    calc
      f.onPoints (r₀.toFun x) =
          f.onPoints x * f.onPoints (s.onPoints (f.onPoints x))⁻¹ := by
        rw [r₀_apply]
        exact f.onPoints.map_mul _ _
      _ = f.onPoints x * (f.onPoints x)⁻¹ := by
        rw [f.onPoints.map_inv, hsection]
      _ = 1 := mul_inv_cancel _
  let r : Variety.Morphism G K.carrierVariety :=
    { toFun := fun x => K.pointEquiv.symm ⟨r₀.toFun x, hr₀ x⟩
      regular := by
        intro i
        rcases r₀.regular i with ⟨p, hp⟩
        refine ⟨p, fun x => ?_⟩
        change (K.pointEquiv (K.pointEquiv.symm
          ⟨r₀.toFun x, hr₀ x⟩)).val.val i = evalPolynomial x.val p
        rw [K.pointEquiv.apply_symm_apply]
        exact hp x }
  have hrsurj : Function.Surjective r.toFun := by
    intro z
    let x : Variety.Point G := K.inclusion.onPoints z
    refine ⟨x, ?_⟩
    apply K.inclusion_injective
    change r₀.toFun x = K.inclusion.onPoints z
    rw [r₀_apply]
    have hx : f.onPoints x = 1 := (K.pointEquiv z).property
    rw [hx, s.onPoints.map_one, inv_one, mul_one]
  let : ConnectedSpace (Variety.Point G) :=
    connectedSpace_iff_univ.mpr hG
  have hrange : _root_.IsConnected (Set.range r.toFun) :=
    isConnected_range r.continuous
  rw [Set.range_eq_univ.mpr hrsurj] at hrange
  exact hrange

end Theory.AlgebraicGroup
