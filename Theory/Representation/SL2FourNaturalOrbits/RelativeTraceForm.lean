module

public import Theory.Representation.SL2FourNaturalOrbits.SelfDual
public import Theory.Representation.SL2NaturalOffenders.Semilinear

/-!
# Choosing the relative trace form without changing the natural actors

Every invariant binary bilinear form on the field-natural SL₂(4) module is
a trace-determinant form. A nonzero scalar change of the natural coordinates
can give any specified nonzero trace coefficient, while commuting with every
original SL₂(4) actor and preserving the upper fixed plane.
-/

@[expose] public section
noncomputable section
namespace Representation.SL2FourNatural

private theorem pairing_equivariant
    (B : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V)
    (hB : ∀ g v w, B (action g v) (action g w) = B v w)
    (g : SL) (v w : V) : B (action g v) w = B v (action g⁻¹ w) := by
  have h := hB g v (action g⁻¹ w)
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h
  exact h

/-- The coefficient of an invariant binary form is an actual element of the
original field of four elements. No change of the SL₂ marking is required. -/
theorem invariant_binary_form_eq_trace
    (B : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V)
    (hB : ∀ g v w, B (action g v) (action g w) = B v w) :
    ∃ c : F, ∀ v w, B v w = QuadraticAlgebra.trace (c * wedge v w) := by
  let f : V →ₗ[ZMod 2] V := selfDual.symm.toLinearMap.comp B
  have hf (g : SL) (v : V) : f (action g v) = action g (f v) := by
    apply selfDual.injective
    apply LinearMap.ext
    intro w
    change selfDual (selfDual.symm (B (action g v))) w = selfDual (action g (f v)) w
    rw [LinearEquiv.apply_symm_apply, selfDual_equivariant]
    change B (action g v) w = selfDual (selfDual.symm (B v)) (action g⁻¹ w)
    rw [LinearEquiv.apply_symm_apply]
    exact pairing_equivariant B hB g v w
  obtain ⟨c,hc⟩ := SL2NaturalOffenders.centralizer_scalar f.toAddMonoidHom hf
  refine ⟨c, fun v w => ?_⟩
  have he := congrArg (fun z : V => selfDual z w) (hc v)
  change selfDual (selfDual.symm (B v)) w = binaryPairing (c • v) w at he
  rw [LinearEquiv.apply_symm_apply, binaryPairing_apply] at he
  rw [he]
  congr 1
  simp only [wedge, Pi.smul_apply, smul_eq_mul]
  ring

/-- Scalar coordinate changes commute with every original natural actor. -/
def scalarCoordinates (c : F) (hc : c ≠ 0) : V ≃ₗ[ZMod 2] V :=
  (LinearEquiv.smulOfNeZero F V c hc : V ≃ₗ[F] V).restrictScalars (ZMod 2)

theorem scalarCoordinates_apply (c : F) (hc : c ≠ 0) (v : V) :
    scalarCoordinates c hc v = c • v := rfl

theorem scalarCoordinates_action (c : F) (hc : c ≠ 0) (g : SL) (v : V) :
    scalarCoordinates c hc (action g v) = action g (scalarCoordinates c hc v) := by
  exact (Matrix.SpecialLinearGroup.toLin' g).map_smul c v |>.symm

theorem scalarCoordinates_upperFixed (c : F) (hc : c ≠ 0) :
    upperFixed.map (scalarCoordinates c hc).toLinearMap = upperFixed := by
  ext v
  constructor
  · rintro ⟨w,hw,rfl⟩
    change w ∈ upperFixed at hw
    rw [mem_upperFixed] at hw ⊢
    change c * w 1 = 0
    rw [hw,mul_zero]
  · intro hv
    refine ⟨(scalarCoordinates c hc).symm v,?_,by simp⟩
    have he := congrFun ((scalarCoordinates c hc).apply_symm_apply v) 1
    change (scalarCoordinates c hc).symm v ∈ upperFixed
    rw [mem_upperFixed] at hv ⊢
    change c * ((scalarCoordinates c hc).symm v) 1 = v 1 at he
    exact (mul_eq_zero.mp (he.trans hv)).resolve_left hc

/-- Any prescribed nonzero trace coefficient is attained by scalar natural
coordinates. The chosen coordinates retain every actor and the exact upper
fixed plane; only the relative form coefficient changes. -/
theorem exists_scalar_coordinates_for_trace
    (B : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V) (hB0 : B ≠ 0)
    (hB : ∀ g v w, B (action g v) (action g w) = B v w)
    (d : F) (hd : d ≠ 0) :
    ∃ e : V ≃ₗ[ZMod 2] V,
      (∀ g v, e (action g v) = action g (e v)) ∧
      upperFixed.map e.toLinearMap = upperFixed ∧
      ∀ v w, B (e v) (e w) = QuadraticAlgebra.trace (d * wedge v w) := by
  obtain ⟨c,hc⟩ := invariant_binary_form_eq_trace B hB
  have hc0 : c ≠ 0 := by
    intro he
    apply hB0
    ext v w
    simp [hc,he]
  have hs : ∀ c d : F, c ≠ 0 → d ≠ 0 → ∃ a : F, a ≠ 0 ∧ c * a ^ 2 = d := by
    decide +kernel
  obtain ⟨a,ha0,ha⟩ := hs c d hc0 hd
  refine ⟨scalarCoordinates a ha0,scalarCoordinates_action a ha0,
    scalarCoordinates_upperFixed a ha0,fun v w => ?_⟩
  rw [hc]
  congr 1
  rw [scalarCoordinates_apply,scalarCoordinates_apply]
  calc
    c * wedge (a • v) (a • w) = (c * a ^ 2) * wedge v w := by
      simp only [wedge,Pi.smul_apply,smul_eq_mul]
      ring
    _ = d * wedge v w := by rw [ha]

/-- An existing natural marking can be chosen with a prescribed relative
trace form. Every literal actor is retained, as is the image of the upper
fixed plane. This applies before choosing lifts in an endpoint extension. -/
theorem exists_equivariant_marking_for_trace
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (e : V ≃ₗ[ZMod 2] M)
    (ρ : SL →* (M ≃ₗ[ZMod 2] M))
    (he : ∀ g v, ρ g (e v) = e (action g v))
    (B : M →ₗ[ZMod 2] Module.Dual (ZMod 2) M) (hB0 : B ≠ 0)
    (hB : ∀ g v w, B (ρ g v) (ρ g w) = B v w)
    (d : F) (hd : d ≠ 0) :
    ∃ e' : V ≃ₗ[ZMod 2] M,
      (∀ g v, ρ g (e' v) = e' (action g v)) ∧
      upperFixed.map e'.toLinearMap = upperFixed.map e.toLinearMap ∧
      ∀ v w, B (e' v) (e' w) = QuadraticAlgebra.trace (d * wedge v w) := by
  let C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V :=
    B.compl₁₂ e.toLinearMap e.toLinearMap
  have hC0 : C ≠ 0 := by
    intro hz
    apply hB0
    ext v w
    obtain ⟨v,rfl⟩ := e.surjective v
    obtain ⟨w,rfl⟩ := e.surjective w
    exact congrArg (fun C : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V => C v w) hz
  have hC : ∀ g v w, C (action g v) (action g w) = C v w := by
    intro g v w
    change B (e (action g v)) (e (action g w)) = B (e v) (e w)
    rw [←he,←he,hB]
  obtain ⟨a,ha,hplane,hform⟩ := exists_scalar_coordinates_for_trace C hC0 hC d hd
  refine ⟨a.trans e,?_,?_,hform⟩
  · intro g v
    change ρ g (e (a v)) = e (a (action g v))
    rw [he,ha]
  · change upperFixed.map (e.toLinearMap.comp a.toLinearMap) = _
    rw [Submodule.map_comp,hplane]

end Representation.SL2FourNatural
