module
public import Theory.Representation.OrthogonalFourPlusMatrix.Commutant
public import Theory.Representation.FirstCohomologyLinearTransport

/-!
# Semilinearity of an ambient action normalizing the determinant tensor

The full additive commutant of the two SL₂ factors is its coefficient field.
Conjugation by the original ambient action therefore constructs a field
automorphism, and uniqueness makes these automorphisms a homomorphism.
This includes factor interchanges and requires no whole-group identification.
Source application: Aschbacher–Smith G.11.7, printed pp.367–368.
-/

public noncomputable section
namespace ClassicalOrthogonal.FourPlusMatrix
open Matrix Subgroup
variable {F D : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] [Group D]

private theorem ambient_semilinear (L : Subgroup D) [L.Normal]
    (e : L ≃* PairSL (F := F))
    (ρ : Representation (ZMod 2) D (Mat (F := F)))
    (hnat : ∀ (g : L) v, ρ (g : D) v = matrixAction (e g) v)
    (h : D) : ∃ σ : F ≃+* F, ∀ (c : F) v,
      ρ h (c • v) = σ c • ρ h v := by
  let f (c : F) : Mat (F := F) →+ Mat (F := F) :=
    { toFun := fun v => ρ h (c • ρ h⁻¹ v)
      map_zero' := by simp
      map_add' := by intro v w; simp [smul_add] }
  have hf (c : F) : ∃ d : F, ∀ v, f c v = d • v := by
    apply centralizer_scalar
    intro g v
    let x : L := e.symm g
    let y : L := ⟨h⁻¹ * (x : D) * h, (inferInstance : L.Normal).conj_mem' x x.property h⟩
    have hx (v : Mat (F := F)) : matrixAction g v = ρ (x : D) v := by
      rw [hnat]
      simp [x]
    have hy (c : F) (v : Mat (F := F)) : ρ (y : D) (c • v) = c • ρ (y : D) v := by
      rw [hnat,hnat]
      exact (matrixAction (e y)).map_smul c v
    have hy₁ (v : Mat (F := F)) : ρ h⁻¹ (ρ (x : D) v) = ρ (y : D) (ρ h⁻¹ v) := by
      simp only [← Module.End.mul_apply, ← map_mul, y, mul_assoc, mul_inv_cancel, mul_one]
    have hy₂ (v : Mat (F := F)) : ρ h (ρ (y : D) v) = ρ (x : D) (ρ h v) := by
      simp only [← Module.End.mul_apply, ← map_mul, y, mul_assoc, mul_inv_cancel_left]
    change ρ h (c • ρ h⁻¹ (matrixAction g v)) = matrixAction g (ρ h (c • ρ h⁻¹ v))
    rw [hx,hx,hy₁,←hy,hy₂]
  let φ : F → F := fun c => f c (Matrix.single 0 0 1) 0 0
  have hφ (c : F) (v : Mat (F := F)) : f c v = φ c • v := by
    obtain ⟨d,hd⟩ := hf c
    have he : φ c = d := by simp [φ,hd,Matrix.single]
    exact he ▸ hd v
  have hcancel (v : Mat (F := F)) : ρ h (ρ h⁻¹ v) = v := by
    simp [← Module.End.mul_apply, ← map_mul]
  have hcancel' (v : Mat (F := F)) : ρ h⁻¹ (ρ h v) = v := by
    simp [← Module.End.mul_apply, ← map_mul]
  have hmul (a b : F) (v : Mat (F := F)) : f (a*b) v = f a (f b v) := by
    simp [f,hcancel',mul_smul]
  let φhom : F →+* F :=
    { toFun := φ
      map_one' := by simp [φ,f,hcancel,Matrix.single]
      map_mul' := by
        intro a b
        change f (a*b) (Matrix.single 0 0 1) 0 0 = φ a * φ b
        rw [hmul,hφ,hφ]
        simp [Matrix.single]
      map_zero' := by simp [φ,f]
      map_add' := by intro a b; simp [φ,f,add_smul] }
  refine ⟨RingEquiv.ofBijective φhom
    ⟨φhom.injective,Finite.surjective_of_injective φhom.injective⟩,fun c v => ?_⟩
  change ρ h (c • v) = φ c • ρ h v
  have he := hφ c (ρ h v)
  simpa only [f,AddMonoidHom.coe_mk,ZeroHom.coe_mk,hcancel',
    RingEquiv.ofBijective_apply,φhom,RingHom.coe_mk,MonoidHom.coe_mk,OneHom.coe_mk] using he

/-- The original ambient group acts on the actual coefficient field.
Its semilinear action includes elements interchanging the two components. -/
theorem normal_ambient_semilinear (L : Subgroup D) [L.Normal]
    (e : L ≃* PairSL (F := F))
    (ρ : Representation (ZMod 2) D (Mat (F := F)))
    (hnat : ∀ (g : L) v, ρ (g : D) v = matrixAction (e g) v) :
    ∃ φ : D →* (F ≃+* F), ∀ (h : D) (c : F) v,
      ρ h (c • v) = φ h c • ρ h v := by
  choose φ hφ using ambient_semilinear L e ρ hnat
  refine ⟨{toFun := φ, map_one' := ?_, map_mul' := ?_},hφ⟩
  · ext c
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Mat (F := F))
    intro v
    change φ 1 c • v = c • v
    simpa only [map_one,Module.End.one_apply] using (hφ 1 c v).symm
  · intro g h
    ext c
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Mat (F := F))
    intro v
    have hsurj : Function.Surjective (ρ (g*h)) := by
      intro w
      refine ⟨ρ (g*h)⁻¹ w,?_⟩
      simp only [← Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
    obtain ⟨w,rfl⟩ := hsurj v
    rw [←hφ,map_mul,Module.End.mul_apply,hφ,hφ]
    rfl
end ClassicalOrthogonal.FourPlusMatrix
