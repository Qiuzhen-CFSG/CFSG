module

public import Theory.AlgebraicGroup.Representations.Algebraic.Irreducible
public import Theory.LinearAlgebra.SemilinearTrace

/-!
# Simultaneous coefficient transport of rational actions

A coefficient action on a presented affine group records the actual action on
its coordinates. Conjugating a polynomial morphism by coefficient actions on
its source and target applies the field automorphism to its defining
polynomials. This proves rationality of the action obtained by semilinear
conjugation after the inverse coefficient action on the source group.
Invariant subspaces pull back along the semilinear equivalence, proving
irreducibility of the transported action.

This is the algebraic transport underlying GLS3, Remark 2.8.8. The concrete
F4 coefficient action is constructed separately in `Carrier`.
-/

public section

open Theory.AlgebraicGroup
namespace Theory.AlgebraicGroup.CoefficientTransport
universe u v
variable {F : Type u} [Field F]
noncomputable section
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- Conjugation of polynomial coordinate functions changes their coefficients. -/
theorem eval_map_coefficients (σ : F ≃+* F) {I : Type*}
    (x : I → F) (p : MvPolynomial I F) :
    evalPolynomial x (MvPolynomial.map (σ : F →+* F) p) =
      σ (evalPolynomial (fun i => σ.symm (x i)) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [evalPolynomial]
  | add p q hp hq => simp [evalPolynomial] at hp hq ⊢; rw [hp, hq]
  | mul_X p i hp => simp [evalPolynomial] at hp ⊢; simp [hp]

/-- A coefficient action on a presented algebraic group records its actual
coordinate action, not merely an abstract group automorphism. -/
structure CoefficientAction (σ : F ≃+* F) (G : Variety F) [AlgebraicGroup G] where
  equiv : Variety.Point G ≃* Variety.Point G
  coordinate : ∀ (g : Variety.Point G) (i : G.Coordinates),
    (equiv g).val i = σ (g.val i)

theorem CoefficientAction.symm_coordinate {σ : F ≃+* F} {G : Variety F}
    [AlgebraicGroup G] (a : CoefficientAction σ G) (g : Variety.Point G)
    (i : G.Coordinates) : (a.equiv.symm g).val i = σ.symm (g.val i) := by
  apply σ.injective
  rw [← a.coordinate, a.equiv.apply_symm_apply, σ.apply_symm_apply]

/-- Simultaneously change the input and output coefficients of a polynomial
morphism. The inverse action on the input is essential. -/
def conjugateMorphism {σ : F ≃+* F} {G H : Variety F}
    [AlgebraicGroup G] [AlgebraicGroup H]
    (a : CoefficientAction σ G) (b : CoefficientAction σ H)
    (f : Theory.AlgebraicGroup.Morphism G H) : Theory.AlgebraicGroup.Morphism G H where
  toVariety :=
    { toFun := fun g => b.equiv (f.onPoints (a.equiv.symm g))
      regular := by
        intro i
        obtain ⟨p, hp⟩ := f.toVariety.regular i
        refine ⟨MvPolynomial.map (σ : F →+* F) p, ?_⟩
        intro g
        rw [b.coordinate, eval_map_coefficients]
        change σ ((f.toVariety.toFun (a.equiv.symm g)).val i) = _
        rw [hp]
        congr 2
        funext j
        exact a.symm_coordinate g j }
  map_one := by simp
  map_mul := by intros; simp

/-- Applying a field automorphism to matrix entries, on the actual GL points. -/
def glCoefficientAction [IsAlgClosed F] (σ : F ≃+* F) (n : ℕ) :
    CoefficientAction σ (glVariety n : Variety F) where
  equiv := (translationGLPointMulEquiv n).trans
    ((Units.mapEquiv σ.mapMatrix.toMulEquiv).trans (translationGLPointMulEquiv n).symm)
  coordinate := by
    intro g i
    cases i with
    | inl ij =>
      change σ ((glMatrixOfPoint n g) ij.1 ij.2) = σ (g.val (Sum.inl ij))
      rfl
    | inr i =>
      change ((glMatrixOfPoint n g).map (σ : F →+* F)).det⁻¹ = σ (g.val (Sum.inr i))
      change ((σ : F →+* F).mapMatrix (glMatrixOfPoint n g)).det⁻¹ = _
      rw [← RingHom.map_det, ← map_inv₀]
      exact congrArg σ (glScalarOfPoint_eq_inv_det n g).symm

variable {V : Type v} [AddCommGroup V] [Module F V]

/-- The semilinear map applying σ to coordinates in a fixed basis. -/
def basisCoefficientEquiv {I : Type*} [Fintype I] (σ : F ≃+* F)
    (b : Module.Basis I F V) :
    LinearEquiv (σ' := (σ.symm : F →+* F)) (σ : F →+* F) V V where
  toFun v := b.equivFun.symm (fun i => σ (b.equivFun v i))
  invFun v := b.equivFun.symm (fun i => σ.symm (b.equivFun v i))
  left_inv v := by
    simp only [LinearEquiv.apply_symm_apply, RingEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  right_inv v := by
    simp only [LinearEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  map_add' v w := by
    apply b.equivFun.injective
    simp only [LinearEquiv.apply_symm_apply, map_add, Pi.add_apply]
    rfl
  map_smul' a v := by
    apply b.equivFun.injective
    ext i
    simp only [map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul, map_mul, RingHom.coe_coe]

@[simp] theorem basisCoefficientEquiv_coord {I : Type*} [Fintype I]
    (σ : F ≃+* F) (b : Module.Basis I F V) (v : V) (i : I) :
    b.repr (basisCoefficientEquiv σ b v) i = σ (b.repr v i) := by
  change b.equivFun (b.equivFun.symm _) i = _
  exact congrFun (b.equivFun.apply_symm_apply _) i

@[simp] theorem basisCoefficientEquiv_basis {I : Type*} [Fintype I]
    (σ : F ≃+* F) (b : Module.Basis I F V) (i : I) :
    basisCoefficientEquiv σ b (b i) = b i := by
  classical
  apply b.repr.injective
  ext j
  simp [Module.Basis.repr_self, Finsupp.single_apply, apply_ite σ]

/-- Conjugate the vector coefficients and precompose by the inverse group
coefficient action. -/
def twistAction {G : Variety F} [AlgebraicGroup G]
    (σ : F ≃+* F) (γ : Variety.Point G ≃* Variety.Point G)
    (ρ : RationalRepresentation G V)
    (e : LinearEquiv (σ' := (σ.symm : F →+* F)) (σ : F →+* F) V V) :
    RationalRepresentation G V where
  action := (Units.map e.conjRingEquiv.toMonoidHom).comp
    (ρ.action.comp γ.symm.toMonoidHom)

@[simp] theorem twistAction_apply {G : Variety F} [AlgebraicGroup G]
    (σ : F ≃+* F) (γ : Variety.Point G ≃* Variety.Point G)
    (ρ : RationalRepresentation G V)
    (e : LinearEquiv (σ' := (σ.symm : F →+* F)) (σ : F →+* F) V V)
    (g : Variety.Point G) (v : V) :
    ((twistAction σ γ ρ e).action g : Module.End F V) (e v) =
      e ((ρ.action (γ.symm g) : Module.End F V) v) := by
  change e ((ρ.action (γ.symm g) : Module.End F V) (e.symm (e v))) = _
  rw [e.symm_apply_apply]


variable [IsAlgClosed F] [FiniteDimensional F V]

theorem glPointEquivOf_coefficient (σ : F ≃+* F)
    (b : Module.Basis (Fin (Module.finrank F V)) F V)
    (x : Variety.Point (glVarietyOf F V)) :
    glPointEquivOf F V b ((glCoefficientAction σ _).equiv x) =
      Units.map (basisCoefficientEquiv σ b).conjRingEquiv.toMonoidHom
        (glPointEquivOf F V b x) := by
  apply Units.ext
  apply b.ext
  intro j
  apply b.equivFun.injective
  ext i
  erw [glPointEquivOf_apply_basis V b _ j]
  rw [LinearEquiv.apply_symm_apply]
  change ((glCoefficientAction σ _).equiv x).val (Sum.inl (i, j)) =
    b.repr (basisCoefficientEquiv σ b
      ((glPointEquivOf F V b x : Module.End F V)
        ((basisCoefficientEquiv σ b).symm (b j)))) i
  erw [(glCoefficientAction σ _).coordinate]
  rw [basisCoefficientEquiv_coord]
  have hb : (basisCoefficientEquiv σ b).symm (b j) = b j := by
    apply (basisCoefficientEquiv σ b).injective
    rw [LinearEquiv.apply_symm_apply, basisCoefficientEquiv_basis]
  rw [hb, glPointEquivOf_apply_basis V b x j]
  change σ (x.val (Sum.inl (i, j))) =
    σ (b.equivFun (b.equivFun.symm _) i)
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Rationality is proved by conjugating the polynomial coordinate morphism. -/
theorem twistAction_rational {G : Variety F} [AlgebraicGroup G]
    (σ : F ≃+* F) (a : CoefficientAction σ G)
    (ρ : RationalRepresentation G V)
    (b : Module.Basis (Fin (Module.finrank F V)) F V)
    (f : Theory.AlgebraicGroup.Morphism G (glVarietyOf F V))
    (hf : ∀ g, glPointEquivOf F V b (f.onPoints g) = ρ.action g) :
    IsRationalRepresentation (twistAction σ a.equiv ρ (basisCoefficientEquiv σ b)) := by
  refine ⟨b, conjugateMorphism a (glCoefficientAction σ _) f, ?_⟩
  intro g
  change glPointEquivOf F V b
    ((glCoefficientAction σ _).equiv (f.onPoints (a.equiv.symm g))) = _
  rw [glPointEquivOf_coefficient, hf]
  rfl

omit [IsAlgClosed F] [FiniteDimensional F V] in
/-- Invariant subspaces pull back along the semilinear equivalence. -/
theorem twistAction_irreducible {G : Variety F} [AlgebraicGroup G]
    (σ : F ≃+* F) (γ : Variety.Point G ≃* Variety.Point G)
    (ρ : RationalRepresentation G V)
    (e : LinearEquiv (σ' := (σ.symm : F →+* F)) (σ : F →+* F) V V)
    (hρ : IsAlgebraicallyIrreducibleRepresentation ρ) :
    IsAlgebraicallyIrreducibleRepresentation (twistAction σ γ ρ e) := by
  intro W hW
  have hU : IsInvariantSubmodule ρ (W.comap e.toLinearMap) := by
    intro g v hv
    change e ((ρ.action g : Module.End F V) v) ∈ W
    have h := hW (γ g) (e v) hv
    rw [twistAction_apply, γ.symm_apply_apply] at h
    exact h
  rcases hρ (W.comap e.toLinearMap) hU with hbot | htop
  · left
    apply eq_bot_iff.mpr
    intro w hw
    have h : e.symm w ∈ W.comap e.toLinearMap := by
      change e (e.symm w) ∈ W
      simpa only [e.apply_symm_apply] using hw
    rw [hbot, Submodule.mem_bot] at h
    rw [Submodule.mem_bot]
    exact e.symm.injective (h.trans (map_zero _).symm)
  · right
    apply top_unique
    intro w _
    have h : e.symm w ∈ W.comap e.toLinearMap := by rw [htop]; trivial
    change e (e.symm w) ∈ W at h
    simpa only [e.apply_symm_apply] using h

end
end Theory.AlgebraicGroup.CoefficientTransport
