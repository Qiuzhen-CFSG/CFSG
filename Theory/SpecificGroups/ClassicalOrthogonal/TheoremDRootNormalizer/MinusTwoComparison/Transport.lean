module

public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.ScalarQuotients
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.GroupTheory.Index

/-!
# Field transport of the genuine binary minus orthogonal groups

The chosen anisotropic-plane parameters need not be preserved by a field
isomorphism. Over a finite field of characteristic two the additive map
`x ↦ x² + x` has kernel `{0, 1}`, so its image has index two. Any two
parameters outside that image therefore differ by `t² + t`. The shear
`(x, y) ↦ (x + t*y, y)` identifies their full quadratic forms. Extending it
by the identity on the hyperbolic coordinates after coefficient transport
gives an actual semilinear isometry between the chosen minus spaces.

Conjugation then identifies their full orthogonal groups and their commutator
subgroups. The characteristic-two scalar-kernel theorem transports the literal
projective quotients, with the quotient-map equation proved explicitly.
`MinusTwoComparison.lean` applies this transport to the Hermitian fixed-field
construction of the minus-four/PSL₂ equivalence.

Sources: GLS3 §2.7 (`refs/KGroup/GLS3/chapter2.tex`), for the quadratic forms,
commutator and scalar-quotient conventions; Aschbacher–Smith I.1.6(3), printed
p.408 (`refs/quasithin.pdf`), for the minus-four comparison.
-/

public noncomputable section

namespace ClassicalOrthogonal.TheoremDRootNormalizer.MinusTwoComparison
open ClassicalOrthogonal.Minus
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]

private theorem exists_parameter_shift [Finite K] [CharP K 2]
    (a b : K) (ha : ∀ x : K, x ^ 2 + x ≠ a) (hb : ∀ x : K, x ^ 2 + x ≠ b) :
    ∃ t : K, t ^ 2 + t = a + b := by
  let f : K →+ K :=
    { toFun := fun x => x ^ 2 + x
      map_zero' := by simp
      map_add' := fun x y => by simp only [CharTwo.add_sq]; ring }
  have hk : Nat.card f.ker = 2 := by
    apply (Nat.card_eq_two_iff' (0 : f.ker)).mpr
    refine ⟨⟨1, by simp [f, CharTwo.add_self_eq_zero]⟩, ?_, ?_⟩
    · intro h
      exact one_ne_zero (congrArg Subtype.val h)
    · intro y hy
      apply Subtype.ext
      have hy0 : (y : K) ≠ 0 := by
        intro h
        exact hy (Subtype.ext h)
      have hp : (y : K) * ((y : K) + 1) = 0 := by
        have h : (y : K) ^ 2 + (y : K) = 0 := y.property
        linear_combination h
      exact CharTwo.add_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hy0)
  have hi : f.range.index = 2 := AddSubgroup.index_range.trans hk
  have ha' : a ∉ f.range := by
    rintro ⟨x, hx⟩
    exact ha x hx
  have hb' : b ∉ f.range := by
    rintro ⟨x, hx⟩
    exact hb x hx
  exact (AddSubgroup.add_mem_iff_of_index_two hi).mpr (by simp [ha', hb'])

/-- Apply the field isomorphism to every hyperbolic and anisotropic coordinate. -/
def spaceCoefficientEquiv (σ : F ≃+* K) (m : ℕ) :
    Space F m ≃ₛₗ[(σ : F →+* K)] Space K m where
  toFun x := ((fun i => (σ (x.1 i).1, σ (x.1 i).2)), (σ x.2.1, σ x.2.2))
  invFun x := ((fun i => (σ.symm (x.1 i).1, σ.symm (x.1 i).2)),
    (σ.symm x.2.1, σ.symm x.2.2))
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp [smul_eq_mul]

/-- Coefficient transport preserves the full quadratic value, with its parameter transported too. -/
@[simp] theorem form_spaceCoefficientEquiv (σ : F ≃+* K) (m : ℕ)
    (a : F) (x : Space F m) :
    form K m (σ a) (spaceCoefficientEquiv σ m x) = σ (form F m a x) := by
  simp [spaceCoefficientEquiv, form_apply, plane_apply, map_sum]

private def planeShear (t : K) : (K × K) ≃ₗ[K] (K × K) where
  toFun x := (x.1 + t * x.2, x.2)
  invFun x := (x.1 - t * x.2, x.2)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_add' x y := by ext <;> simp; ring
  map_smul' c x := by ext <;> simp [smul_eq_mul]; ring

/-- A shear of the final plane identifies parameters differing by an Artin–Schreier value. -/
def formShiftIsometry [CharP K 2] (m : ℕ) (a b t : K)
    (ht : t ^ 2 + t = a + b) : (form K m a).IsometryEquiv (form K m b) where
  toLinearEquiv := (LinearEquiv.refl K (Fin m → K × K)).prodCongr (planeShear t)
  map_app' x := by
    have ht' : t ^ 2 + t + b = a := by
      rw [ht, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    simp only [form_apply]
    congr 1
    simp only [plane_apply]
    change (x.2.1 + t * x.2.2) ^ 2 + (x.2.1 + t * x.2.2) * x.2.2 -
      b * x.2.2 ^ 2 = x.2.1 ^ 2 + x.2.1 * x.2.2 - a * x.2.2 ^ 2
    simp only [CharTwo.sub_eq_add, CharTwo.add_sq]
    calc
      _ = x.2.1 ^ 2 + x.2.1 * x.2.2 + (t ^ 2 + t + b) * x.2.2 ^ 2 := by ring
      _ = _ := by rw [ht']

private theorem exists_mapped_parameter_shift [Finite F] [Finite K] [CharP K 2]
    (σ : F ≃+* K) : ∃ t : K, t ^ 2 + t = σ (parameter F) + parameter K := by
  apply exists_parameter_shift _ _ _ (parameter_spec K)
  intro x hx
  apply parameter_spec F (σ.symm x)
  apply σ.injective
  simpa only [map_add, map_pow, σ.apply_symm_apply] using hx

private def parameterShift [Finite F] [Finite K] [CharP K 2] (σ : F ≃+* K) : K :=
  (exists_mapped_parameter_shift σ).choose

private theorem parameterShift_spec [Finite F] [Finite K] [CharP K 2] (σ : F ≃+* K) :
    parameterShift σ ^ 2 + parameterShift σ = σ (parameter F) + parameter K :=
  (exists_mapped_parameter_shift σ).choose_spec

/-- A semilinear equivalence of the independently chosen minus spaces.
The shear corrects the discrepancy between their anisotropic-plane parameters. -/
def minusSpaceEquiv [Finite F] [Finite K] [CharP K 2] (σ : F ≃+* K) (r : ℕ) :
    Space F (r - 1) ≃ₛₗ[(σ : F →+* K)] Space K (r - 1) :=
  (spaceCoefficientEquiv σ (r - 1)).trans
    (formShiftIsometry (r - 1) (σ (parameter F)) (parameter K) (parameterShift σ)
      (parameterShift_spec σ)).toLinearEquiv

/-- The chosen coordinate comparison preserves quadratic values across the field isomorphism. -/
@[simp] theorem quadraticForm_minusSpaceEquiv [Finite F] [Finite K] [CharP K 2]
    (σ : F ≃+* K) (r : ℕ) (x : Space F (r - 1)) :
    quadraticForm K r (minusSpaceEquiv σ r x) = σ (quadraticForm F r x) := by
  change form K (r - 1) (parameter K)
    ((formShiftIsometry (r - 1) (σ (parameter F)) (parameter K) (parameterShift σ)
      (parameterShift_spec σ)) (spaceCoefficientEquiv σ (r - 1) x)) = _
  rw [QuadraticMap.IsometryEquiv.map_app, form_spaceCoefficientEquiv]
  rfl

variable {V : Type u} {W : Type v} [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module K W] {Q : QuadraticForm F V} {R : QuadraticForm K W}

/-- Conjugation by a semilinear isometry identifies the full quadratic-isometry groups. -/
def orthogonalSemilinearCongr (σ : F ≃+* K) (e : V ≃ₛₗ[(σ : F →+* K)] W)
    (he : ∀ x, R (e x) = σ (Q x)) :
    Orthogonal F V Q ≃* Orthogonal K W R where
  toFun g := ⟨e.symm.trans (g.val.trans e), by
    apply (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mpr
    intro w
    change R (e (g.val (e.symm w))) = R w
    rw [he, (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mp g.property,
      ← he, e.apply_symm_apply]⟩
  invFun g := ⟨e.trans (g.val.trans e.symm), by
    apply (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mpr
    intro x
    apply σ.injective
    change σ (Q (e.symm (g.val (e x)))) = σ (Q x)
    rw [← he, e.apply_symm_apply,
      (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mp g.property, he]⟩
  left_inv g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change e.symm (e (g.val (e.symm (e x)))) = g.val x
    simp
  right_inv g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    change e (e.symm (g.val (e (e.symm w)))) = g.val w
    simp
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    change e (g.val (h.val (e.symm w))) = e (g.val (e.symm (e (h.val (e.symm w)))))
    simp

/-- The transported isometry acts on the transported vector by the original action. -/
@[simp] theorem orthogonalSemilinearCongr_apply (σ : F ≃+* K)
    (e : V ≃ₛₗ[(σ : F →+* K)] W) (he : ∀ x, R (e x) = σ (Q x))
    (g : Orthogonal F V Q) (x : V) :
    (orthogonalSemilinearCongr σ e he g).val (e x) = e (g.val x) := by
  change e (g.val (e.symm (e x))) = _
  rw [e.symm_apply_apply]

/-- The full orthogonal commutator is carried onto the full orthogonal commutator. -/
theorem map_commutator_orthogonalSemilinearCongr (σ : F ≃+* K)
    (e : V ≃ₛₗ[(σ : F →+* K)] W) (he : ∀ x, R (e x) = σ (Q x)) :
    (commutator (Orthogonal F V Q)).map
      (orthogonalSemilinearCongr σ e he).toMonoidHom = commutator (Orthogonal K W R) := by
  rw [map_commutator_eq,
    MonoidHom.range_eq_top.mpr (orthogonalSemilinearCongr σ e he).surjective, ← commutator_def]

/-- The equivalence induced on the literal commutator subgroups. -/
def omegaSemilinearCongr (σ : F ≃+* K) (e : V ≃ₛₗ[(σ : F →+* K)] W)
    (he : ∀ x, R (e x) = σ (Q x)) : Omega F V Q ≃* Omega K W R :=
  ((orthogonalSemilinearCongr σ e he).subgroupMap (commutator (Orthogonal F V Q))).trans
    (MulEquiv.subgroupCongr (map_commutator_orthogonalSemilinearCongr σ e he))

/-- Commutator transport intertwines the literal natural actions. -/
@[simp] theorem omegaSemilinearCongr_apply (σ : F ≃+* K)
    (e : V ≃ₛₗ[(σ : F →+* K)] W) (he : ∀ x, R (e x) = σ (Q x))
    (g : Omega F V Q) (x : V) :
    (omegaSemilinearCongr σ e he g).val.val (e x) = e (g.val.val x) :=
  orthogonalSemilinearCongr_apply σ e he g.val x

/-- Field transport for the chosen minus-form commutator groups. -/
def minusOmegaFieldEquiv [Finite F] [Finite K] [CharP K 2] (σ : F ≃+* K) (r : ℕ) :
    Omega F (Space F (r - 1)) (quadraticForm F r) ≃*
      Omega K (Space K (r - 1)) (quadraticForm K r) :=
  omegaSemilinearCongr σ (minusSpaceEquiv σ r) (quadraticForm_minusSpaceEquiv σ r)

/-- The chosen minus-group comparison respects its semilinear coordinate comparison. -/
@[simp] theorem minusOmegaFieldEquiv_apply [Finite F] [Finite K] [CharP K 2]
    (σ : F ≃+* K) (r : ℕ) (g : Omega F (Space F (r - 1)) (quadraticForm F r))
    (x : Space F (r - 1)) :
    (minusOmegaFieldEquiv σ r g).val.val (minusSpaceEquiv σ r x) =
      minusSpaceEquiv σ r (g.val.val x) :=
  omegaSemilinearCongr_apply σ (minusSpaceEquiv σ r) (quadraticForm_minusSpaceEquiv σ r) g x

/-- Field transport through the literal scalar quotients.
Their scalar kernels are trivial in characteristic two. -/
def minusProjectiveFieldEquiv [Finite F] [Finite K] [CharP F 2] [CharP K 2]
    (σ : F ≃+* K) (r : ℕ) : ClassicalGroup.POmegaMinus r F ≃* ClassicalGroup.POmegaMinus r K :=
  (minusOmegaEquivProjective r).symm.trans
    ((minusOmegaFieldEquiv σ r).trans (minusOmegaEquivProjective r))

/-- The projective transport commutes with the actual quotient maps. -/
@[simp] theorem minusProjectiveFieldEquiv_apply [Finite F] [Finite K] [CharP F 2] [CharP K 2]
    (σ : F ≃+* K) (r : ℕ) (g : Omega F (Space F (r - 1)) (quadraticForm F r)) :
    minusProjectiveFieldEquiv σ r (QuotientGroup.mk g) =
      QuotientGroup.mk (minusOmegaFieldEquiv σ r g) := by
  change minusProjectiveFieldEquiv σ r (minusOmegaEquivProjective r g) =
    minusOmegaEquivProjective r (minusOmegaFieldEquiv σ r g)
  simp only [minusProjectiveFieldEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

end ClassicalOrthogonal.TheoremDRootNormalizer.MinusTwoComparison
