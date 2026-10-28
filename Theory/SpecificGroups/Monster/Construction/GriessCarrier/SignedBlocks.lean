module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.Core
public import Theory.SpecificGroups.Monster.Construction.GriessCarrier.TensorBlocks

/-!
# Descent of the mixed blocks through the signed short-vector relations

The existing signed-vector basis extends any sign-compatible coefficient
family uniquely to a linear map. Symmetry of bilinear coefficients survives
this extension. Applying this to the diagonal short-tensor coefficients
constructs the `S,R,R` block with exactly the normalized source pairing.
Applying it to the tensor coefficients constructs the `R,W,W` block and
proves its descent and symmetry.

The signed set, source short tensors and spin action are explicit inputs.
The final Griess carrier must instantiate them using the fixed Leech
comparison and the descended extraspecial action. No second short-lift
space or lattice comparison is introduced here.

Source: Aschbacher, *Sporadic Groups*, the signed module before 27.8,
equations 28.2 and 28.6, and Lemmas 28.9 and 28.11, pp. 150–153.
-/

@[expose] public section

noncomputable section
namespace Sporadic.Monster.Construction.Griess
open TrialitySpin.SignedModules

section
variable {X M : Type*} [Finite X] [AddCommGroup M] [Module ℝ M]

/-- Extend values from one element of each signed pair using the existing
signed-vector basis. The sign law is proved separately, rather than assumed
as an algebra structure. -/
def signedExtension (s : SignedSet X) (f : X → M) : s.Space →ₗ[ℝ] M :=
  s.basis.constr ℝ (fun a => f a.out)

@[simp] theorem signedExtension_basis (s : SignedSet X) (f : X → M)
    (a : s.toPairing.Orbit) : signedExtension s f (s.basis a) = f a.out :=
  s.basis.constr_basis ℝ _ a

/-- The extension has the prescribed value at every signed vector, precisely
when the values respect the negative-pair relation. -/
theorem signedExtension_delta (s : SignedSet X) (f : X → M)
    (hf : ∀ x, f (s.flip x) = -f x) (x : X) :
    signedExtension s f (s.delta x) = f x := by
  have hout : s.toPairing.orbit x = s.toPairing.orbit (s.toPairing.orbit x).out :=
    (Quotient.out_eq _).symm
  rcases (s.toPairing.orbit_eq _ _).mp hout with h | h
  · calc
      signedExtension s f (s.delta x) =
          signedExtension s f (s.delta (s.toPairing.orbit x).out) :=
        congrArg (fun y => signedExtension s f (s.delta y)) h
      _ = f (s.toPairing.orbit x).out := by
        rw [← s.basis_eq_delta, signedExtension_basis]
      _ = f x := congrArg f h.symm
  · calc
      signedExtension s f (s.delta x) =
          signedExtension s f (s.delta (s.flip (s.toPairing.orbit x).out)) :=
        congrArg (fun y => signedExtension s f (s.delta y)) h
      _ = -f (s.toPairing.orbit x).out := by
        rw [s.delta_flip, map_neg, ← s.basis_eq_delta, signedExtension_basis]
      _ = f x := (hf _).symm.trans (congrArg f h.symm)

theorem signedExtension_unique (s : SignedSet X) (f : X → M)
    (L : s.Space →ₗ[ℝ] M) (hL : ∀ x, L (s.delta x) = f x) :
    L = signedExtension s f := by
  apply s.basis.ext
  intro a
  rw [signedExtension_basis, s.basis_eq_delta, hL]

/-- A family of symmetric bilinear coefficients remains symmetric after
linear extension through the signed-vector relations. -/
theorem signedExtension_symmetric {W : Type*} [AddCommGroup W] [Module ℝ W]
    (s : SignedSet X) (f : X → LinearMap.BilinForm ℝ W)
    (hf : ∀ x v w, f x v w = f x w v) (a : s.Space) (v w : W) :
    signedExtension s f a v w = signedExtension s f a w v := by
  have h : signedExtension s f =
      LinearMap.lflip.toLinearMap.comp (signedExtension s f) := by
    apply s.basis.ext
    intro i
    ext v w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.lflip_apply,
      LinearMap.flip_apply, signedExtension_basis]
    exact hf i.out v w
  exact congrArg (fun L : s.Space →ₗ[ℝ] LinearMap.BilinForm ℝ W => L a v w) h

/-- The diagonal source action `A*y(r) = gamma_S(A,t(r))*y(r)`,
where `t` will be the already constructed short tensor. -/
def signedDiagonalAction (s : SignedSet X) (t : X → SymmetricPart) :
    SymmetricPart →ₗ[ℝ] s.Space →ₗ[ℝ] s.Space where
  toFun A := signedExtension s (fun x => symmetricGammaForm A (t x) • s.delta x)
  map_add' A B := by
    apply s.basis.ext
    intro i
    simp only [map_add, LinearMap.add_apply, signedExtension_basis, add_smul]
  map_smul' c A := by
    apply s.basis.ext
    intro i
    simp only [LinearMap.smul_apply, signedExtension_basis, RingHom.id_apply,
      map_smul, smul_smul, smul_eq_mul]

@[simp] theorem signedDiagonalAction_basis (s : SignedSet X) (t : X → SymmetricPart)
    (A : SymmetricPart) (i : s.toPairing.Orbit) :
    signedDiagonalAction s t A (s.basis i) =
      symmetricGammaForm A (t i.out) • s.basis i := by
  change signedExtension s (fun x => symmetricGammaForm A (t x) • s.delta x) (s.basis i) = _
  rw [signedExtension_basis, s.basis_eq_delta]

theorem signedDiagonalAction_delta (s : SignedSet X) (t : X → SymmetricPart)
    (ht : ∀ x, t (s.flip x) = t x) (A : SymmetricPart) (x : X) :
    signedDiagonalAction s t A (s.delta x) = symmetricGammaForm A (t x) • s.delta x := by
  change signedExtension s (fun y => symmetricGammaForm A (t y) • s.delta y) (s.delta x) = _
  apply signedExtension_delta
  intro y
  rw [ht, s.delta_flip, smul_neg]

variable [Fintype X]

/-- The `S,R,R` block of (28.2), using the existing normalized signed form. -/
def signedDiagonalBlock (s : SignedSet X) (t : X → SymmetricPart) :
    SymmetricPart →ₗ[ℝ] s.Space →ₗ[ℝ] s.Space →ₗ[ℝ] ℝ :=
  (signedDiagonalAction s t).compr₂ s.form

@[simp] theorem signedDiagonalBlock_delta (s : SignedSet X) (t : X → SymmetricPart)
    (ht : ∀ x, t (s.flip x) = t x) (A : SymmetricPart) (x y : X) :
    signedDiagonalBlock s t A (s.delta x) (s.delta y) =
      symmetricGamma A (t x) * s.form (s.delta x) (s.delta y) := by
  change s.form (signedDiagonalAction s t A (s.delta x)) (s.delta y) = _
  rw [signedDiagonalAction_delta s t ht, map_smul, LinearMap.smul_apply]
  rfl

theorem signedDiagonalBlock_symmetric (s : SignedSet X) (t : X → SymmetricPart)
    (A : SymmetricPart) (v w : s.Space) :
    signedDiagonalBlock s t A v w = signedDiagonalBlock s t A w v := by
  have h : signedDiagonalBlock s t A = (signedDiagonalBlock s t A).flip := by
    apply LinearMap.BilinForm.ext_basis s.basis
    intro i j
    change s.form (signedDiagonalAction s t A (s.basis i)) (s.basis j) =
      s.form (signedDiagonalAction s t A (s.basis j)) (s.basis i)
    rw [signedDiagonalAction_basis, signedDiagonalAction_basis]
    simp only [map_smul, LinearMap.smul_apply, s.basis_orthonormal]
    by_cases hij : i = j
    · subst j; rfl
    · simp only [hij, Ne.symm hij, if_false, smul_zero]
  exact congrArg (fun B : LinearMap.BilinForm ℝ s.Space => B v w) h

end

section
open scoped TensorProduct
variable {X V : Type*} [Finite X] [AddCommGroup V] [Module ℝ V]

/-- The `R,W,W` block obtained by descent from the source tensor coefficients. -/
def signedTensorBlock (s : SignedSet X) (γ : LinearMap.BilinForm ℝ V)
    (t : X → SymmetricPart) (T : X → Module.End ℝ V) :
    s.Space →ₗ[ℝ] LinearMap.BilinForm ℝ ((Fin 24 → ℝ) ⊗[ℝ] V) :=
  signedExtension s (fun x => shortTensorBlock γ (t x) (T x))

/-- Descent uses only the proved source sign identities for tensor and spin. -/
theorem signedTensorBlock_delta (s : SignedSet X) (γ : LinearMap.BilinForm ℝ V)
    (t : X → SymmetricPart) (T : X → Module.End ℝ V)
    (ht : ∀ x, t (s.flip x) = t x) (hT : ∀ x, T (s.flip x) = -(T x)) (x : X) :
    signedTensorBlock s γ t T (s.delta x) = shortTensorBlock γ (t x) (T x) := by
  apply signedExtension_delta
  intro y
  rw [ht, hT, shortTensorBlock_neg]

theorem signedTensorBlock_symmetric (s : SignedSet X) (γ : LinearMap.BilinForm ℝ V)
    (t : X → SymmetricPart) (T : X → Module.End ℝ V)
    (hs : ∀ v w, γ v w = γ w v)
    (hi : ∀ x v, T x (T x v) = v)
    (ho : ∀ x v w, γ (T x v) (T x w) = γ v w)
    (a : s.Space) (v w : (Fin 24 → ℝ) ⊗[ℝ] V) :
    signedTensorBlock s γ t T a v w = signedTensorBlock s γ t T a w v :=
  signedExtension_symmetric s _
    (fun x => shortTensorBlock_symmetric γ (t x) (T x) hs (hi x) (ho x)) a v w

/-- Equation (28.6) after linear descent, for an actual rank-one short tensor. -/
theorem signedTensorBlock_rankOne (s : SignedSet X) (γ : LinearMap.BilinForm ℝ V)
    (t : X → SymmetricPart) (T : X → Module.End ℝ V)
    (ht : ∀ x, t (s.flip x) = t x) (hT : ∀ x, T (s.flip x) = -(T x))
    (x : X) (ξ a b : Fin 24 → ℝ) (hξ : ∀ i j, (t x).val i j = ξ i * ξ j) (v w : V) :
    signedTensorBlock s γ t T (s.delta x) (a ⊗ₜ[ℝ] v) (b ⊗ₜ[ℝ] w) =
      (a ⬝ᵥ b - 2 * (a ⬝ᵥ ξ) * (ξ ⬝ᵥ b)) * γ (T x v) w / 8 := by
  rw [signedTensorBlock_delta s γ t T ht hT]
  exact shortTensorBlock_rankOne γ (t x) (T x) ξ a b hξ v w

end

end Sporadic.Monster.Construction.Griess
