module

public import Theory.AlgebraicGroup.Tori.Character.Duality
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Torus kernels and integral character cokernels

Evaluation against a complete character lattice identifies actual torus points
with lattice characters. Characters annihilating an integral endomorphism
factor uniquely through its cokernel. Smith normal form computes the order of
this cokernel as the absolute determinant, and finite abelian duality preserves
that order when the characteristic does not divide it. Finiteness is supplied
by the same equivalences, rather than inferred from a natural-cardinality
convention.

Source: the duality step in Steinberg,
`refs/KGroup/GLS3/Chapter2St2.tex`, proof of 14.8(a), following 14.9(b).
-/

@[expose] public noncomputable section
namespace Theory.AlgebraicGroup
universe u v
variable {k : Type u} [Field k]
variable {M : Type v} [AddCommGroup M]

/-- Characters of an integral lattice annihilating the image of an endomorphism. -/
def IntegralCharacterKernel (k : Type u) [Field k] (f : M →ₗ[ℤ] M) :=
  {χ : M →ₗ[ℤ] Additive kˣ // χ.comp f = 0}

/-- An annihilating character is precisely a character of the cokernel. -/
def integralCharacterKernelEquiv (f : M →ₗ[ℤ] M) :
    IntegralCharacterKernel k f ≃
      (Multiplicative (M ⧸ LinearMap.range f) →* kˣ) := by
  let e : IntegralCharacterKernel k f ≃
      (M ⧸ LinearMap.range f →ₗ[ℤ] Additive kˣ) :=
    { toFun := fun χ => (LinearMap.range f).liftQ χ.val
        (by rintro x ⟨a, rfl⟩; exact LinearMap.congr_fun χ.property a)
      invFun := fun χ => ⟨χ.comp (LinearMap.range f).mkQ, by
        apply LinearMap.ext
        intro a
        change χ ((LinearMap.range f).mkQ (f a)) = 0
        rw [show (LinearMap.range f).mkQ (f a) = 0 from
          (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).mpr ⟨a, rfl⟩, map_zero]⟩
      left_inv := fun χ => by apply Subtype.ext; ext a; rfl
      right_inv := fun χ => by
        apply LinearMap.ext
        intro a
        obtain ⟨a, rfl⟩ := (LinearMap.range f).mkQ_surjective a
        rfl }
  exact e.trans ((addMonoidHomLequivInt ℤ).symm.toEquiv.trans
    AddMonoidHom.toMultiplicativeLeft)

section Finite
variable [Module.Free ℤ M] [Module.Finite ℤ M]

lemma integralCokernel_card (f : M →ₗ[ℤ] M) (hf : f.det ≠ 0) :
    Nat.card (M ⧸ LinearMap.range f) = f.det.natAbs := by
  have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp
    (not_not.mp (mt LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hf))
  let e := LinearEquiv.ofInjective f hinj
  have h := Submodule.natAbs_det_equiv (LinearMap.range f) e.toAddEquiv
  exact h.symm

lemma integralCokernel_finite (f : M →ₗ[ℤ] M) (hf : f.det ≠ 0) :
    Finite (M ⧸ LinearMap.range f) := by
  have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp
    (not_not.mp (mt LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hf))
  exact Submodule.finiteQuotientOfFreeOfRankEq (LinearMap.range f)
    (LinearEquiv.ofInjective f hinj).finrank_eq.symm

/-- Finite cokernel duality gives both finiteness and the determinant cardinality
when the characteristic does not divide the determinant. -/
theorem integralCharacterKernel_finite_card [IsAlgClosed k]
    (f : M →ₗ[ℤ] M) (hf : f.det ≠ 0)
    (hchar : (f.det.natAbs : k) ≠ 0) :
    Finite (IntegralCharacterKernel k f) ∧
      Nat.card (IntegralCharacterKernel k f) = f.det.natAbs := by
  let Q := M ⧸ LinearMap.range f
  let : Finite Q := integralCokernel_finite f hf
  have hcard : Nat.card (Multiplicative Q) = f.det.natAbs := by
    exact (Nat.card_congr (Multiplicative.toAdd : Multiplicative Q ≃ Q)).trans
      (integralCokernel_card f hf)
  have hexp : (Monoid.exponent (Multiplicative Q) : k) ≠ 0 := by
    intro hz
    obtain ⟨d, hd⟩ := Group.exponent_dvd_nat_card (G := Multiplicative Q)
    have hzero : (Nat.card (Multiplicative Q) : k) = 0 := by
      rw [hd, Nat.cast_mul, hz, zero_mul]
    exact hchar (hcard ▸ hzero)
  let : NeZero (Monoid.exponent (Multiplicative Q) : k) := ⟨hexp⟩
  let e := (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity
    (Multiplicative Q) k).some
  let E := (integralCharacterKernelEquiv (k := k) f).trans e.toEquiv
  exact ⟨Finite.of_equiv (Multiplicative Q) E.symm,
    (Nat.card_congr E).trans hcard⟩

end Finite

variable {T : Variety k} [AlgebraicGroup T]

/-- Evaluation identifies torus points with all linear characters of any chosen
complete integral character lattice. -/
def torusLatticeEvalEquiv [IsAlgClosed k] (hT : IsTorus T)
    (e : Multiplicative M ≃* TorusCharacter T) :
    Variety.Point T ≃ (M →ₗ[ℤ] Additive kˣ) :=
  (Equiv.ofBijective (torusPointEval T) (torusPointEval_bijective hT)).trans
    (e.symm.monoidHomCongrLeft.toEquiv.trans
      (MonoidHom.toAdditiveRight.trans (addMonoidHomLequivInt ℤ).toEquiv))

lemma torusLatticeEvalEquiv_apply [IsAlgClosed k] (hT : IsTorus T)
    (e : Multiplicative M ≃* TorusCharacter T) (t : Variety.Point T) (a : M) :
    ((torusLatticeEvalEquiv hT e t a).toMul : k) =
      (e (Multiplicative.ofAdd a)).pointCharacter t := rfl

/-- The literal torus points on which every character in the image is one. -/
def TorusLatticeKernel (e : Multiplicative M ≃* TorusCharacter T)
    (f : M →ₗ[ℤ] M) :=
  {t : Variety.Point T // ∀ a, (e (Multiplicative.ofAdd (f a))).pointCharacter t = 1}

/-- Torus evaluation identifies the actual point kernel with the dual of the
integral cokernel; no cardinality assumptions enter this equivalence. -/
def torusLatticeKernelEquiv [IsAlgClosed k] (hT : IsTorus T)
    (e : Multiplicative M ≃* TorusCharacter T) (f : M →ₗ[ℤ] M) :
    TorusLatticeKernel e f ≃ IntegralCharacterKernel k f :=
  Equiv.subtypeEquiv (torusLatticeEvalEquiv hT e) (fun t => by
    constructor
    · intro ht
      apply LinearMap.ext
      intro a
      apply Additive.toMul.injective
      apply Units.ext
      exact ht a
    · intro ht a
      exact congrArg (fun x : Additive kˣ => (x.toMul : k))
        (LinearMap.congr_fun ht a))

/-- The actual torus kernel is finite and its order is the absolute integral
determinant, provided this determinant is nonzero in the field. -/
theorem torusLatticeKernel_finite_card [IsAlgClosed k]
    [Module.Free ℤ M] [Module.Finite ℤ M] (hT : IsTorus T)
    (e : Multiplicative M ≃* TorusCharacter T) (f : M →ₗ[ℤ] M)
    (hf : f.det ≠ 0) (hchar : (f.det.natAbs : k) ≠ 0) :
    Finite (TorusLatticeKernel e f) ∧
      Nat.card (TorusLatticeKernel e f) = f.det.natAbs := by
  obtain ⟨hfin, hcard⟩ := integralCharacterKernel_finite_card (k := k) f hf hchar
  let := hfin
  let E := torusLatticeKernelEquiv hT e f
  exact ⟨Finite.of_equiv (IntegralCharacterKernel k f) E.symm,
    (Nat.card_congr E).trans hcard⟩

end Theory.AlgebraicGroup
