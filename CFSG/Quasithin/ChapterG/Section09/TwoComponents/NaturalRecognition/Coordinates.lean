module

public import Theory.Representation.SpecialLinearNatural
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Full special-linear images in the small tensor factors

A faithful representation of a perfect group with the order of SL_d(E)
is the natural action in actual semilinear coordinates. A basis and a field
isomorphism conjugate the given action to matrices over E. Perfectness kills
the determinant character; injectivity and the order equality make that
matrix homomorphism an isomorphism. The same coordinates intertwine the action.

This is the linear-algebra step in the G.9.3 recognition on printed p.356.
It does not assert any low-dimensional classification or assume that the
given representation is natural. In dimension three it also handles a dual
factor: its actual matrix image determines the appropriate group isomorphism.
-/

@[expose] public noncomputable section

open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents.NaturalRecognition

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

variable {F : Type*} [Field F]
  {M : Type*} [AddCommGroup M] [Module F M]
  {S : Type*} [Group S] [Group.IsPerfect S]

/-- Perfectness makes the actual representation image special linear. -/
private def specialCoordinates {d : ℕ} (σ : Representation F S M)
    (b : Module.Basis (Fin d) F M) : S →* SL(d, F) := by
  let g : S →* (M ≃ₗ[F] M) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F M).toMonoidHom.comp σ.asGroupHom
  have hdet (s : S) : (g s).det = 1 := by
    exact Abelianization.commutator_subset_ker (LinearEquiv.det.comp g)
      (Group.IsPerfect.mem_commutator (g := s))
  let t : S →* _root_.SpecialLinearGroup F M :=
    { toFun := fun s => ⟨g s, hdet s⟩
      map_one' := by apply Subtype.ext; exact g.map_one
      map_mul' := fun s t => by apply Subtype.ext; exact g.map_mul s t }
  exact (Matrix.SpecialLinearGroup.toLin_equiv b).symm.toMonoidHom.comp t

private theorem specialCoordinates_intertwines {d : ℕ} (σ : Representation F S M)
    (b : Module.Basis (Fin d) F M) (s : S) (x : M) :
    b.equivFun (σ s x) = Representation.specialLinearNatural d
      (specialCoordinates σ b s) (b.equivFun x) := by
  change b.repr (σ s x) = (LinearMap.toMatrix b b (σ s)).mulVec (b.repr x)
  exact (LinearMap.toMatrix_mulVec_repr b b (σ s) x).symm

private theorem specialCoordinates_injective {d : ℕ} (σ : Representation F S M)
    (b : Module.Basis (Fin d) F M) (hi : Function.Injective σ) :
    Function.Injective (specialCoordinates σ b) := by
  intro s t h
  apply hi
  ext x
  apply b.equivFun.injective
  rw [specialCoordinates_intertwines, specialCoordinates_intertwines, h]

private def fullSpecialCoordinates {d : ℕ} [Finite F] (σ : Representation F S M)
    (b : Module.Basis (Fin d) F M) (hi : Function.Injective σ)
    (ho : Nat.card S = Nat.card SL(d, F)) : S ≃* SL(d,F) :=
  MulEquiv.ofBijective (specialCoordinates σ b)
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨specialCoordinates_injective σ b hi, ho⟩)

variable {E : Type*} [Field E]

/-- Entrywise transport of scalar coordinates. -/
private def coordinateField (c : F ≃+* E) (d : ℕ) :
    (Fin d → F) ≃ₛₗ[(c : F →+* E)] (Fin d → E) where
  toFun x i := c (x i)
  invFun x i := c.symm (x i)
  left_inv x := by ext i; exact c.symm_apply_apply _
  right_inv x := by ext i; exact c.apply_symm_apply _
  map_add' x y := by ext i; exact c.map_add _ _
  map_smul' a x := by ext i; exact c.map_mul _ _

variable {M : Type*} [AddCommGroup M] [Module F M] [FiniteDimensional F M]
  {S : Type*} [Group S] [Group.IsPerfect S]

/-- A faithful perfect action of full special-linear order is the natural action
in actual semilinear coordinates. The group map is constructed from that action. -/
theorem natural_coordinates_of_order {d : ℕ} [Finite E]
    (σ : Representation F S M) (hi : Function.Injective σ)
    (hd : Module.finrank F M = d) (c : F ≃+* E)
    (ho : Nat.card S = Nat.card SL(d,E)) :
    ∃ e : S ≃* SL(d,E), ∃ f : M ≃ₛₗ[(c : F →+* E)] (Fin d → E),
      ∀ g x, f (σ g x) = Representation.specialLinearNatural d (e g) (f x) := by
  let f := (Module.finBasisOfFinrankEq F M hd).equivFun.trans (coordinateField c d)
  let τ : Representation E S (Fin d → E) := f.conjRingEquiv.toMonoidHom.comp σ
  have hτ : Function.Injective τ := f.conjRingEquiv.injective.comp hi
  let b := Pi.basisFun E (Fin d)
  let e := fullSpecialCoordinates τ b hτ ho
  refine ⟨e, f.trans b.equivFun, ?_⟩
  intro g x
  change b.equivFun (f (σ g x)) = Representation.specialLinearNatural d
    (specialCoordinates τ b g) (b.equivFun (f x))
  rw [← specialCoordinates_intertwines τ b g]
  change b.equivFun (f (σ g x)) = b.equivFun (f (σ g (f.symm (f x))))
  rw [f.symm_apply_apply]

end CFSG.Quasithin.ChapterG.Section09.TwoComponents.NaturalRecognition
