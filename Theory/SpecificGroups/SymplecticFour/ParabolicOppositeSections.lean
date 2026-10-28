module
public import Theory.Representation.BinarySquareInverseWeights
public import Theory.SpecificGroups.SymplecticFour.RootTori
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.Coordinates
public import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Algebra.ZMod

/-!
# Opposite one-dimensional sections of the point parabolic

In the original symplectic coordinates, the long root at index zero is
parametrized by the additive field. The natural cofixed line is the quotient
by the hyperplane whose f₀ coordinate vanishes. If a point-parabolic element
has point character c, its conjugation on the root has weight c² and its
action on the cofixed line has weight c⁻¹. In particular both calculations
use the same diagonal element `diagonalTorus a 1`.

The natural quotient map and root parametrization below are actual
equivariant identifications. Source graph sections require a separate
marking before this model calculation applies to them.

Source: the point-parabolic module comparison in MS93 (3.7),
“Pushing up weak BN-pairs of rank two”, printed pp.876–877.
-/

@[expose] public section

open Matrix
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.ParabolicOppositeSections
variable {F : Type*} [Field F]

noncomputable def coordinate : Vector F →ₗ[F] F := LinearMap.proj (.inr 0)

@[simp] theorem coordinate_apply (v : Vector F) : coordinate v = v (.inr 0) := rfl

theorem coordinate_surjective : Function.Surjective (coordinate (F := F)) :=
  fun a => ⟨Pi.single (.inr 0) a, by simp⟩

noncomputable def hyperplane : Submodule F (Vector F) := coordinate.ker

@[simp] theorem mem_hyperplane (v : Vector F) : v ∈ hyperplane ↔ v (.inr 0) = 0 := Iff.rfl

noncomputable def quotientCoordinate : (Vector F ⧸ hyperplane (F := F)) ≃ₗ[F] F :=
  (coordinate (F := F)).quotKerEquivOfSurjective coordinate_surjective

@[simp] theorem quotientCoordinate_mk (v : Vector F) :
    (quotientCoordinate (F := F)) (Submodule.Quotient.mk v) = v (.inr 0) := rfl

theorem coordinate_parabolic (g : stabilizer (point F)) (v : Vector F) :
    coordinate (g.val • v) = (determinantCharacter (point F) g : F)⁻¹ * coordinate v := by
  have h := preserves_form g.val v (e (F := F) 0)
  rw [pointParabolic_smul_e_zero g] at h
  have hh : g.val.val (.inl 0) (.inl 0) * (g.val • v) (.inr 0) = v (.inr 0) := by
    simpa only [map_smul, form_e_right, smul_eq_mul, mul_neg, neg_inj] using h
  rw [← determinantCharacter_point_coe g] at hh
  change (g.val • v) (.inr 0) = (determinantCharacter (point F) g : F)⁻¹ * v (.inr 0)
  rw [← hh]
  simp

theorem coordinate_torus (a : Fˣ) (v : Vector F) :
    coordinate (diagonalTorus a 1 • v) = (a : F)⁻¹ * coordinate v := by
  simpa only [diagonalTorus_point_character] using
    coordinate_parabolic ⟨diagonalTorus a 1, (diagonalTorus_mem_borel a 1).1⟩ v

theorem root_torus (a : Fˣ) (x : F) :
    diagonalTorus a 1 * rootElement 0 x * (diagonalTorus a 1)⁻¹ =
      rootElement 0 ((a : F)^2 * x) := by
  simpa [RootTori.element, RootTori.weight] using RootTori.conjugate (F := F) 0 a x

noncomputable def quotientAction (g : stabilizer (point F)) :
    (Vector F ⧸ hyperplane (F := F)) →ₗ[F] (Vector F ⧸ hyperplane (F := F)) :=
  (hyperplane (F := F)).mapQ (hyperplane (F := F)) (toLinear g.val).toLinearMap (by
    intro v hv
    change coordinate (g.val • v) = 0
    rw [coordinate_parabolic]
    exact mul_eq_zero_of_right _ hv)

@[simp] theorem quotientAction_mk (g : stabilizer (point F)) (v : Vector F) :
    quotientAction g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (g.val • v) := rfl

theorem quotientCoordinate_equivariant (g : stabilizer (point F))
    (v : Vector F ⧸ hyperplane (F := F)) :
    (quotientCoordinate (F := F)) (quotientAction g v) =
      (determinantCharacter (point F) g : F)⁻¹ * (quotientCoordinate (F := F)) v := by
  induction v using Submodule.Quotient.induction_on with
  | _ v => exact coordinate_parabolic g v

noncomputable def rootParameter : Multiplicative F ≃* RootSubgroup.group (F := F) 0 :=
  RootSubgroup.equiv 0

@[simp] theorem rootParameter_coe (x : F) :
    (rootParameter (Multiplicative.ofAdd x) : Sp F) = rootElement 0 x := rfl

theorem root_natural (x : F) (v : Vector F) :
    rootElement 0 x • v = v + (x * coordinate v) • e (F := F) 0 := by
  ext i
  fin_cases i <;> simp [coordinate, rootElement, rootMatrix, Matrix.mulVec,
    dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.single, e]

theorem root_parabolic (g : stabilizer (point F)) (x : F) :
    g.val * rootElement 0 x * g.val⁻¹ =
      rootElement 0 ((determinantCharacter (point F) g : F)^2 * x) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext
  apply Matrix.ext_of_mulVec_single
  intro j
  have hh (v : Vector F) :
      (g.val * rootElement 0 x) • v =
        (rootElement 0 ((determinantCharacter (point F) g : F)^2 * x) * g.val) • v := by
    simp only [mul_smul]
    rw [root_natural, root_natural, coordinate_parabolic]
    change toLinear g.val (v + (x * coordinate v) • e 0) = _
    rw [map_add, map_smul]
    change g.val • v + (x * coordinate v) • (g.val • e 0) = _
    rw [pointParabolic_smul_e_zero g, ← determinantCharacter_point_coe g, smul_smul]
    congr 1
    congr 1
    field_simp
  exact hh (Pi.single j 1)

/-- The same embedded unit actor is used on both sections. -/
noncomputable def torusActor : Fˣ →* stabilizer (point F) :=
  (RootTori.parameter (F := F) 0).codRestrict _ (by
    intro a
    exact (diagonalTorus_mem_borel a 1).1)

@[simp] theorem torusActor_coe (a : Fˣ) :
    (torusActor a : Sp F) = diagonalTorus a 1 := rfl

@[simp] theorem torusActor_character (a : Fˣ) :
    determinantCharacter (point F) (torusActor a) = a :=
  diagonalTorus_point_character a 1

/-- Additive coordinates on the literal long-root subgroup. -/
noncomputable def rootCoordinate : Additive (RootSubgroup.group (F := F) 0) ≃+ F :=
  rootParameter.symm.toAdditiveLeft

@[simp] theorem rootCoordinate_symm_coe (x : F) :
    ((rootCoordinate.symm x).toMul : Sp F) = rootElement 0 x := rfl

theorem parabolic_normalizes_root :
    stabilizer (point F) ≤ Subgroup.normalizer (RootSubgroup.group (F := F) 0 : Set (Sp F)) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro g hg r hr
  obtain ⟨x,rfl⟩ := (RootSubgroup.mem_group_iff 0 r).mp hr
  rw [root_parabolic ⟨g,hg⟩]
  exact (RootSubgroup.mem_group_iff 0 _).mpr ⟨_,rfl⟩

/-- Literal conjugation, restricted to the normalized long-root subgroup. -/
noncomputable def rootAction (g : stabilizer (point F)) :
    Additive (RootSubgroup.group (F := F) 0) ≃+ Additive (RootSubgroup.group (F := F) 0) :=
  ((RootSubgroup.group (F := F) 0).normalizerMonoidHom
    ⟨g.val,parabolic_normalizes_root g.property⟩).toAdditive

@[simp] theorem rootAction_coe (g : stabilizer (point F))
    (r : Additive (RootSubgroup.group (F := F) 0)) :
    ((rootAction g r).toMul : Sp F) = g.val * (r.toMul : Sp F) * g.val⁻¹ := rfl

theorem rootCoordinate_equivariant (g : stabilizer (point F))
    (r : Additive (RootSubgroup.group (F := F) 0)) :
    rootCoordinate (rootAction g r) =
      (determinantCharacter (point F) g : F)^2 * rootCoordinate r := by
  apply rootCoordinate.symm.injective
  apply Additive.toMul.injective
  apply Subtype.val_injective
  simp only [rootCoordinate_symm_coe, AddEquiv.symm_apply_apply, rootAction_coe]
  have hr : (r.toMul : Sp F) = rootElement 0 (rootCoordinate r) := by
    simpa only [AddEquiv.symm_apply_apply] using
      rootCoordinate_symm_coe (rootCoordinate r)
  rw [hr,root_parabolic]

@[simp] theorem rootCoordinate_torus (a : Fˣ)
    (r : Additive (RootSubgroup.group (F := F) 0)) :
    rootCoordinate (rootAction (torusActor a) r) = (a : F)^2 * rootCoordinate r := by
  simp [rootCoordinate_equivariant]

@[simp] theorem quotientCoordinate_torus (a : Fˣ)
    (v : Vector F ⧸ hyperplane (F := F)) :
    (quotientCoordinate (F := F)) (quotientAction (torusActor a) v) =
      (a : F)⁻¹ * (quotientCoordinate (F := F)) v := by
  simp [quotientCoordinate_equivariant]

noncomputable def pairCoordinate :
    (Additive (RootSubgroup.group (F := F) 0) × (Vector F ⧸ hyperplane (F := F))) ≃+ F × F :=
  rootCoordinate.prodCongr quotientCoordinate.toAddEquiv

variable [Finite F] [CharP F 2]

theorem root_to_quotient_zero_torus (hq : 2 < Nat.card F) (h4 : Nat.card F ≠ 4)
    (f : Additive (RootSubgroup.group (F := F) 0) →+ (Vector F ⧸ hyperplane (F := F)))
    (he : ∀ a : Fˣ, ∀ r, f (rootAction (torusActor a) r) = quotientAction (torusActor a) (f r)) :
    f = 0 := by
  let ψ := quotientCoordinate.toAddEquiv.toAddMonoidHom.comp (f.comp rootCoordinate.symm.toAddMonoidHom)
  have hψ : ψ = 0 := Representation.BinarySquareInverseWeights.square_to_inverse_eq_zero hq h4 ψ (by
    intro a x
    change (quotientCoordinate (F := F)) (f (rootCoordinate.symm ((a : F)^2*x))) =
      (a : F)⁻¹ * (quotientCoordinate (F := F)) (f (rootCoordinate.symm x))
    have hr : rootCoordinate.symm ((a : F)^2*x) = rootAction (torusActor a) (rootCoordinate.symm x) := by
      apply rootCoordinate.injective
      simp
    rw [hr,he,quotientCoordinate_torus])
  apply AddMonoidHom.ext
  intro r
  apply (quotientCoordinate (F := F)).injective
  have hh := congrArg (fun f : F →+ F => f (rootCoordinate r)) hψ
  simpa [ψ] using hh

theorem quotient_to_root_zero_torus (hq : 2 < Nat.card F) (h4 : Nat.card F ≠ 4)
    (f : (Vector F ⧸ hyperplane (F := F)) →+ Additive (RootSubgroup.group (F := F) 0))
    (he : ∀ a : Fˣ, ∀ v, f (quotientAction (torusActor a) v) = rootAction (torusActor a) (f v)) :
    f = 0 := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let ψ := rootCoordinate.toAddMonoidHom.comp (f.comp (quotientCoordinate (F := F)).symm.toAddEquiv.toAddMonoidHom)
  have hψ : ψ = 0 := Representation.BinarySquareInverseWeights.inverse_to_square_eq_zero hq h4 ψ (by
    intro a x
    change rootCoordinate (f ((quotientCoordinate (F := F)).symm ((a : F)⁻¹*x))) =
      (a : F)^2 * rootCoordinate (f ((quotientCoordinate (F := F)).symm x))
    have hr : (quotientCoordinate (F := F)).symm ((a : F)⁻¹*x) =
        quotientAction (torusActor a) ((quotientCoordinate (F := F)).symm x) := by
      apply (quotientCoordinate (F := F)).injective
      simp
    rw [hr,he,rootCoordinate_torus])
  apply AddMonoidHom.ext
  intro v
  apply (rootCoordinate (F := F)).injective
  have hh := congrArg (fun f : F →+ F => f ((quotientCoordinate (F := F)) v)) hψ
  simpa [ψ] using hh

theorem not_equiv_torus (hq : 2 < Nat.card F) (h4 : Nat.card F ≠ 4) :
    ¬ ∃ e : Additive (RootSubgroup.group (F := F) 0) ≃+ (Vector F ⧸ hyperplane (F := F)),
      ∀ a : Fˣ, ∀ r, e (rootAction (torusActor a) r) = quotientAction (torusActor a) (e r) := by
  rintro ⟨e,he⟩
  have hz := root_to_quotient_zero_torus hq h4 e.toAddMonoidHom he
  have hh : e (rootCoordinate.symm (1 : F)) = e 0 := by
    have hh := congrArg (fun f : Additive (RootSubgroup.group (F := F) 0) →+ _ => f (rootCoordinate.symm (1 : F))) hz
    exact hh.trans e.map_zero.symm
  have h1 := congrArg rootCoordinate (e.injective hh)
  simp at h1

theorem not_equiv_parabolic (hq : 2 < Nat.card F) (h4 : Nat.card F ≠ 4) :
    ¬ ∃ e : Additive (RootSubgroup.group (F := F) 0) ≃+ (Vector F ⧸ hyperplane (F := F)),
      ∀ g : stabilizer (point F), ∀ r, e (rootAction g r) = quotientAction g (e r) := by
  rintro ⟨e,he⟩
  exact not_equiv_torus hq h4 ⟨e,fun a r => he (torusActor a) r⟩

omit [Finite F] [CharP F 2] in
/-- At the boundary field order, the actual two sections are equivariantly
isomorphic for the entire point parabolic. -/
theorem equiv_parabolic_of_card_four (h4 : Nat.card F = 4) :
    ∃ e : Additive (RootSubgroup.group (F := F) 0) ≃+ (Vector F ⧸ hyperplane (F := F)),
      ∀ g : stabilizer (point F), ∀ r, e (rootAction g r) = quotientAction g (e r) := by
  refine ⟨rootCoordinate.trans quotientCoordinate.symm.toAddEquiv, ?_⟩
  intro g r
  apply (quotientCoordinate (F := F)).injective
  change (quotientCoordinate (F := F))
      ((quotientCoordinate (F := F)).symm (rootCoordinate (rootAction g r))) =
    (quotientCoordinate (F := F))
      (quotientAction g ((quotientCoordinate (F := F)).symm (rootCoordinate r)))
  rw [LinearEquiv.apply_symm_apply, quotientCoordinate_equivariant,
    LinearEquiv.apply_symm_apply, rootCoordinate_equivariant,
    Representation.BinarySquareInverseWeights.weights_eq_of_card_four h4]

theorem order_q_axes_torus (hq : 2 < Nat.card F) (h4 : Nat.card F ≠ 4)
    (K : AddSubgroup (Additive (RootSubgroup.group (F := F) 0) × (Vector F ⧸ hyperplane (F := F))))
    (hcard : Nat.card K = Nat.card F)
    (hK : ∀ a : Fˣ, ∀ x ∈ K, (rootAction (torusActor a) x.1, quotientAction (torusActor a) x.2) ∈ K) :
    K = (⊤ : AddSubgroup (Additive (RootSubgroup.group (F := F) 0))).prod ⊥ ∨
      K = (⊥ : AddSubgroup (Additive (RootSubgroup.group (F := F) 0))).prod ⊤ := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let e := pairCoordinate (F := F)
  let J := K.map e.toAddMonoidHom
  have hc : Nat.card J = Nat.card F :=
    (Nat.card_congr (K.equivMapOfInjective e.toAddMonoidHom e.injective).toEquiv).symm.trans hcard
  have hJ : ∀ a : Fˣ, ∀ x ∈ J, ((a : F)^2*x.1,(a : F)⁻¹*x.2) ∈ J := by
    intro a x hx
    obtain ⟨y,hy,rfl⟩ := hx
    refine ⟨_,hK a y hy,?_⟩
    exact Prod.ext (rootCoordinate_torus a y.1) (quotientCoordinate_torus a y.2)
  have hm (x) : x ∈ K ↔ e x ∈ J := by
    constructor
    · intro hx; exact ⟨x,hx,rfl⟩
    · rintro ⟨y,hy,hh⟩
      exact e.injective hh ▸ hy
  rcases Representation.BinarySquareInverseWeights.order_q_addSubgroup_axes hq h4 J hc hJ with hj | hj
  · left
    ext x
    rw [hm,hj]
    change (True ∧ (quotientCoordinate (F := F)) x.2 = 0) ↔ (True ∧ x.2 = 0)
    simp
  · right
    ext x
    rw [hm,hj]
    change ((rootCoordinate (F := F)) x.1 = 0 ∧ True) ↔ (x.1 = 0 ∧ True)
    simp

theorem order_q_axes_parabolic (hq : 2 < Nat.card F) (h4 : Nat.card F ≠ 4)
    (K : AddSubgroup (Additive (RootSubgroup.group (F := F) 0) × (Vector F ⧸ hyperplane (F := F))))
    (hcard : Nat.card K = Nat.card F)
    (hK : ∀ g : stabilizer (point F), ∀ x ∈ K, (rootAction g x.1, quotientAction g x.2) ∈ K) :
    K = (⊤ : AddSubgroup (Additive (RootSubgroup.group (F := F) 0))).prod ⊥ ∨
      K = (⊥ : AddSubgroup (Additive (RootSubgroup.group (F := F) 0))).prod ⊤ :=
  order_q_axes_torus hq h4 K hcard (fun a x hx => hK (torusActor a) x hx)
end Theory.SpecificGroups.SymplecticFour.ParabolicOppositeSections
