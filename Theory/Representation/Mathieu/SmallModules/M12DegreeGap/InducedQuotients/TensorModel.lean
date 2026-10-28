module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.InducedHeart
public import Mathlib.RepresentationTheory.FiniteIndex

/-!
# The native twelve-fiber model of the induced M₁₁ heart

The point module extends to the actual M₁₂ heart. Untwisting coinduction
therefore identifies its induction with twelve copies of that heart, acted
on diagonally: `(g v)(x) = g (v(g⁻¹ x))`. We first identify the literal
M₁₁ induction with induction from the native point stabilizer. All
comparisons are equivariant linear equivalences, including the inverse
convention in Mathlib's coinvariant induction.

This prepares the finite module calculation for James, J. Algebra 27
(1973), 57–111, used in the Chapter K degree reduction (printed p.457).
It does not assert simplicity or a composition-factor list.
-/

public noncomputable section
namespace Representation.MathieuSmall.M12DegreeGap.InducedQuotients
open Sporadic.Mathieu M12Recognition

abbrev PointGroup := MulAction.stabilizer M12 (12 : Fin 12)
abbrev pointAction := m12HeartRepresentation.comp PointGroup.subtype
abbrev TensorSpace := Fin 12 → M12Heart

/-- The heart tensored with the native twelve-point permutation action. -/
@[expose] def tensorAction : Representation (ZMod 2) M12 TensorSpace where
  toFun g :=
    { toFun := fun v x => m12HeartRepresentation g (v (g⁻¹ • x))
      map_add' := by intros; ext x; simp
      map_smul' := by intros; ext x; simp }
  map_one' := by ext v x; simp
  map_mul' := by intros; ext v x; simp [mul_smul]

@[simp] theorem tensorAction_apply (g : M12) (v : TensorSpace) (x : Fin 12) :
    tensorAction g v x = m12HeartRepresentation g (v (g⁻¹ • x)) := rfl

private theorem inducedKernel_eq :
    Coinvariants.ker (Representation.tprod
      ((leftRegular (ZMod 2) M12).comp pointEmbedding) pointRepresentation) =
    Coinvariants.ker (Representation.tprod
      ((leftRegular (ZMod 2) M12).comp PointGroup.subtype) pointAction) := by
  unfold Coinvariants.ker
  congr 1
  ext x
  constructor
  · rintro ⟨⟨g, v⟩, rfl⟩
    exact ⟨(m11ToM12PointStabilizer g, v), rfl⟩
  · rintro ⟨⟨g, v⟩, rfl⟩
    have hs : Function.Surjective m11ToM12PointStabilizer :=
      (m11ToM12PointStabilizer_injective.bijective_of_nat_card_le
        (Nat.card_congr m11EquivM12PointStabilizer.toEquiv).ge).surjective
    obtain ⟨s, rfl⟩ := hs g
    exact ⟨(s, v), rfl⟩

/-- Replace the M₁₁ parametrization by its actual point-stabilizer image. -/
def inducedPointEquiv : inducedHeart.Equiv (ind PointGroup.subtype pointAction) where
  toLinearEquiv := Submodule.quotEquivOfEq _ _ inducedKernel_eq
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl

private def liftPoint (x : Fin 12) : M12 :=
  Classical.choose (MulAction.exists_smul_eq M12 (12 : Fin 12) x)

private theorem liftPoint_spec (x : Fin 12) : liftPoint x • (12 : Fin 12) = x :=
  Classical.choose_spec (MulAction.exists_smul_eq M12 (12 : Fin 12) x)

/-- Untwist a coinduced function along a point transporter. -/
private def coindToTensor : coindV PointGroup.subtype pointAction →ₗ[ZMod 2] TensorSpace where
  toFun f x := m12HeartRepresentation (liftPoint x) (f.val (liftPoint x)⁻¹)
  map_add' := by intros; ext x; simp
  map_smul' := by intros; ext x; simp

/-- The inverse untwisting has no choice of coset representatives. -/
private def tensorToCoind : TensorSpace →ₗ[ZMod 2] coindV PointGroup.subtype pointAction where
  toFun v := ⟨fun g => m12HeartRepresentation g (v (g⁻¹ • (12 : Fin 12))), by
    intro h g
    change m12HeartRepresentation (h.val * g) (v ((h.val * g)⁻¹ • (12 : Fin 12))) =
      m12HeartRepresentation h.val (m12HeartRepresentation g (v (g⁻¹ • (12 : Fin 12))))
    have hh : h.val⁻¹ • (12 : Fin 12) = (12 : Fin 12) :=
      (show h.val⁻¹ ∈ PointGroup from PointGroup.inv_mem h.property)
    simp only [mul_inv_rev, mul_smul, hh, map_mul, Module.End.mul_apply]⟩
  map_add' := by intros; apply Subtype.ext; ext g; simp
  map_smul' := by intros; apply Subtype.ext; ext g; simp

private theorem recover (f : coindV PointGroup.subtype pointAction) (g : M12) :
    m12HeartRepresentation g (coindToTensor f (g⁻¹ • (12 : Fin 12))) = f.val g := by
  let x := g⁻¹ • (12 : Fin 12)
  have hh : g * liftPoint x ∈ PointGroup := by
    change (g * liftPoint x) • (12 : Fin 12) = (12 : Fin 12)
    rw [mul_smul, liftPoint_spec]
    exact smul_inv_smul g (12 : Fin 12)
  have hf := f.property ⟨g * liftPoint x, hh⟩ (liftPoint x)⁻¹
  change f.val ((g * liftPoint x) * (liftPoint x)⁻¹) =
    m12HeartRepresentation (g * liftPoint x) (f.val (liftPoint x)⁻¹) at hf
  change m12HeartRepresentation g
    (m12HeartRepresentation (liftPoint x) (f.val (liftPoint x)⁻¹)) = f.val g
  simpa only [mul_inv_cancel_right, map_mul, Module.End.mul_apply] using hf.symm

/-- Coinduction is the diagonal twelve-fiber action. -/
def coindTensorEquiv : (coind PointGroup.subtype pointAction).Equiv tensorAction := by
  refine Representation.Equiv.mk (LinearEquiv.ofLinearMap coindToTensor tensorToCoind ?_ ?_) ?_
  · apply LinearMap.ext
    intro v
    funext x
    change m12HeartRepresentation (liftPoint x)
      (m12HeartRepresentation (liftPoint x)⁻¹
        (v (((liftPoint x)⁻¹)⁻¹ • (12 : Fin 12)))) = v x
    rw [inv_inv, liftPoint_spec, Representation.self_inv_apply]
  · apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext g
    exact recover f g
  · intro g
    apply LinearMap.ext
    intro f
    funext x
    change m12HeartRepresentation (liftPoint x) (f.val ((liftPoint x)⁻¹ * g)) =
      m12HeartRepresentation g (coindToTensor f (g⁻¹ • x))
    rw [← recover f ((liftPoint x)⁻¹ * g)]
    simp only [map_mul, Module.End.mul_apply, Representation.self_inv_apply,
      mul_inv_rev, inv_inv, mul_smul, liftPoint_spec]

/-- The actual tensor-coinvariant induction is the native 120-dimensional model. -/
def inducedTensorEquiv : inducedHeart.Equiv tensorAction :=
  inducedPointEquiv.trans
    ((Representation.equivOfIso (Rep.indCoindIso (Rep.of pointAction))).trans coindTensorEquiv)

/-- Twelve independent fibers, each the actual ten-dimensional heart. -/
theorem finrank_tensorSpace : Module.finrank (ZMod 2) TensorSpace = 120 := by
  rw [Module.finrank_pi_fintype]
  simp [finrank_m12Heart]

/-- Dimension of the literal induction used by the restriction consumer. -/
theorem finrank_inducedHeart :
    Module.finrank (ZMod 2) (IndV pointEmbedding pointRepresentation) = 120 :=
  inducedTensorEquiv.toLinearEquiv.finrank_eq.trans finrank_tensorSpace

end Representation.MathieuSmall.M12DegreeGap.InducedQuotients
