module

public import Theory.Representation.Mathieu.M23DegreeSpectrum.Coordinates
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Automorphisms
public import Theory.Representation.FactorDegreeFiltration.FiniteDual
public import Theory.AlgebraicGroup.Representations.Coinduction.RightQuotientDual

/-!
# Marking independence and duality of the M23 point inductions

The native ten-dimensional code and cocode extend to the actual automorphism
group of M22. Applying that extension to the change of marking intertwines
any two marked point actions. Blockwise transport preserves the literal
right-coset correction, hence compares their actual M23 inductions.

The native perfect code–cocode pairing, summed over the 23 right cosets,
identifies the two inductions as contragredients. Thus one canonical cocode
filtration suffices for every marking and both ten-dimensional models.
No constituent calculation or small-degree classification is used here.

Source application: Guralnick–Malle, Classification of 2F-modules I,
Proposition 5.1, M23 paragraph, manuscript p.16; the native pair modules
and their automorphism actions are Aschbacher–Smith H.13.1, printed p.395.
-/

public noncomputable section
open Representation Sporadic.Mathieu MathieuCode
namespace Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads

/-- The inverse of the native point-stabilizer identification. -/
@[expose] def canonicalMarking : Models.pointGroup ≃* M22 :=
  m23EquivM22PointStabilizer.symm

private def automorphismAction : (b : Bool) →
    Representation (ZMod 2) (MulAut M22) (Models.Space b)
  | false => m22AutCocodeRepresentation
  | true => m22AutCodeRepresentation

private theorem automorphismAction_inner (b : Bool) (g : M22) :
    automorphismAction b (MulAut.conj g) = Models.action b g := by
  cases b
  · apply LinearMap.ext
    intro v
    exact m22AutCocodeRepresentation_inner g v
  · apply LinearMap.ext
    intro v
    exact m22AutCodeRepresentation_inner g v

/-- Every automorphism twist of either native M22 module is equivalent to it. -/
def actionTwistEquiv (a : MulAut M22) (b : Bool) :
    (Models.action b).Equiv ((Models.action b).comp a.toMonoidHom) := by
  let σ := automorphismAction b
  let E : Models.Space b ≃ₗ[ZMod 2] Models.Space b :=
    LinearEquiv.ofLinearMap (σ a) (σ a⁻¹)
      (by ext v; exact σ.self_inv_apply a v)
      (by ext v; exact σ.inv_self_apply a v)
  refine .mk E ?_
  intro g
  change σ a ∘ₗ Models.action b g = Models.action b (a g) ∘ₗ σ a
  rw [← automorphismAction_inner, ← automorphismAction_inner]
  have h : a * MulAut.conj g = MulAut.conj (a g) * a := by
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  change σ a * σ (MulAut.conj g) = σ (MulAut.conj (a g)) * σ a
  rw [← map_mul, h, map_mul]

/-- Change the marking without changing the native code/cocode choice. -/
def pointMarkingEquiv (e f : Models.pointGroup ≃* M22) (b : Bool) :
    (Models.pointAction e b).Equiv (Models.pointAction f b) := by
  let E := actionTwistEquiv (e.symm.trans f) b
  refine .mk E.toLinearEquiv ?_
  intro g
  simpa only [Models.pointAction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using E.isIntertwining' (e g)

/-- Apply a point-module equivalence in each right-coset block. -/
def coordinateMapEquiv {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    {τ : Representation (ZMod 2) Models.pointGroup V}
    {σ : Representation (ZMod 2) Models.pointGroup W} (E : τ.Equiv σ) :
    (Theory.AlgebraicGroup.Representation.coindRightQuotient Models.pointGroup
      (Rep.of τ)).Equiv
    (Theory.AlgebraicGroup.Representation.coindRightQuotient Models.pointGroup
      (Rep.of σ)) := by
  refine .mk (LinearEquiv.piCongrRight fun _ : Coordinates.Cosets => E.toLinearEquiv) ?_
  intro g
  apply LinearMap.ext
  intro v
  funext q
  change E (Theory.AlgebraicGroup.Representation.coindRightQuotient Models.pointGroup
    (Rep.of τ) g v q) =
    Theory.AlgebraicGroup.Representation.coindRightQuotient Models.pointGroup
      (Rep.of σ) g (fun q => E (v q)) q
  simp only [Theory.AlgebraicGroup.Representation.coindRightQuotient_apply]
  exact IntertwiningMap.isIntertwining τ σ E.toIntertwiningMap _ _

/-- The coordinate actions are equivalent for all actual markings. -/
def coordinateMarkingEquiv (e f : Models.pointGroup ≃* M22) (b : Bool) :
    (Coordinates.action e b).Equiv (Coordinates.action f b) :=
  coordinateMapEquiv (pointMarkingEquiv e f b)

/-- The native pairing remains equivariant for the supplied point marking. -/
def pointDualEquiv (e : Models.pointGroup ≃* M22) :
    (Models.pointAction e true).Equiv (Models.pointAction e false).dual := by
  refine .mk m22CodeCocodeDuality ?_
  intro g
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro u
  have h := LinearMap.congr_fun (m22CodeCocodeDuality_equivariant_native (e g) v) u
  change m22CodeCocodeDuality (m22CodeRepresentation (e g) v) u =
    m22CodeCocodeDuality v (m22CocodeRepresentation (e g⁻¹) u)
  rw [map_inv]
  exact h

/-- Sum the native pairings over right cosets, with the existing correction convention. -/
def coordinateDualEquiv (e : Models.pointGroup ≃* M22) :
    (Coordinates.action e true).Equiv (Coordinates.action e false).dual :=
  (coordinateMapEquiv (pointDualEquiv e)).trans
    (Theory.AlgebraicGroup.Representation.rightQuotientDualEquiv
      Models.pointGroup (Models.pointAction e false))

/-- Marking independence for the original quotient-tensor inductions. -/
def inducedMarkingEquiv (e f : Models.pointGroup ≃* M22) (b : Bool) :
    (Models.induced e b).Equiv (Models.induced f b) :=
  ((Coordinates.inducedEquiv e b).trans (coordinateMarkingEquiv e f b)).trans
    (Coordinates.inducedEquiv f b).symm

/-- The original code induction is the contragredient of the cocode induction. -/
def inducedDualEquiv (e : Models.pointGroup ≃* M22) :
    (Models.induced e true).Equiv (Models.induced e false).dual :=
  ((Coordinates.inducedEquiv e true).trans (coordinateDualEquiv e)).trans
    (Coordinates.inducedEquiv e false).contragredient

end Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads
