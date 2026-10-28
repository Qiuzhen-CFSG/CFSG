module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsNine.Reduction
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsNine.Simple.Certificate

/-!
# No mixed tensor point module extends to the actual triple Mathieu cover

An actual binary point-module equivalence transports the full-group action.
The marked central scalar is omega or omega squared in the two tensor
orientations. Centrality forces every transported operator to commute with
omega, hence to be F₄-linear. The actual involution B then satisfies the
three matrix equations ruled out by the checked finite certificate.

No irreducibility, absolute irreducibility, faithfulness or Schur-field
hypothesis is needed once the specified binary equivalence is supplied.
Source context: Guralnick–Malle I, Proposition 5.1, pp.15–16, and
Aschbacher–Smith H.12.1, pp.393–394. Literal word identities and matrix
attribution are retained in Uniqueness/PointRestriction/ExtensionExclusion.
-/

@[expose] public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsNine.Simple
open Representation
open Uniqueness Uniqueness.PointRestriction Uniqueness.PointRestriction.PointModel
open Uniqueness.PointRestriction.ExtensionExclusion
open Representation.SL3FourNaturalDual
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) M22TripleCover V)
  (b : Bool) (e : (pointAction ρ).Equiv (mixedBinaryRep b))

def fullBinary : Representation (ZMod 2) M22TripleCover Space9 :=
  e.toLinearEquiv.conjRingEquiv.toMonoidHom.comp ρ

lemma fullBinary_on_point (g : pointStabilizer) :
    fullBinary ρ b e g = mixedBinaryRep b (pointStabilizerEquiv g) := by
  apply LinearMap.ext
  intro v
  change e (ρ g (e.symm v)) = mixedBinaryRep b (pointStabilizerEquiv g) v
  have he := LinearMap.congr_fun (e.isIntertwining' (pointStabilizerEquiv g)) (e.symm v)
  change e (ρ ((pointStabilizerEquiv.symm (pointStabilizerEquiv g) : pointStabilizer) :
      M22TripleCover) (e.symm v)) =
    mixedBinaryRep b (pointStabilizerEquiv g) (e (e.symm v)) at he
  rwa [pointStabilizerEquiv.symm_apply_apply, e.apply_symm_apply] at he

lemma fullBinary_scalar (v : Space9) :
    fullBinary ρ b e scalar v = centralValue b • v := by
  have hz := fullBinary_on_point ρ b e pointScalar
  rw [pointStabilizerEquiv_pointScalar] at hz
  exact (LinearMap.congr_fun hz v).trans (mixedBinaryRep_central b v)

lemma fullBinary_omega (g : M22TripleCover) (v : Space9) :
    fullBinary ρ b e g ((QuadraticAlgebra.omega : SL3FourNaturalDual.F) • v) =
      (QuadraticAlgebra.omega : SL3FourNaturalDual.F) • fullBinary ρ b e g v := by
  have h (w : Space9) : fullBinary ρ b e g (centralValue b • w) =
      centralValue b • fullBinary ρ b e g w := by
    have hc := (show Commute g scalar from
      Subgroup.mem_center_iff.mp scalar_mem_center g).map (fullBinary ρ b e)
    have he := LinearMap.congr_fun hc.eq w
    change fullBinary ρ b e g (fullBinary ρ b e scalar w) =
      fullBinary ρ b e scalar (fullBinary ρ b e g w) at he
    simpa only [fullBinary_scalar] using he
  cases b with
  | false => exact h v
  | true =>
    have he := h (centralValue true • v)
    rw [h v, smul_smul, smul_smul] at he
    have hw : centralValue true * centralValue true = (QuadraticAlgebra.omega : SL3FourNaturalDual.F) := by
      decide +kernel
    rwa [hw] at he

/-- Commutation with the marked center upgrades every full-group operator
from binary linearity to linearity over the actual coefficient field. -/
def fullField : Representation SL3FourNaturalDual.F M22TripleCover Space9 where
  toFun g := {
    (fullBinary ρ b e g).toAddHom with
    map_smul' := by
      intro a v
      change fullBinary ρ b e g (a • v) = a • fullBinary ρ b e g v
      have ha : a = algebraMap (ZMod 2) SL3FourNaturalDual.F a.re +
          a.im • (QuadraticAlgebra.omega : SL3FourNaturalDual.F) :=
        QuadraticAlgebra.mk_eq_add_smul_omega a.re a.im
      have hs (w : Space9) : a • w = a.re • w +
          a.im • ((QuadraticAlgebra.omega : SL3FourNaturalDual.F) • w) := by
        conv_lhs => rw [ha]
        rw [add_smul, algebraMap_smul, smul_assoc]
      rw [hs, map_add, map_smul, map_smul, fullBinary_omega, hs] }
  map_one' := by
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun (fullBinary ρ b e).map_one v
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun ((fullBinary ρ b e).map_mul g h) v

def fullMatrix : M22TripleCover →* Matrix9 :=
  Matrix.toLinAlgEquiv'.symm.toMonoidHom.comp (fullField ρ b e)

lemma fullMatrix_on_point (g : pointStabilizer) :
    fullMatrix ρ b e g = mixedMatrix b (pointStabilizerEquiv g) := by
  apply Matrix.toLinAlgEquiv'.injective
  change Matrix.toLinAlgEquiv' (Matrix.toLinAlgEquiv'.symm (fullField ρ b e g)) = _
  rw [AlgEquiv.apply_symm_apply]
  apply LinearMap.ext
  intro v
  exact LinearMap.congr_fun (fullBinary_on_point ρ b e g) v

private lemma involution_intertwines {G R : Type*} [Group G] [Monoid R]
    (f : G →* R) (x k : G) (hx : x * x = 1) :
    f x * f k = f (x * k * x) * f x := by
  rw [← map_mul, ← map_mul]
  apply congrArg f
  rw [mul_assoc, mul_assoc, hx, mul_one]

/-- The actual involution B supplies all three equations used by the finite
obstruction, after a binary equivalence with a mixed tensor model. -/
lemma fullMatrix_equations :
    let X := fullMatrix ρ b e coreGeneratorB
    X * X = 1 ∧
      X * mixedMatrix b (classicalWord 0) = mixedMatrix b (classicalWord 2) * X ∧
      X * mixedMatrix b (classicalWord 1) = mixedMatrix b (classicalWord 3) * X := by
  let f := fullMatrix ρ b e
  have hw (j : Fin 4) : f (localWord j) = mixedMatrix b (classicalWord j) := by
    rw [fullMatrix_on_point, pointStabilizerEquiv_localWord]
  have hi (k : M22TripleCover) :
      f coreGeneratorB * f k = f (coreGeneratorB * k * coreGeneratorB) * f coreGeneratorB := by
    exact involution_intertwines f _ _ PointExtension.generatorB_sq
  refine ⟨?_, ?_, ?_⟩
  · change f coreGeneratorB * f coreGeneratorB = 1
    exact (f.map_mul _ _).symm.trans
      ((congrArg f PointExtension.generatorB_sq).trans f.map_one)
  · rw [← hw 0, ← hw 2]
    exact hi PointExtension.wordS
  · rw [← hw 1, ← hw 3]
    exact hi PointExtension.wordT

include ρ b e in
/-- Neither actual mixed binary point module extends across B. This is the
consumer of the finite matrix obstruction and the central-linearity bridge. -/
theorem no_mixed_extension : False := by
  obtain ⟨hsq, hS, hT⟩ := fullMatrix_equations ρ b e
  exact Generated.excludes b (fullMatrix ρ b e coreGeneratorB) hsq hS hT

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsNine.Simple
