module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.ModuleTransport

/-!
# Changing only the target coordinates of the natural quotient

Conjugate the natural SL₂(4) marking by k in S₅ and pull back its S₅ action
by conjugation by k⁻¹. Composing the original projection with the old action
of k⁻¹ gives the compatible equivariant projection. This is a coordinated
change of target coordinates: the original quotient map H → H/O₂(H) → S₅,
the action on U/V₁, and every actual source subgroup are retained.

The inverse action proves surjectivity and equality of kernels. Thus U₀,
module separation and the literal section-centralizer assertion are unchanged.
Existence of an upper-root alignment is proved in the higher SourceMarking
extension, using the original parabolic image rather than a marking assumption.

Source: Aschbacher–Smith, Remark 14.7.64, Lemma 14.7.65 and the proof of
14.7.70, printed pp.1069–1074.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.L2FourAction
open Representation

/-- Conjugate the natural marking and pull back the target action together. -/
def remark (r : L2FourAction) (k : S5) : L2FourAction where
  marking := r.marking.trans (MulAut.conjNormal k)
  action := r.action.comp (MulAut.conj k⁻¹).toMonoidHom
  restriction g v := by
    change r.action (k⁻¹ * (k * (r.marking g : S5) * k⁻¹) * (k⁻¹)⁻¹) v = _
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using r.restriction g v
/-- The new marking is conjugated in the actual five-point permutation group. -/
@[simp] theorem remark_marking_apply (r : L2FourAction) (k : S5)
    (g : SL2FourNatural.SL) :
    ((r.remark k).marking g : S5) = k * (r.marking g : S5) * k⁻¹ := rfl

/-- The target representation is pulled back by the inverse conjugation. -/
@[simp] theorem remark_action_apply (r : L2FourAction) (k x : S5) (v : FourSpace) :
    (r.remark k).action x v = r.action (k⁻¹ * x * k) v := by
  change r.action (k⁻¹ * x * (k⁻¹)⁻¹) v = _
  rw [inv_inv]

end CFSG.Quasithin.ChapterJ.L2FourAction

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
open Representation Subgroup Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (k : ChapterJ.S5)

private def remarkProjection : d.action.IntertwiningMap
    ((d.naturalQuotient.remark k).action.comp d.qH) where
  toLinearMap := (d.naturalQuotient.action k⁻¹).comp d.projection.toLinearMap
  isIntertwining' h := by
    apply LinearMap.ext
    intro w
    change d.naturalQuotient.action k⁻¹ (d.projection (d.action h w)) =
      d.naturalQuotient.action (k⁻¹ * d.qH h * (k⁻¹)⁻¹)
        (d.naturalQuotient.action k⁻¹ (d.projection w))
    rw [show d.projection (d.action h w) = d.naturalQuotient.action (d.qH h)
      (d.projection w) from LinearMap.congr_fun (d.projection.isIntertwining' h) w]
    simp only [← Module.End.mul_apply, ← map_mul, inv_inv, mul_inv_cancel_right]

private theorem remarkProjection_onto : Function.Surjective (remarkProjection d k) := by
  intro v
  obtain ⟨w, hw⟩ := d.projection_onto (d.naturalQuotient.action k v)
  refine ⟨w, ?_⟩
  change d.naturalQuotient.action k⁻¹ (d.projection w) = v
  rw [hw, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

private theorem remarkProjection_ker : (remarkProjection d k).toLinearMap.ker =
    d.projection.toLinearMap.ker := by
  ext w
  change d.naturalQuotient.action k⁻¹ (d.projection w) = 0 ↔ d.projection w = 0
  constructor
  · intro h
    have h' := congrArg (d.naturalQuotient.action k) h
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply, map_zero] using h'
  · intro h
    rw [h, map_zero]

/-- Change only the natural target marking, action and projection coordinates. -/
def remark : Data T L V F W :=
  { d with naturalQuotient := d.naturalQuotient.remark k
           projection :=
             { toLinearMap := (d.naturalQuotient.action k⁻¹).comp d.projection.toLinearMap
               isIntertwining' := by exact (remarkProjection d k).isIntertwining' }
           projection_onto := by exact remarkProjection_onto d k
           fixed_kernel := by exact (remarkProjection_ker d k).trans d.fixed_kernel }

@[simp] theorem remark_counterexample : (d.remark k).counterexample = d.counterexample := rfl
@[simp] theorem remark_natural : (d.remark k).natural = d.natural := rfl
@[simp] theorem remark_model : (d.remark k).model = d.model := rfl
@[simp] theorem remark_qH : (d.remark k).qH = d.qH := rfl
@[simp] theorem remark_action : (d.remark k).action = d.action := rfl
@[simp] theorem remark_conjugationSection :
    (d.remark k).conjugationSection = d.conjugationSection := rfl
@[simp] theorem remark_U₀ : (d.remark k).U₀ = d.U₀ := rfl
@[simp] theorem remark_moduleSeparation :
    (d.remark k).ModuleSeparation ↔ d.ModuleSeparation := Iff.rfl
@[simp] theorem remark_sectionCentralizer :
    (d.remark k).SectionCentralizer ↔ d.SectionCentralizer := Iff.rfl

/-- The precise new projection in terms of the old target coordinates. -/
@[simp] theorem remark_projection_apply (w : W) :
    (d.remark k).projection w = d.naturalQuotient.action k⁻¹ (d.projection w) := rfl

/-- The kernel defining the actual source filtration does not change. -/
@[simp] theorem remark_projection_ker :
    (d.remark k).projection.toLinearMap.ker = d.projection.toLinearMap.ker :=
  remarkProjection_ker d k

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
