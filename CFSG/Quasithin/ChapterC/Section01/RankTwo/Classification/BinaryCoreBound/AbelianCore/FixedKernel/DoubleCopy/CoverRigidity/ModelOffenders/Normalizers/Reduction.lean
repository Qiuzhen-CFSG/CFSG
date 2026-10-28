module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.FixedKernel.DoubleCopy.CoverRigidity.ModelOffenders.Actors

/-!
# From twist stabilizers and centralizers to the full linear normalizer

Conjugation in the full linear normalizer induces an automorphism of the
faithful matrix-group image, and an actual intertwining equivalence with
its twist. If every such automorphism is inner, multiplying the normalizer
element by a matrix-group actor leaves an element of the full centralizer.

This is the group-theoretic assembly for the independent universal-cover
normalizer argument supporting Aschbacher–Smith C.1.34(2),(5), printed
pp.136–137, with the covering convention of I.1.5, printed p.408.
-/

@[expose] public section
open Representation Representation.OneCohomology
namespace CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.DoubleCopy.CoverModels.ModelOffenders
noncomputable section
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

/-- A faithful doubled-natural quotient makes the literal linear action faithful. -/
lemma linearAction_injective_of_cover (τ : Representation (ZMod 2) MatrixGroup M)
    (p : τ.IntertwiningMap natural) (hp : IsCover p) : Function.Injective (linearAction τ) := by
  intro g h he
  apply natural_injective
  apply LinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := hp.1 v
  rw [← p.isIntertwining, ← p.isIntertwining]
  exact congrArg p (LinearEquiv.congr_fun he w)

/-- Conjugation by a full linear normalizer element, transported to the actual matrix group. -/
def normalizerAut (τ : Representation (ZMod 2) MatrixGroup M)
    (hτ : Function.Injective (linearAction τ)) (f : normalizer τ) : MulAut MatrixGroup :=
  let e := MonoidHom.ofInjective hτ
  (e.trans ((linearAction τ).range.normalizerMonoidHom f)).trans e.symm

lemma normalizerAut_apply (τ : Representation (ZMod 2) MatrixGroup M)
    (hτ : Function.Injective (linearAction τ)) (f : normalizer τ) (g : MatrixGroup) :
    linearAction τ (normalizerAut τ hτ f g) = f.val * linearAction τ g * f.val⁻¹ := by
  exact MonoidHom.apply_ofInjective_symm hτ _

/-- Every normalizer element supplies an actual equivalence with the induced automorphism twist. -/
def normalizerTwist (τ : Representation (ZMod 2) MatrixGroup M)
    (hτ : Function.Injective (linearAction τ)) (f : normalizer τ) :
    Representation.Equiv (τ.comp (normalizerAut τ hτ f).toMonoidHom) τ where
  toLinearEquiv := f.val.symm
  isIntertwining' g := by
    apply LinearMap.ext
    intro w
    have h := LinearEquiv.congr_fun (normalizerAut_apply τ hτ f g) w
    change τ (normalizerAut τ hτ f g) w = f.val (τ g (f.val.symm w)) at h
    change f.val.symm (τ (normalizerAut τ hτ f g) w) = τ g (f.val.symm w)
    rw [h, f.val.symm_apply_apply]

/-- Innerness of twist stabilizers reduces full normalizer coverage to its centralizer. -/
lemma normalizer_le_of_inner_stabilizers (τ : Representation (ZMod 2) MatrixGroup M)
    (hτ : Function.Injective (linearAction τ)) (K : Subgroup (BinaryGL M))
    (himage : (linearAction τ).range ≤ K)
    (hcentral : Subgroup.centralizer ((linearAction τ).range : Set (BinaryGL M)) ≤ K)
    (hinner : ∀ a : MulAut MatrixGroup,
      Nonempty (Representation.Equiv (τ.comp a.toMonoidHom) τ) → a ∈ MulAut.innerSubgroup MatrixGroup) :
    normalizer τ ≤ K := by
  intro f hf
  let n : normalizer τ := ⟨f, hf⟩
  obtain ⟨g, hg⟩ := hinner (normalizerAut τ hτ n) ⟨normalizerTwist τ hτ n⟩
  have hc : linearAction τ g⁻¹ * f ∈
      Subgroup.centralizer ((linearAction τ).range : Set (BinaryGL M)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, rfl⟩
    have h := normalizerAut_apply τ hτ n x
    rw [← hg] at h
    change linearAction τ (g * x * g⁻¹) = f * linearAction τ x * f⁻¹ at h
    have he := congrArg (fun t => linearAction τ g⁻¹ * t * f) h
    simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel,
      mul_one] using he
  have hmem := K.mul_mem (himage ⟨g, rfl⟩) (hcentral hc)
  simpa only [map_inv, ← mul_assoc, mul_inv_cancel, one_mul] using hmem

end
end CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.DoubleCopy.CoverModels.ModelOffenders
