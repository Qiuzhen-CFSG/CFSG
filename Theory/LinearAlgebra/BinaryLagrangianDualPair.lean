module
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Field.ZMod

/-!
# Polar coordinates for the literal complementary singular subspaces

A nondegenerate polar form pairs two complementary equally sized singular
subspaces perfectly. Restricting the form gives the second subspace as the
dual of the first, and any isometry preserving both acts naturally and
contragrediently in the resulting coordinates. This is the linear bridge
used by source 15.3.56(5) and its later marked three-dimensional action.
-/
@[expose] public noncomputable section
namespace BinaryLagrangianDualPair
open Module
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (B : LinearMap.BilinForm (ZMod 2) V) (E F : Submodule (ZMod 2) V)

def pairing : F →ₗ[ZMod 2] Module.Dual (ZMod 2) E :=
  E.subtype.dualMap.comp (LinearMap.comp B F.subtype)

omit [FiniteDimensional (ZMod 2) V] in
@[simp] theorem pairing_apply (f : F) (e : E) : pairing B E F f e=B f e := rfl

omit [FiniteDimensional (ZMod 2) V] in
theorem pairing_injective (hB : B.Nondegenerate) (hEF : IsCompl E F)
    (hF : ∀ f ∈ F, ∀ f' ∈ F, B f f'=0) : Function.Injective (pairing B E F) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro f hf
  change pairing B E F f=0 at hf
  have hz : (f:V)=0 := hB.1 _ (by
    intro v
    obtain ⟨e,w,he,hw,rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hEF.codisjoint v
    rw [map_add]
    have heq := LinearMap.congr_fun hf (⟨e,he⟩:E)
    change B f e=0 at heq
    rw [heq,hF f f.property w hw,zero_add])
  exact Subtype.ext hz

def dualEquiv (hB : B.Nondegenerate) (hEF : IsCompl E F)
    (hF : ∀ f ∈ F, ∀ f' ∈ F, B f f'=0)
    (hdim : finrank (ZMod 2) F=finrank (ZMod 2) E) :
    F ≃ₗ[ZMod 2] Module.Dual (ZMod 2) E :=
  (pairing B E F).linearEquivOfInjective (pairing_injective B E F hB hEF hF)
    (by rw [Subspace.dual_finrank_eq]; exact hdim)

@[simp] theorem dualEquiv_apply (hB : B.Nondegenerate) (hEF : IsCompl E F)
    (hF : ∀ f ∈ F, ∀ f' ∈ F, B f f'=0)
    (hdim : finrank (ZMod 2) F=finrank (ZMod 2) E) (f : F) (e : E) :
    dualEquiv B E F hB hEF hF hdim f e=B f e := rfl

def coordinates (hB : B.Nondegenerate) (hEF : IsCompl E F)
    (hF : ∀ f ∈ F, ∀ f' ∈ F, B f f'=0)
    (hdim : finrank (ZMod 2) F=finrank (ZMod 2) E) :
    V ≃ₗ[ZMod 2] E × Module.Dual (ZMod 2) E :=
  (Submodule.prodEquivOfIsCompl E F hEF).symm.trans
    ((LinearEquiv.refl (ZMod 2) E).prodCongr (dualEquiv B E F hB hEF hF hdim))

variable (hB : B.Nondegenerate) (hEF : IsCompl E F)
  (hF : ∀ f ∈ F, ∀ f' ∈ F, B f f'=0)
  (hdim : finrank (ZMod 2) F=finrank (ZMod 2) E)

@[simp] theorem coordinates_E (e : E) : coordinates B E F hB hEF hF hdim e=(e,0) := by
  simp only [coordinates,LinearEquiv.trans_apply,
    Submodule.prodEquivOfIsCompl_symm_apply_left,LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply,map_zero]

@[simp] theorem coordinates_F (f : F) :
    coordinates B E F hB hEF hF hdim f=(0,dualEquiv B E F hB hEF hF hdim f) := by
  simp only [coordinates,LinearEquiv.trans_apply,
    Submodule.prodEquivOfIsCompl_symm_apply_right,LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply]

theorem coordinates_mem_E (v : V) : v∈E ↔
    (coordinates B E F hB hEF hF hdim v).2=0 := by
  change v∈E ↔ dualEquiv B E F hB hEF hF hdim
    ((Submodule.prodEquivOfIsCompl E F hEF).symm v).2=0
  rw [LinearEquiv.map_eq_zero_iff]
  exact (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero E F hEF).symm

theorem coordinates_mem_F (v : V) : v∈F ↔
    (coordinates B E F hB hEF hF hdim v).1=0 :=
  (Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero E F hEF).symm

/-- Natural and dual equivariance needs only the literal restrictions of
an isometry to the two marked subspaces. -/
theorem coordinates_equivariant (a : V ≃ₗ[ZMod 2] V)
    (aE : E ≃ₗ[ZMod 2] E) (aF : F ≃ₗ[ZMod 2] F)
    (hE : ∀ e : E, (aE e:V)=a e) (hFa : ∀ f : F, (aF f:V)=a f)
    (ha : ∀ v w, B (a v) (a w)=B v w) (v : V) :
    coordinates B E F hB hEF hF hdim (a v)=
      (aE (coordinates B E F hB hEF hF hdim v).1,
        aE.symm.dualMap (coordinates B E F hB hEF hF hdim v).2) := by
  obtain ⟨p,rfl⟩ := (Submodule.prodEquivOfIsCompl E F hEF).surjective v
  change coordinates B E F hB hEF hF hdim (a ((p.1:V)+(p.2:V)))=_
  rw [map_add,← hE,← hFa,map_add,coordinates_E,coordinates_F]
  have hp : coordinates B E F hB hEF hF hdim ((p.1:V)+(p.2:V))=
      (p.1,dualEquiv B E F hB hEF hF hdim p.2) := by
    rw [map_add,coordinates_E,coordinates_F]
    simp only [Prod.mk_add_mk,add_zero,zero_add]
  change _=(aE (coordinates B E F hB hEF hF hdim ((p.1:V)+(p.2:V))).1,
    aE.symm.dualMap (coordinates B E F hB hEF hF hdim ((p.1:V)+(p.2:V))).2)
  rw [hp]
  apply Prod.ext
  · simp only [Prod.fst_add,add_zero]
  · simp only [Prod.snd_add,zero_add]
    ext e
    change B (aF p.2) e=B p.2 (aE.symm e)
    rw [hFa]
    have he : a (aE.symm e:V)=(e:V) := (hE (aE.symm e)).symm.trans
      (congrArg Subtype.val (aE.apply_symm_apply e))
    rw [← he,ha]

end BinaryLagrangianDualPair
