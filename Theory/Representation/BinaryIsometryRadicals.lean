module
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.GroupTheory.PCoreInRestriction
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Algebra

/-!
# Binary isometry kernels and parabolic two-cores

The pointwise kernel of a self-orthogonal half-space has square one:
isometry moves every vector into that fixed half-space. More generally,
the kernel on three invariant binary layers has fourth power one. These
kernels are normal in the corresponding stabilizers, so lie in their
actual two-cores. A point-stabilizer application uses its invariant polar
hyperplane and the marked point, keeping the original representation.

Source application: Aschbacher--Smith, The Classification of Quasithin
Groups, 12.9.4, printed pp.859--860, the two parabolic radical containments.
-/

public noncomputable section
open Subgroup Module
namespace Representation.BinaryIsometryRadicals
open BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The pointwise kernel on a self-orthogonal half-space is a two-group. -/
theorem halfSpace_kernel_isPGroup
    (hf : Function.Injective ρ) (B : LinearMap.BilinForm (ZMod 2) V)
    (hB : ∀ g u w, B (ρ g u) (ρ g w) = B u w)
    (W : Submodule (ZMod 2) V) (hW : W = B.orthogonal W) (P : Subgroup G) :
    IsPGroup 2 (subspaceKernel ρ W P) := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · intro a
    exact ⟨0,Subtype.ext (hf (Subsingleton.elim _ _))⟩
  let : CharP (Module.End (ZMod 2) V) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (Module.End (ZMod 2) V)).injective 2
  intro a
  refine ⟨1,?_⟩
  apply Subtype.ext
  apply hf
  have hd (w : V) : ρ a w - w ∈ W := by
    apply hW.ge
    intro u hu
    change B u (ρ a w - w) = 0
    rw [map_sub]
    apply sub_eq_zero.mpr
    calc
      B u (ρ a w) = B (ρ a u) (ρ a w) := by rw [a.property.2 u hu]
      _ = B u w := hB a u w
  have hn : (ρ a - 1)^2 = 0 := by
    ext w
    change ρ a (ρ a w - w) - (ρ a w - w) = 0
    rw [a.property.2 _ (hd w),sub_self]
  rw [sub_pow_char_of_commute 2 (Commute.one_right (ρ a)),one_pow] at hn
  simpa only [Subgroup.coe_pow,Subgroup.coe_one,pow_one,map_pow,map_one] using sub_eq_zero.mp hn

/-- The actual pointwise kernel lies in the stabilizer's two-core. -/
theorem halfSpace_kernel_le_pCoreIn
    (hf : Function.Injective ρ) (B : LinearMap.BilinForm (ZMod 2) V)
    (hB : ∀ g u w, B (ρ g u) (ρ g w) = B u w)
    (W : Submodule (ZMod 2) V) (hW : W = B.orthogonal W)
    (P : Subgroup G) (hP : P ≤ subspaceStabilizer ρ W) :
    subspaceKernel ρ W P ≤ P.pCoreIn 2 := by
  have hn := subspaceKernel_normal ρ W P hP
  exact le_pCoreIn_of_normalizes (halfSpace_kernel_isPGroup ρ hf B hB W hW P)
    (subspaceKernel_le ρ W P)
    ((normal_subgroupOf_iff_le_normalizer (subspaceKernel_le ρ W P)).mp hn)

/-- The kernel on three successive layers of an invariant flag. -/
def flagKernel (A H : Submodule (ZMod 2) V) (P : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ P ∧ (∀ a ∈ A, ρ g a = a) ∧
    (∀ w ∈ H, ρ g w - w ∈ A) ∧ (∀ w, ρ g w - w ∈ H)}
  one_mem' := by simp
  mul_mem' := by
    rintro g h ⟨hg,hgA,hgH,hgV⟩ ⟨hh,hhA,hhH,hhV⟩
    refine ⟨P.mul_mem hg hh,?_,?_,?_⟩
    · intro a ha
      simp only [map_mul,Module.End.mul_apply,hhA a ha,hgA a ha]
    · intro w hw
      have hm : ρ (g*h) w - w = (ρ g (ρ h w - w)) + (ρ g w - w) := by
        simp only [map_mul,Module.End.mul_apply,map_sub]
        abel
      rw [hm,hgA _ (hhH w hw)]
      exact A.add_mem (hhH w hw) (hgH w hw)
    · intro w
      have hm : ρ (g*h) w - w = (ρ g (ρ h w) - ρ h w) + (ρ h w - w) := by
        simp only [map_mul,Module.End.mul_apply]
        abel
      rw [hm]
      exact H.add_mem (hgV _) (hhV w)
  inv_mem' := by
    rintro g ⟨hg,hgA,hgH,hgV⟩
    have hinv (w : V) : ρ g (ρ g⁻¹ w) = w := Representation.self_inv_apply ρ g w
    have hback (w : V) : ρ g⁻¹ w - w = -(ρ g (ρ g⁻¹ w) - ρ g⁻¹ w) := by
      rw [hinv,neg_sub]
    refine ⟨P.inv_mem hg,?_,?_,?_⟩
    · intro a ha
      have hh := congrArg (ρ g⁻¹) (hgA a ha)
      simpa only [Representation.inv_self_apply] using hh.symm
    · intro w hw
      have hw' : ρ g⁻¹ w ∈ H := by
        have hh := H.sub_mem hw (hgV (ρ g⁻¹ w))
        rw [hinv,sub_sub_cancel] at hh
        exact hh
      rw [hback]
      exact A.neg_mem (hgH _ hw')
    · intro w
      rw [hback]
      exact H.neg_mem (hgV _)

/-- The flag kernel is normal relative to any group preserving both terms. -/
theorem flagKernel_normalizes (A H : Submodule (ZMod 2) V) (P : Subgroup G)
    (hA : P ≤ subspaceStabilizer ρ A) (hH : P ≤ subspaceStabilizer ρ H) :
    P ≤ normalizer (flagKernel ρ A H P : Set G) := by
  apply le_normalizer_iff.mpr
  rintro g hg a ⟨ha,haA,haH,haV⟩
  have he (w : V) : ρ (g*a*g⁻¹) w - w = ρ g (ρ a (ρ g⁻¹ w) - ρ g⁻¹ w) := by
    rw [map_sub,Representation.self_inv_apply]
    simp only [map_mul,Module.End.mul_apply]
  refine ⟨P.mul_mem (P.mul_mem hg ha) (P.inv_mem hg),?_,?_,?_⟩
  · intro w hw
    apply sub_eq_zero.mp
    rw [he,haA _ ((hA (P.inv_mem hg) w).mpr hw),sub_self,map_zero]
  · intro w hw
    rw [he]
    exact (hA hg _).mpr (haH _ ((hH (P.inv_mem hg) w).mpr hw))
  · intro w
    rw [he]
    exact (hH hg _).mpr (haV _)

/-- A faithful kernel on three binary layers has exponent dividing four. -/
theorem flagKernel_isPGroup (hf : Function.Injective ρ)
    (A H : Submodule (ZMod 2) V) (P : Subgroup G) :
    IsPGroup 2 (flagKernel ρ A H P) := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · intro a
    exact ⟨0,Subtype.ext (hf (Subsingleton.elim _ _))⟩
  let : CharP (Module.End (ZMod 2) V) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (Module.End (ZMod 2) V)).injective 2
  intro a
  refine ⟨2,?_⟩
  apply Subtype.ext
  apply hf
  have hn : (ρ a - 1)^3 = 0 := by
    ext w
    change ρ a ((ρ a) ((ρ a) w - w) - ((ρ a) w - w)) -
      ((ρ a) ((ρ a) w - w) - ((ρ a) w - w)) = 0
    rw [a.property.2.1 _ (a.property.2.2.1 _ (a.property.2.2.2 w)),sub_self]
  have hn4 : (ρ a - 1)^4 = 0 := by rw [show 4 = 3+1 from rfl,pow_succ,hn,zero_mul]
  rw [show 4 = 2^2 from rfl,sub_pow_char_pow_of_commute 2 2 (Commute.one_right (ρ a)),
    one_pow] at hn4
  simpa only [Subgroup.coe_pow,Subgroup.coe_one,map_pow,map_one] using sub_eq_zero.mp hn4

/-- The three-layer kernel lies in the two-core of its actual stabilizer. -/
theorem flagKernel_le_pCoreIn (hf : Function.Injective ρ)
    (A H : Submodule (ZMod 2) V) (P : Subgroup G)
    (hA : P ≤ subspaceStabilizer ρ A) (hH : P ≤ subspaceStabilizer ρ H) :
    flagKernel ρ A H P ≤ P.pCoreIn 2 :=
  le_pCoreIn_of_normalizes (flagKernel_isPGroup ρ hf A H P)
    (fun _ h => h.1) (flagKernel_normalizes ρ A H P hA hH)

/-- Hyperplane displacements into a fixed point lie in the point-stabilizer core. -/
theorem le_pointCore_of_displacement
    (hf : Function.Injective ρ) (B : LinearMap.BilinForm (ZMod 2) V)
    (hB : ∀ g u w, B (ρ g u) (ρ g w) = B u w) (v : V)
    (P R : Subgroup G) (hP : ∀ g ∈ P, ρ g v = v) (hRP : R ≤ P)
    (hR : ∀ g ∈ R, ∀ w ∈ (B v).ker, ρ g w - w ∈ Submodule.span (ZMod 2) {v}) :
    R ≤ P.pCoreIn 2 := by
  let A := Submodule.span (ZMod 2) {v}
  let H := (B v).ker
  have hfix (g : G) (hg : g ∈ P) (w : V) (hw : w ∈ A) : ρ g w = w := by
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul,hP g hg]
  have hp (g : G) (hg : g ∈ P) (w : V) : B v (ρ g w) = B v w := by
    calc
      _ = B (ρ g v) (ρ g w) := by rw [hP g hg]
      _ = _ := hB g v w
  have hA : P ≤ subspaceStabilizer ρ A :=
    le_subspaceStabilizer ρ A (fun g hg w hw => (hfix g hg w hw).symm ▸ hw)
  have hH : P ≤ subspaceStabilizer ρ H := by
    intro g hg w
    change B v (ρ g w) = 0 ↔ B v w = 0
    rw [hp g hg]
  apply le_trans ?_ (flagKernel_le_pCoreIn ρ hf A H P hA hH)
  intro g hg
  refine ⟨hRP hg,hfix g (hRP hg),hR g hg,?_⟩
  intro w
  change B v (ρ g w - w) = 0
  rw [map_sub,hp g (hRP hg),sub_self]

end Representation.BinaryIsometryRadicals
