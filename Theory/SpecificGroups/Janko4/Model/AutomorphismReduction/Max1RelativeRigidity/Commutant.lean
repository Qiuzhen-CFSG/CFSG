module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1RelativeRigidity.Core
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1RelativeRigidity.CommutantData
import Mathlib.Tactic.Group
/-!
# Scalar commutant of the actual max1 action on its binary kernel

The word `xy` fixes only the identity and the seed `(xy)^14` in the actual
kernel. This is checked on 2048 bounded masks, using the proved coordinate
bijection and right-conjugation tables. An endomorphism commuting with the
left actions of x and y commutes with every local conjugation. Its value on
the seed is therefore either the identity or the seed. Since the seed
normally generates the kernel inside max1, these two cases force the zero
endomorphism or the identity endomorphism, respectively.

This proves the full scalar commutant without enumerating endomorphisms or
assuming irreducibility. Injectivity eliminates the zero endomorphism for an
automorphism. Left conjugation is used for equivariance; the fixed-mask check
is explicitly transported through the inverse of xy to respect right tables.

Source: literal ATLAS `J4G1-max1W1`, documented in `Cardinality.Subgroup`;
local structure motivation: GLS3, Table 5.3i.
-/

set_option maxRecDepth 10000
@[expose] public section
namespace Janko4.Max1RelativeRigidity
open Cardinality Cardinality.KernelCount Cardinality.QuotientCount.Image
open Simplicity.Max1Fusion.KernelOrbits
attribute [local irreducible] basis modelGroup matrixA matrixB localKernel
  max1Subgroup localX localY localKernelSeed

/-- Equivariance at the actual generators extends to their generated group. -/
theorem equivariant_of_generators (f : K →* K)
    (hx : ∀ e, f (MulAut.conjNormal x e) = MulAut.conjNormal x (f e))
    (hy : ∀ e, f (MulAut.conjNormal y e) = MulAut.conjNormal y (f e))
    (c : M) (e : K) : f (MulAut.conjNormal c e) = MulAut.conjNormal c (f e) := by
  have hc : c ∈ Subgroup.closure {x, y} := by rw [localXY_generate]; trivial
  suffices ∀ e : K, f (MulAut.conjNormal c e) = MulAut.conjNormal c (f e) from this e
  induction hc using Subgroup.closure_induction with
  | mem c hc =>
    rcases hc with rfl | hc
    · exact hx
    · obtain rfl := Set.mem_singleton_iff.mp hc; exact hy
  | one => simp
  | mul a b _ _ iha ihb =>
    intro e
    simp only [map_mul, MulAut.mul_apply, iha, ihb]
  | inv a _ ih =>
    intro e
    apply (MulAut.conjNormal a : MulAut K).injective
    have h := ih ((MulAut.conjNormal a⁻¹ : MulAut K) e)
    simpa only [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      MulAut.one_apply] using h.symm

/-- The actual normal generator of the binary kernel, with its membership proof. -/
def seed : K := ⟨localKernelSeed matrixA_mul_self matrixB_pow_four,
  localKernelSeed_mem matrixA_mul_self matrixB_pow_four⟩

/-- Normal generation makes an equivariant map determined by the seed. -/
theorem equivariant_ext (f g : K →* K)
    (hf : ∀ (c : M) (e : K), f (MulAut.conjNormal c e) = MulAut.conjNormal c (f e))
    (hg : ∀ (c : M) (e : K), g (MulAut.conjNormal c e) = MulAut.conjNormal c (g e))
    (hs : f seed = g seed) : f = g := by
  let T : Subgroup M := (f.eqLocus g).map K.subtype
  let : T.Normal := ⟨by
    intro a ha c
    obtain ⟨e, he, rfl⟩ := ha
    refine ⟨MulAut.conjNormal c e, ?_, rfl⟩
    change f (MulAut.conjNormal c e) = g (MulAut.conjNormal c e)
    rw [hf, hg, show f e = g e from he]⟩
  have hK : K ≤ T := by
    unfold K localKernel
    apply Subgroup.normalClosure_le_normal
    rintro a rfl
    exact ⟨seed, hs, rfl⟩
  apply MonoidHom.ext
  intro e
  obtain ⟨w, hw, he⟩ := hK e.property
  have he' : w = e := Subtype.ext he
  subst w
  exact hw

open CommutantData

/-- The right action of xy fixes exactly the identity and the kernel seed. -/
theorem fixed_xy (e : K) (he : MulAut.conjNormal (x * y)⁻¹ e = e) :
    e = 1 ∨ e = seed := by
  obtain ⟨m, rfl⟩ := maskEquiv.surjective e
  have hr : (x * y)⁻¹ * (maskEquiv m : M) * (x * y) =
      maskValue matrixA_mul_self matrixB_pow_four (maskImage yMasks (maskImage xMasks m.val)) := by
    calc
      _ = y⁻¹ * (x⁻¹ * (maskEquiv m : M) * x) * y := by group
      _ = _ := by rw [maskEquiv_apply, right_conj_mask_x, right_conj_mask_y]
  have hc := congrArg (fun z : K => (z : M)) he
  change (x * y)⁻¹ * (maskEquiv m : M) * ((x * y)⁻¹)⁻¹ = _ at hc
  rw [inv_inv, hr] at hc
  have hm : (⟨maskImage yMasks (maskImage xMasks m.val), (xy_fixed_masks m).1⟩ : Fin 2048) = m :=
    maskValue_injective (Subtype.ext hc)
  rcases (xy_fixed_masks m).2 (congrArg Fin.val hm) with h | h
  · subst m
    exact Or.inl (maskValue_zero matrixA_mul_self matrixB_pow_four)
  · subst m
    exact Or.inr (Subtype.ext (maskValue_one matrixA_mul_self matrixB_pow_four))

/-- The two scalars are the trivial homomorphism and the identity homomorphism. -/
theorem commutant_endomorphism (f : K →* K)
    (hx : ∀ e, f (MulAut.conjNormal x e) = MulAut.conjNormal x (f e))
    (hy : ∀ e, f (MulAut.conjNormal y e) = MulAut.conjNormal y (f e)) :
    f = 1 ∨ f = MonoidHom.id K := by
  have hf := equivariant_of_generators f hx hy
  have hs : MulAut.conjNormal (x * y)⁻¹ seed = seed := by
    apply Subtype.ext
    change (x * y)⁻¹ * localKernelSeed matrixA_mul_self matrixB_pow_four *
      ((x * y)⁻¹)⁻¹ = localKernelSeed matrixA_mul_self matrixB_pow_four
    rw [localKernelSeed]
    change (x * y)⁻¹ * (x * y) ^ 14 * ((x * y)⁻¹)⁻¹ = (x * y) ^ 14
    rw [inv_inv, (Commute.self_pow (x * y) 14).inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
  have hfs : MulAut.conjNormal (x * y)⁻¹ (f seed) = f seed := by rw [← hf, hs]
  rcases fixed_xy (f seed) hfs with h | h
  · left
    exact equivariant_ext f 1 hf (by intro c e; simp) (by simpa using h)
  · right
    exact equivariant_ext f (MonoidHom.id K) hf (by intro c e; rfl) h

/-- The actual kernel action has trivial centralizer in its automorphism group. -/
theorem commutant_automorphism (kappa : MulAut K)
    (hx : Commute kappa (MulAut.conjNormal x : MulAut K))
    (hy : Commute kappa (MulAut.conjNormal y : MulAut K)) : kappa = 1 := by
  have hx' : ∀ e, kappa (MulAut.conjNormal x e) = MulAut.conjNormal x (kappa e) :=
    fun e => DFunLike.congr_fun hx.eq e
  have hy' : ∀ e, kappa (MulAut.conjNormal y e) = MulAut.conjNormal y (kappa e) :=
    fun e => DFunLike.congr_fun hy.eq e
  rcases commutant_endomorphism kappa.toMonoidHom hx' hy' with h | h
  · have hseed : seed = 1 := kappa.injective (by
      simpa only [MulEquiv.coe_toMonoidHom, map_one, MonoidHom.one_apply] using DFunLike.congr_fun h seed)
    have hzero : maskEquiv 1 = maskEquiv 0 := by
      have h1 : maskEquiv 1 = seed := Subtype.ext (maskValue_one matrixA_mul_self matrixB_pow_four)
      rw [h1, hseed]
      exact (maskValue_zero matrixA_mul_self matrixB_pow_four).symm
    have hbad := maskEquiv.injective hzero
    norm_num at hbad
  · exact MulEquiv.ext (fun e => DFunLike.congr_fun h e)
end Janko4.Max1RelativeRigidity
