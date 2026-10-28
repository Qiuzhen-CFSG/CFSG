module
public import Theory.Representation.SubspaceQuotient
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Theory.Representation.BinaryConjugationSection.InvariantPreimage
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# Cubics fixing a dual-free simple half-space

An invariant pairing vanishes on a simple submodule with no map to its dual.
If that submodule has half the ambient dimension, it equals its orthogonal
complement. Any isometry fixing it pointwise then has square one in
characteristic two. A cubic isometry fixing it must therefore be the identity.

The conjugation-section adapter retains an arbitrary original fixed kernel.
Orbit generation supplies an injective intertwiner from the simple generator;
no splitting of the containing central section is assumed.
Source application: Aschbacher--Smith 10.2.9, printed p.752, the binary-four
orthogonal containing action and its opposite cubic.
-/

public noncomputable section
open Representation
namespace Representation
variable {H A W X : Type*} [Group H] [Group A]
  [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
  {ρ : Representation (ZMod 2) H W}
  (σ : Representation (ZMod 2) A X) (q : H →* A)
  (f : ρ.IntertwiningMap (σ.comp q))

/-- A cubic isometry fixing a dual-free simple half-space is trivial. -/
theorem cubic_eq_one_of_half_dual_free
    (hzero : ∀ b : ρ.IntertwiningMap ρ.dual, b = 0)
    (hfi : Function.Injective f)
    (hd : Module.finrank (ZMod 2) X = 2 * Module.finrank (ZMod 2) W)
    (B : LinearMap.BilinForm (ZMod 2) X) (hB : B.Nondegenerate)
    (hinv : ∀ a x y, B (σ a x) (σ a y) = B x y)
    (a : A) (ha : a ^ 3 = 1) (hfix : ∀ w, σ a (f w) = f w) : σ a = 1 := by
  have hfe (h : H) (w : W) : f (ρ h w) = σ (q h) (f w) :=
    LinearMap.congr_fun (f.isIntertwining' h) w
  let b : ρ.IntertwiningMap ρ.dual := {
    toLinearMap := LinearMap.comp f.toLinearMap.dualMap (LinearMap.comp B f.toLinearMap)
    isIntertwining' := by
      intro h
      apply LinearMap.ext
      intro u
      apply LinearMap.ext
      intro v
      change B (f (ρ h u)) (f v) = B (f u) (f (ρ h⁻¹ v))
      calc
        _ = B (σ (q h) (f u)) (σ (q h) (f (ρ h⁻¹ v))) := by
          rw [←hfe,←hfe,Representation.self_inv_apply]
        _ = _ := hinv _ _ _ }
  have hz (u v : W) : B (f u) (f v) = 0 :=
    congrArg (fun c : ρ.IntertwiningMap ρ.dual => c u v) (hzero b)
  let P := LinearMap.range f.toLinearMap
  have hP : P ≤ B.orthogonal P := by
    rintro _ ⟨u,rfl⟩ _ ⟨v,rfl⟩
    exact hz v u
  have hpdim : Module.finrank (ZMod 2) P = Module.finrank (ZMod 2) W :=
    (LinearEquiv.ofInjective f.toLinearMap hfi).finrank_eq.symm
  have he : P = B.orthogonal P := Submodule.eq_of_le_of_finrank_eq hP (by
    rw [LinearMap.BilinForm.finrank_orthogonal hB,hpdim,hd]
    omega)
  have hdisp (x : X) : σ a x - x ∈ P := by
    rw [he]
    rintro _ ⟨w,rfl⟩
    change B (f w) (σ a x - x) = 0
    rw [map_sub]
    apply sub_eq_zero.mpr
    calc
      _ = B (σ a (f w)) (σ a x) := by rw [hfix]
      _ = _ := hinv _ _ _
  have htwo : σ a ^ 2 = 1 := by
    apply LinearMap.ext
    intro x
    obtain ⟨w,hw⟩ := hdisp x
    have hh : σ a (σ a x - x) = σ a x - x := by rw [←hw]; exact hfix w
    rw [map_sub] at hh
    change σ a (σ a x) = x
    calc
      _ = (σ a (σ a x) - σ a x) + σ a x := (sub_add_cancel _ _).symm
      _ = (σ a x - x) + σ a x := congrArg (fun z => z + σ a x) hh
      _ = x := by
        have hsum (z : X) : z + z = 0 := by
          rw [←two_smul (ZMod 2),show (2 : ZMod 2) = 0 from rfl,zero_smul]
        have hneg : -x = x := neg_eq_iff_add_eq_zero.mpr (hsum x)
        rw [sub_eq_add_neg,hneg,add_right_comm,hsum,zero_add]
  have hthree : σ a ^ 3 = 1 := by rw [←map_pow,ha,map_one]
  simpa only [show 3 = 2+1 from rfl,pow_succ,htwo,one_mul] using hthree
end Representation

open scoped IsMulCommutative

open Subgroup
namespace Representation.BinaryConjugationSection
variable {G W X : Type*} [Group G]
  [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X] [Nontrivial X]
  {L H A R Z : Subgroup G} [IsElementaryAbelian 2 A]
  {ρ : Representation (ZMod 2) L W} [IsIrreducible ρ]
  (r : BinaryConjugationSection L A ⊥ ρ)
  (τ : Representation (ZMod 2) H X)
  (s : BinaryConjugationSection H R Z τ)

omit [FiniteDimensional (ZMod 2) X] in
include r s in
/-- Coordinates for a simple subgroup generate the actual orbit section. -/
theorem exists_simple_generator
    (hLH : L ≤ H) (hAR : A ≤ R) (hgen : R ≤ conjugateSpanBy A H) :
    ∃ f : ρ.IntertwiningMap (τ.comp (inclusion hLH)),
      Function.Injective f ∧
      ∀ w : A, f (r.coordinates w).toAdd = (s.coordinates (inclusion hAR w)).toAdd := by
  have hrinj : Function.Injective r.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [r.kernel_eq,bot_subgroupOf]
  let a : Additive A ≃ₗ[ZMod 2] W := LinearEquiv.ofBijective
    (r.coordinates.toAdditiveLeft.toZModLinearMap 2) ⟨hrinj,r.onto⟩
  let b : Additive A →ₗ[ZMod 2] X :=
    (s.coordinates.comp (inclusion hAR)).toAdditiveLeft.toZModLinearMap 2
  have ha (w : A) : a (Additive.ofMul w) = (r.coordinates w).toAdd := rfl
  have hb (w : A) : b (Additive.ofMul w) =
      (s.coordinates (inclusion hAR w)).toAdd := rfl
  let f : ρ.IntertwiningMap (τ.comp (inclusion hLH)) := {
    toLinearMap := b.comp a.symm.toLinearMap
    isIntertwining' := by
      intro l
      apply LinearMap.ext
      intro w
      obtain ⟨u,rfl⟩ := a.surjective w
      let z : A := ⟨(l:G)*u.toMul*(l:G)⁻¹,
        (mem_normalizer_iff.mp (r.normalized l.property) u.toMul).mp u.toMul.property⟩
      have he : ρ l (a u) = a (Additive.ofMul z) := (r.equivariant l u.toMul).symm
      change b (a.symm (ρ l (a u))) = τ (inclusion hLH l) (b (a.symm (a u)))
      rw [he,a.symm_apply_apply,a.symm_apply_apply]
      exact s.equivariant (inclusion hLH l) (inclusion hAR u.toMul) }
  have hgen' (P : Subrepresentation τ) (hP : ∀ w, f w ∈ P.toSubmodule) : P = ⊤ := by
    have hAP : A ≤ s.invariantPreimage P := by
      intro w hw
      apply (s.mem_invariantPreimage P w).mpr
      refine ⟨hAR hw,?_⟩
      have hh := hP (a (Additive.ofMul (⟨w,hw⟩ : A)))
      change b (a.symm (a (Additive.ofMul (⟨w,hw⟩ : A)))) ∈ P.toSubmodule at hh
      rwa [a.symm_apply_apply] at hh
    have hRP : R ≤ s.invariantPreimage P := hgen.trans
      (conjugateSpanBy_le hAP (s.invariantPreimage_normalized P))
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro z _
    obtain ⟨u,rfl⟩ := s.onto (Multiplicative.ofAdd z)
    exact ((s.mem_invariantPreimage P u).mp (hRP u.property)).choose_spec
  have hfn : f ≠ 0 := by
    intro hz
    have he := hgen' ⊥ (fun w => congrArg (fun g : ρ.IntertwiningMap (τ.comp (inclusion hLH)) => g w) hz)
    obtain ⟨x,hx⟩ := exists_ne (0 : X)
    have hm : x ∈ (⊥ : Subrepresentation τ).toSubmodule := he.symm ▸ Submodule.mem_top
    exact hx hm
  refine ⟨f,(IsIrreducible.injective_or_eq_zero f).resolve_right hfn,?_⟩
  intro w
  change b (a.symm (a (Additive.ofMul w))) = _
  rw [a.symm_apply_apply]
  rfl
include r s in
/-- A cubic fixing the original simple half-dimensional generator acts
trivially on a section carrying a nondegenerate invariant pairing. -/
theorem cubic_eq_one_of_centralizes_generator
    (hLH : L ≤ H) (hAR : A ≤ R) (hgen : R ≤ conjugateSpanBy A H)
    (hzero : ∀ b : ρ.IntertwiningMap ρ.dual, b = 0)
    (hd : Module.finrank (ZMod 2) X = 2 * Module.finrank (ZMod 2) W)
    (B : LinearMap.BilinForm (ZMod 2) X) (hB : B.Nondegenerate)
    (hinv : ∀ h x y, B (τ h x) (τ h y) = B x y)
    (y : H) (hy : y ^ 3 = 1) (hyC : (y : G) ∈ centralizer (A : Set G)) : τ y = 1 := by
  obtain ⟨f,hfi,hf⟩ := r.exists_simple_generator τ s hLH hAR hgen
  apply cubic_eq_one_of_half_dual_free τ (inclusion hLH) f hzero hfi hd B hB hinv y hy
  intro w
  obtain ⟨u,hu⟩ := r.onto (Multiplicative.ofAdd w)
  have hw : (r.coordinates u).toAdd = w := congrArg Multiplicative.toAdd hu
  rw [←hw,hf,←s.equivariant y (inclusion hAR u)]
  apply congrArg Multiplicative.toAdd
  apply congrArg s.coordinates
  apply Subtype.ext
  change (y:G) * (u:G) * (y:G)⁻¹ = (u:G)
  rw [←hyC u u.property,mul_inv_cancel_right]

end Representation.BinaryConjugationSection
