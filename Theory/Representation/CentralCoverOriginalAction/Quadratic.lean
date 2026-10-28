module

public import Theory.Representation.CentralCoverOriginalAction
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Singular complements under the original actor

The additive scalar commutant of the natural L-module forces each binary
normalizer to be field-semilinear. The polar form changes by a scalar;
the difference of quadratic forms is additive and L-invariant, hence vanishes
on a commutator-generated cover. Thus the singular complement over every
totally isotropic subspace is preserved by its original ambient stabilizer.

No classification of normalizers or pointwise fixation of the universal
L-kernel is required. Source: Aschbacher--Smith I.2.3, printed p.413.
-/

@[expose] public section
noncomputable section

namespace Representation.OneCohomology.CentralCoverOriginalAction

open Module

variable {F L N U : Type*} [Field F] [Finite F] [CharP F 2]
  [Algebra (ZMod 2) F] [Group L]
  [AddCommGroup N] [Module F N] [Module (ZMod 2) N] [IsScalarTower (ZMod 2) F N]
  [AddCommGroup U] [Module F U] [Module (ZMod 2) U] [IsScalarTower (ZMod 2) F U]

/-- The exact local input, furnished by the natural matrix commutant. -/
def HasScalarCommutant (ρ : Representation F L N) : Prop :=
  ∀ f : N →+ N, (∀ l v, f (ρ l v) = ρ l (f v)) →
    ∃ c : F, ∀ v, f v = c • v

omit [CharP F 2] [Algebra (ZMod 2) F] [IsScalarTower (ZMod 2) F N] in
/-- A binary normalizer of a scalar-commutant action is field-semilinear. -/
theorem normalizer_semilinear [Nontrivial N]
    (ρ : Representation F L N) (hscalar : HasScalarCommutant ρ)
    (a : MulAut L) (e : N ≃ₗ[ZMod 2] N)
    (he : ∀ l v, e (ρ l v) = ρ (a l) (e v)) :
    ∃ s : F ≃+* F, ∀ c v, e (c • v) = s c • e v := by
  let f (c : F) : N →+ N :=
    { toFun v := e (c • e.symm v)
      map_zero' := by simp
      map_add' v w := by simp [smul_add] }
  have hi (l : L) (v : N) : e.symm (ρ l v) = ρ (a.symm l) (e.symm v) := by
    apply e.injective
    rw [e.apply_symm_apply, he, a.apply_symm_apply, e.apply_symm_apply]
  have hf (c : F) : ∃ d : F, ∀ v, f c v = d • v := by
    apply hscalar
    intro l v
    change e (c • e.symm (ρ l v)) = ρ l (e (c • e.symm v))
    rw [hi, ← map_smul, he, a.apply_symm_apply]
  choose s hs using hf
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : N)
  have hinj : Function.Injective (fun c : F => c • v₀) := smul_left_injective F hv₀
  have hmul (c d : F) (v : N) : f (c * d) v = f c (f d v) := by
    simp [f, mul_smul]
  let s₀ : F →+* F :=
    { toFun := s
      map_one' := by
        apply hinj
        change s 1 • v₀ = (1 : F) • v₀
        rw [← hs]
        simp [f]
      map_mul' c d := by
        apply hinj
        change s (c * d) • v₀ = (s c * s d) • v₀
        rw [← hs, hmul, hs, hs, mul_smul]
      map_zero' := by
        apply hinj
        change s 0 • v₀ = (0 : F) • v₀
        rw [← hs]
        simp [f]
      map_add' c d := by
        apply hinj
        change s (c + d) • v₀ = (s c + s d) • v₀
        rw [← hs, add_smul]
        change e ((c + d) • e.symm v₀) = _
        rw [add_smul, map_add]
        exact congrArg₂ (· + ·) (hs c v₀) (hs d v₀) }
  refine ⟨RingEquiv.ofBijective s₀
    ⟨s₀.injective, Finite.surjective_of_injective s₀.injective⟩, fun c v => ?_⟩
  change e (c • v) = s c • e v
  simpa only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    LinearEquiv.symm_apply_apply] using hs c (e v)

omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F] [IsScalarTower (ZMod 2) F N] in
/-- A semilinear normalizer preserves the nondegenerate invariant polar form
up to its field automorphism and a nonzero scalar. -/
theorem polar_similitude [Nontrivial N] [FiniteDimensional F N]
    (ρ : Representation F L N) (hscalar : HasScalarCommutant ρ)
    (B : LinearMap.BilinForm F N) (hB : B.Nondegenerate)
    (hBinv : ∀ l v w, B (ρ l v) (ρ l w) = B v w)
    (a : MulAut L) (e : N ≃ₗ[ZMod 2] N)
    (he : ∀ l v, e (ρ l v) = ρ (a l) (e v))
    (s : F ≃+* F) (hs : ∀ c v, e (c • v) = s c • e v) :
    ∃ c : F, c ≠ 0 ∧ ∀ v w, s.symm (B (e v) (e w)) = c * B v w := by
  let D : LinearMap.BilinForm F N :=
    { toFun v :=
        { toFun w := s.symm (B (e v) (e w))
          map_add' w x := by simp
          map_smul' c w := by simp [hs, smul_eq_mul] }
      map_add' v w := by ext x; simp
      map_smul' c v := by ext w; simp [hs, smul_eq_mul] }
  let T : Module.End F N := (B.toDual hB).symm.toLinearMap.comp D
  have hT (v w : N) : B (T v) w = D v w :=
    LinearMap.BilinForm.apply_toDual_symm_apply (hB := hB) (D v) w
  have hD (l : L) (v w : N) : D (ρ l v) (ρ l w) = D v w := by
    change s.symm (B (e (ρ l v)) (e (ρ l w))) = _
    rw [he, he, hBinv]
    rfl
  obtain ⟨c, hc⟩ := hscalar T.toAddMonoidHom (by
    intro l v
    apply (B.toDual hB).injective
    apply LinearMap.ext
    intro w
    obtain ⟨w, rfl⟩ := (actorEquiv ρ l).surjective w
    change B (T (ρ l v)) (ρ l w) = B (ρ l (T v)) (ρ l w)
    rw [hT, hD, ← hT, hBinv])
  have hform (v w : N) : s.symm (B (e v) (e w)) = c * B v w := by
    change D v w = _
    have hc' : T v = c • v := hc v
    rw [← hT, hc', map_smul]
    rfl
  refine ⟨c, ?_, hform⟩
  intro hc0
  obtain ⟨v, hv⟩ := exists_ne (0 : N)
  apply hv
  apply hB.1 v
  intro w
  have h := hform (e.symm v) (e.symm w)
  rw [e.apply_symm_apply, e.apply_symm_apply, hc0, zero_mul] at h
  exact s.symm.injective (h.trans (map_zero _).symm)

omit [CharP F 2] in
/-- A zero-polar invariant difference vanishes on the generated cover.
Consequently the original lift preserves precisely the singular vectors. -/
theorem lift_preserves_singular [Nontrivial N] [FiniteDimensional F N]
    (ρ : Representation F L N) (σ : Representation F L U)
    (p : σ.IntertwiningMap ρ)
    (hp : IsCover (restrictCoverMap (k := ZMod 2) p))
    (hscalar : HasScalarCommutant ρ)
    (B : LinearMap.BilinForm F N) (hB : B.Nondegenerate)
    (hBinv : ∀ l v w, B (ρ l v) (ρ l w) = B v w)
    (Q : QuadraticForm F U) (hQ : ∀ l u, Q (σ l u) = Q u)
    (hpolar : ∀ u v, Q.polarBilin u v = B (p u) (p v))
    (a : MulAut L) (e : N ≃ₗ[ZMod 2] N) (E : U ≃ₗ[ZMod 2] U)
    (he : ∀ l v, e (ρ l v) = ρ (a l) (e v))
    (hE : ∀ l u, E (σ l u) = σ (a l) (E u))
    (hover : ∀ u, p (E u) = e (p u)) :
    ∀ u, Q (E u) = 0 ↔ Q u = 0 := by
  obtain ⟨s, hs⟩ := normalizer_semilinear ρ hscalar a e he
  obtain ⟨c, hc, hform⟩ := polar_similitude ρ hscalar B hB hBinv a e he s hs
  let d : U →+ F :=
    { toFun u := s.symm (Q (E u)) - c * Q u
      map_zero' := by simp
      map_add' u v := by
        have heq := hform (p u) (p v)
        rw [← hover, ← hover, ← hpolar, ← hpolar] at heq
        change s.symm (Q (E (u + v))) - c * Q (u + v) = _
        rw [map_add]
        simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar] at heq
        simp only [map_sub] at heq
        linear_combination heq }
  have hd : d.toZModLinearMap 2 = 0 := by
    apply invariant_map_eq_zero (restrictScalars (k := ZMod 2) σ) hp.2.2
    intro l u
    change s.symm (Q (E (σ l u))) - c * Q (σ l u) = _
    rw [hE, hQ, hQ]
    rfl
  intro u
  have h : s.symm (Q (E u)) = c * Q u :=
    sub_eq_zero.mp (LinearMap.congr_fun hd u)
  constructor
  · intro hu
    rw [hu, map_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hc
  · intro hu
    apply s.symm.injective
    rw [h, hu, mul_zero, map_zero]

/-- Singular vectors over an isotropic base subspace form a field submodule. -/
def singularPreimage (p : U →ₗ[F] N) (Q : QuadraticForm F U)
    (A : Submodule F N)
    (hpolar : ∀ u v, p u ∈ A → p v ∈ A → Q.polarBilin u v = 0) :
    Submodule F U where
  carrier := {u | p u ∈ A ∧ Q u = 0}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv
    refine ⟨by simpa using A.add_mem hu.1 hv.1, ?_⟩
    have h := hpolar u v hu.1 hv.1
    simpa [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hu.2, hv.2] using h
  smul_mem' := by
    intro c u hu
    refine ⟨by simpa using A.smul_mem c hu.1, ?_⟩
    simp [Q.map_smul, hu.2]

omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [Module (ZMod 2) N] [IsScalarTower (ZMod 2) F N]
  [Module (ZMod 2) U] [IsScalarTower (ZMod 2) F U] in
/-- An anisotropic central line has zero intersection with the singular section. -/
theorem singularPreimage_injective
    (p : U →ₗ[F] N) (Q : QuadraticForm F U) (A : Submodule F N)
    (hpolar : ∀ u v, p u ∈ A → p v ∈ A → Q.polarBilin u v = 0)
    (haniso : ∀ u, p u = 0 → Q u = 0 → u = 0) :
    Function.Injective (fun u : singularPreimage p Q A hpolar => p u) := by
  intro u v huv
  change p u = p v at huv
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply haniso (u.val - v.val)
  · rw [map_sub, huv, sub_self]
  · exact ((singularPreimage p Q A hpolar).sub_mem u.property v.property).2

omit [Algebra (ZMod 2) F] [Module (ZMod 2) N] [IsScalarTower (ZMod 2) F N]
  [Module (ZMod 2) U] [IsScalarTower (ZMod 2) F U] in
/-- Every vector above an isotropic base subspace has a singular representative.
The hypotheses describe the actual nonsingular radical line, not a splitting. -/
theorem singularPreimage_surjective
    (p : U →ₗ[F] N) (hp : Function.Surjective p)
    (Q : QuadraticForm F U) (A : Submodule F N)
    (hpolar : ∀ u v, p u ∈ A → p v ∈ A → Q.polarBilin u v = 0)
    (r : U) (hr : p r = 0) (hQr : Q r ≠ 0) :
    ∀ v : A, ∃ u : singularPreimage p Q A hpolar, p u = v := by
  intro v
  obtain ⟨u, hu⟩ := hp v
  obtain ⟨c, hc⟩ := Finite.surjective_of_injective (CharTwo.sq_injective (R := F))
    (Q u / Q r)
  change c ^ 2 = Q u / Q r at hc
  have hpc : p (c • r) = 0 := by rw [map_smul, hr, smul_zero]
  have hpu : p u ∈ A := hu ▸ v.property
  have hQcr : Q (c • r) = Q u := by
    rw [Q.map_smul]
    calc
      _ = c ^ 2 * Q r := by simp [smul_eq_mul, pow_two, mul_assoc]
      _ = Q u := by rw [hc, div_mul_cancel₀ _ hQr]
  have hq : Q (u + c • r) = 0 := by
    have hb := hpolar u (c • r) hpu (hpc ▸ A.zero_mem)
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hQcr] at hb
    have hh : Q u + Q u = 0 := CharTwo.add_self_eq_zero _
    linear_combination hb + hh
  refine ⟨⟨u + c • r, ?_, hq⟩, ?_⟩
  · rw [map_add, hpc, add_zero, hu]
    exact v.property
  · simp [map_add, hpc, hu]

omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [IsScalarTower (ZMod 2) F N] [IsScalarTower (ZMod 2) F U] in
/-- The original stabilizer preserves the unique singular complement. -/
theorem singularPreimage_stable
    (p : U →ₗ[F] N) (Q : QuadraticForm F U) (A : Submodule F N)
    (hpolar : ∀ u v, p u ∈ A → p v ∈ A → Q.polarBilin u v = 0)
    (e : N ≃ₗ[ZMod 2] N) (E : U ≃ₗ[ZMod 2] U)
    (hover : ∀ u, p (E u) = e (p u))
    (hA : ∀ v ∈ A, e v ∈ A)
    (hQ : ∀ u, Q (E u) = 0 ↔ Q u = 0) :
    ∀ u ∈ singularPreimage p Q A hpolar,
      E u ∈ singularPreimage p Q A hpolar := by
  intro u hu
  exact ⟨by rw [hover]; exact hA (p u) hu.1, (hQ u).mpr hu.2⟩

omit [CharP F 2] in
/-- Construct the lifted original action and prove its singular-set preservation
from the genuine universal L-cover and its polar geometry. -/
theorem exists_original_action_preserving_singular
    {G : Type*} [Group G] [Finite G] [Nontrivial N]
    [FiniteDimensional F N] [FiniteDimensional (ZMod 2) N]
    [FiniteDimensional (ZMod 2) U]
    (H : Subgroup G) [H.Normal]
    (η : Representation (ZMod 2) G N)
    (ρ : Representation F H N) (σ : Representation F H U)
    (hρ : ∀ h : H, ∀ v, η h v = ρ h v)
    (p : σ.IntertwiningMap ρ)
    (hp : IsCover (restrictCoverMap (k := ZMod 2) p))
    (hd : finrank (ZMod 2) (p.toLinearMap.restrictScalars (ZMod 2)).ker =
      finrank (ZMod 2) (H1 (restrictScalars (k := ZMod 2) ρ).dual))
    (hscalar : HasScalarCommutant ρ)
    (B : LinearMap.BilinForm F N) (hB : B.Nondegenerate)
    (hBinv : ∀ h v w, B (ρ h v) (ρ h w) = B v w)
    (Q : QuadraticForm F U) (hQ : ∀ h u, Q (σ h u) = Q u)
    (hpolar : ∀ u v, Q.polarBilin u v = B (p u) (p v)) :
    ∃ ζ : Representation (ZMod 2) G U,
      (∀ h : H, ∀ u, ζ h u = σ h u) ∧
      (∀ g u, p (ζ g u) = η g (p u)) ∧
      (∀ g u, Q (ζ g u) = 0 ↔ Q u = 0) := by
  have hρeq : η.comp H.subtype = restrictScalars (k := ZMod 2) ρ := by
    apply MonoidHom.ext
    intro h
    exact LinearMap.ext (hρ h)
  let p' : Representation.IntertwiningMap (restrictScalars (k := ZMod 2) σ)
      (η.comp H.subtype) :=
    (p.toLinearMap.restrictScalars (ZMod 2)).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro h u
      change p (σ h u) = η h (p u)
      rw [p.isIntertwining, hρ])
  have hd' : finrank (ZMod 2) p'.toLinearMap.ker =
      finrank (ZMod 2) (H1 (Representation.dual (η.comp H.subtype))) := by
    change finrank (ZMod 2) (p.toLinearMap.restrictScalars (ZMod 2)).ker = _
    exact hd.trans (congrArg (fun δ : Representation (ZMod 2) H N =>
      finrank (ZMod 2) (H1 δ.dual)) hρeq).symm
  obtain ⟨ζ, hζ, hquot⟩ := exists_original_action H η p' hp hd'
  change ∀ h : H, ∀ u, ζ h u = σ h u at hζ
  change ∀ g u, p (ζ g u) = η g (p u) at hquot
  refine ⟨ζ, hζ, hquot, fun g => ?_⟩
  let a := normalConjugation H g
  have he (h : H) (v : N) : η g (ρ h v) = ρ (a h) (η g v) := by
    rw [← hρ, ← hρ]
    change η g (η h v) = η (g * h * g⁻¹) (η g v)
    simp [← Module.End.mul_apply, ← map_mul, mul_assoc]
  have hE (h : H) (u : U) : ζ g (σ h u) = σ (a h) (ζ g u) := by
    rw [← hζ, ← hζ]
    change ζ g (ζ h u) = ζ (g * h * g⁻¹) (ζ g u)
    simp [← Module.End.mul_apply, ← map_mul, mul_assoc]
  exact lift_preserves_singular ρ σ p hp hscalar B hB hBinv Q hQ hpolar a
    (actorEquiv η g) (actorEquiv ζ g) he hE (hquot g)

end Representation.OneCohomology.CentralCoverOriginalAction
