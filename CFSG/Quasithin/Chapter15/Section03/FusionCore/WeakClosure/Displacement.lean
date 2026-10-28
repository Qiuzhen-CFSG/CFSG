module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.Setup

/-!
# Nonsingular displacement of an isometry fixing a nonsingular vector

In a nondegenerate quadratic four-space, an isometry with totally singular
image of `f - 1` that fixes a nonsingular vector is the identity. The image has
dimension at most two. Dimension two makes it equal to its orthogonal
complement, which cannot contain that fixed vector. A one-dimensional image
is ruled out by polarization and nondegeneracy.

Transporting this argument to conjugation on the actual subgroup `V` proves
the nonsingularity assertion used in 15.3.47. In particular it does not assume
that a nontrivial commutator is nonsingular.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1141.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore

open Module LinearMap Submodule
open CFSG.Quasithin

private theorem isometry_eq_id_of_singular_displacements {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (Q : QuadraticForm K E)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : finrank K E = 4)
    (f : E →ₗ[K] E) (hf : ∀ u, Q (f u) = Q u)
    (hs : ∀ u, Q (f u - u) = 0)
    (v : E) (hv : Q v ≠ 0) (hfix : f v = v) : f = LinearMap.id := by
  let N := f - LinearMap.id
  let R := LinearMap.range N
  let B : LinearMap.BilinForm K E := Q.polarBilin
  have hsing : ∀ u ∈ R, Q u = 0 := by
    rintro u ⟨w, rfl⟩
    exact hs w
  have hdiag (u : E) : B u (N u) = 0 := by
    change Q.polarBilin u (f u - u) = 0
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      show u + (f u - u) = f u by abel, hf, hs]
    ring
  have hcross (u w : E) : B u (N w) + B w (N u) = 0 := by
    have h := hdiag (u + w)
    simp only [map_add, LinearMap.add_apply] at h
    rw [hdiag u, hdiag w] at h
    simpa [add_comm] using h
  have horth : R ≤ B.orthogonal R := by
    intro u hu
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    apply QuadraticMap.isOrtho_polarBilin.mpr
    change Q (w + u) = Q w + Q u
    rw [hsing _ (R.add_mem hw hu), hsing _ hw, hsing _ hu, add_zero]
  have hfixed : v ∈ B.orthogonal R := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    rintro w ⟨u, rfl⟩
    have h := hcross u v
    have hNv : N v = 0 := by simp [N, hfix]
    rw [hNv, map_zero, zero_add] at h
    rw [show B (N u) v = B v (N u) from QuadraticMap.polar_comm Q _ _]
    exact h
  have hrle := Chapter12.Section01.twice_finrank_le_of_totally_singular Q hQ R hsing
  rw [hdim] at hrle
  have hrne2 : finrank K R ≠ 2 := by
    intro hr
    have heq : R = B.orthogonal R :=
      Submodule.eq_of_le_of_finrank_eq horth (by rw [B.finrank_orthogonal hQ, hdim, hr])
    exact hv (hsing v (heq.symm ▸ hfixed))
  have hrle1 : finrank K R ≤ 1 := by omega
  by_contra hne
  have hN : N ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨u, hu⟩ : ∃ u, N u ≠ 0 := by
    by_contra! h
    exact hN (LinearMap.ext h)
  have hrne0 : finrank K R ≠ 0 := by
    intro hr
    have he := Submodule.finrank_eq_zero.mp hr
    have hum : N u ∈ R := ⟨u, rfl⟩
    rw [he] at hum
    exact hu hum
  have hrone : finrank K R = 1 := by omega
  have hNu : (⟨N u, ⟨u, rfl⟩⟩ : R) ≠ 0 := fun h => hu (congrArg Subtype.val h)
  have hall (w : E) : B w (N u) = 0 := by
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hrone hNu (⟨N w, ⟨w, rfl⟩⟩ : R)
    have hcw : c • N u = N w := congrArg Subtype.val hc
    have h := hcross u w
    rw [← hcw, map_smul, hdiag, smul_zero, zero_add] at h
    exact h
  exact hu (hQ.2 _ hall)

open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G} [IsElementaryAbelian 2 V]
/-- A nontrivial commutator with an isometry fixing a nonsingular vector
cannot be totally singular. -/
theorem NaturalOrthogonalAction.not_totallySingular_commutator_of_fixed_nonsingular
    (d : NaturalOrthogonalAction M V) (x : M)
    (v : V) (hv : d.form (Additive.ofMul v) ≠ 0)
    (hfix : MulAut.conj (x : G) (v : G) = v)
    (hne : ⁅V, zpowers (x : G)⁆ ≠ ⊥) :
    ¬ IsTotallySingular d.form ⁅V, zpowers (x : G)⁆ := by
  intro hsing
  let e : MulAut V := V.normalizerMonoidHom ⟨x, d.normalizes x.property⟩
  let f : Additive V →ₗ[ZMod 2] Additive V :=
    e.toMonoidHom.toAdditive.toZModLinearMap 2
  have hf (u : Additive V) : d.form (f u) = d.form u := d.preserves x u.toMul
  have hs (u : Additive V) : d.form (f u - u) = 0 := by
    apply hsing.2 (f u - u).toMul
    change ((e u.toMul) / u.toMul : V).val ∈ ⁅V, zpowers (x : G)⁆
    simp only [div_eq_mul_inv]
    change (x : G) * (u.toMul : G) * (x : G)⁻¹ * (u.toMul : G)⁻¹ ∈ ⁅V, zpowers (x : G)⁆
    rw [commutator_comm V]
    exact commutator_mem_commutator (mem_zpowers _) u.toMul.property
  have hfv : f (Additive.ofMul v) = Additive.ofMul v := by
    apply Additive.toMul.injective
    exact Subtype.ext hfix
  have hid := isometry_eq_id_of_singular_displacements d.form d.nondegenerate
    d.dimension f hf hs (Additive.ofMul v) hv hfv
  apply hne
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mp
  apply zpowers_le.mpr
  intro u hu
  have h := congrArg (fun l : Additive V →ₗ[ZMod 2] Additive V =>
    ((l (Additive.ofMul (⟨u, hu⟩ : V))).toMul : G)) hid
  change (x : G) * u * (x : G)⁻¹ = u at h
  have hcomm : (x : G) * u = u * (x : G) := by
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using congrArg (· * (x : G)) h
  exact hcomm.symm
end CFSG.Quasithin.Chapter15.Section03.FusionCore
