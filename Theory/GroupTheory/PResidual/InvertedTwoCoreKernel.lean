module
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PPerfectHom
public import Theory.PGroupCore

/-!
# Killing the inverter kills the two-residual

Let a invert O²(H) modulo O₂(H). If a homomorphism kills a, the square of
each residual image comes from the two-core. Thus the residual image is a
two-group. Since the finite two-residual is two-perfect, that image is trivial.

The application is conjugation on C_G(U) in the c₂ branch of
Aschbacher–Smith, 14.4.5, printed pp.1007–1008. This argument retains the
actual two-core quotient and does not assume the kernel is U.
-/

@[expose] public section
open Subgroup
namespace Subgroup
variable {H D : Type*} [Group H] [Finite H] [Group D]

/-- Killing an inverter modulo the two-core kills the two-residual. -/
theorem pResidual_le_ker_of_inverts_mod_twoCore
    (f : H →* D) (a : H) (ha : f a = 1)
    (hinv : ∀ k : pResidual 2 H,
      QuotientGroup.mk' (pCore 2 H) (a * k * a⁻¹) =
        (QuotientGroup.mk' (pCore 2 H) k)⁻¹) :
    pResidual 2 H ≤ f.ker := by
  let r := f.comp (pResidual 2 H).subtype
  have hp : IsPGroup 2 r.range := by
    rintro ⟨x, k, rfl⟩
    let q : H := a * k * a⁻¹ * k
    have hq : q ∈ pCore 2 H := by
      apply (QuotientGroup.eq_one_iff q).mp
      change QuotientGroup.mk' (pCore 2 H) q = 1
      rw [show q = (a * k * a⁻¹) * k from rfl, map_mul, hinv k, inv_mul_cancel]
    obtain ⟨n, hn⟩ := pCore_isPGroup.exists_pow_pow_eq_one (⟨q,hq⟩ : pCore 2 H)
    have he : f q = (r k) ^ 2 := by
      simp only [q, r, MonoidHom.comp_apply, map_mul, map_inv, ha, one_mul,
        inv_one, mul_one, pow_two]
      rfl
    have hh : ((r k) ^ 2) ^ (2 ^ n) = 1 := by
      rw [← he, ← map_pow, show q ^ (2 ^ n) = 1 from congrArg Subtype.val hn, map_one]
    refine ⟨n + 1, Subtype.ext ?_⟩
    change (r k) ^ (2 ^ (n + 1)) = 1
    rw [pow_succ, Nat.mul_comm, pow_mul]
    exact hh
  have he := (isPPerfect_pResidual (G := H) 2).hom_eq_one_of_isPGroup hp r.rangeRestrict
  intro k hk
  have hh := congrArg Subtype.val (DFunLike.congr_fun he (⟨k,hk⟩ : pResidual 2 H))
  exact hh
end Subgroup
