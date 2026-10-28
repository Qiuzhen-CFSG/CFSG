module
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Paired outer-action kernels

Suppose a normal subgroup is a commuting product of two factor images, and
its ambient quotient is a p-group. Two actions on centerless quotient groups,
inner on their own factors and trivial on the opposite factors, have a joint
p-group kernel. Raising an element into the normal subgroup reduces this to
the p-group kernels of the two factor quotients.

If the ambient p-core lies in the normal subgroup, an element inducing two
inner actions lies there too: lift and cancel those inner actions using the
two commuting factors.

Source application: the paired linear-block outer coordinates in
Aschbacher–Smith, Chapter 2, Section 4, printed p.540.
-/

public section
namespace Theory.GroupTheory
open Subgroup
variable {B L₁ L₂ K₁ K₂ : Type*}
  [Group B] [Group L₁] [Group L₂] [Group K₁] [Group K₂] {p : ℕ}

/-- Two complementary centerless quotient actions have a joint p-group kernel. -/
theorem paired_action_kernel_isPGroup
    (N : Subgroup B) [N.Normal] (hq : IsPGroup p (B ⧸ N))
    (a₁ : L₁ →* B) (a₂ : L₂ →* B)
    (hdecomp : ∀ n : N, ∃ l₁ l₂, (n : B) = a₁ l₁ * a₂ l₂)
    (hcomm : ∀ l₁ l₂, Commute (a₁ l₁) (a₂ l₂))
    (q₁ : L₁ →* K₁) (q₂ : L₂ →* K₂)
    (hk₁ : IsPGroup p q₁.ker) (hk₂ : IsPGroup p q₂.ker)
    (hc₁ : center K₁ = ⊥) (hc₂ : center K₂ = ⊥)
    (ρ₁ : B →* MulAut K₁) (ρ₂ : B →* MulAut K₂)
    (hi₁ : ∀ l, ρ₁ (a₁ l) = MulAut.conj (q₁ l))
    (hi₂ : ∀ l, ρ₂ (a₂ l) = MulAut.conj (q₂ l))
    (hx₁ : ∀ l, ρ₁ (a₂ l) = 1) (hx₂ : ∀ l, ρ₂ (a₁ l) = 1) :
    IsPGroup p (ρ₁.prod ρ₂).ker := by
  intro k
  obtain ⟨m, hm⟩ := hq (QuotientGroup.mk' N (k : B))
  have hkm : (k : B) ^ (p ^ m) ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' N ((k : B) ^ (p ^ m)) = 1
    simpa only [map_pow] using hm
  obtain ⟨l₁, l₂, he⟩ := hdecomp ⟨(k : B) ^ (p ^ m), hkm⟩
  change (k : B) ^ (p ^ m) = a₁ l₁ * a₂ l₂ at he
  have hρ₁ : ρ₁ (k : B) = 1 := congrArg Prod.fst k.property
  have hρ₂ : ρ₂ (k : B) = 1 := congrArg Prod.snd k.property
  have hl₁ : q₁ l₁ = 1 := by
    apply conj_injective_of_center_eq_bot hc₁
    rw [← hi₁, map_one]
    have hh := congrArg ρ₁ he
    simp only [map_pow, hρ₁, one_pow, map_mul, hx₁, mul_one] at hh
    exact hh.symm
  have hl₂ : q₂ l₂ = 1 := by
    apply conj_injective_of_center_eq_bot hc₂
    rw [← hi₂, map_one]
    have hh := congrArg ρ₂ he
    simp only [map_pow, hρ₂, one_pow, map_mul, hx₂, one_mul] at hh
    exact hh.symm
  obtain ⟨r, hr⟩ := hk₁ ⟨l₁, hl₁⟩
  obtain ⟨s, hs⟩ := hk₂ ⟨l₂, hl₂⟩
  have hr' : a₁ l₁ ^ (p ^ r) = 1 := by
    have hh := congrArg (fun z : q₁.ker => a₁ (z : L₁)) hr
    change a₁ (l₁ ^ (p ^ r)) = a₁ 1 at hh
    simpa only [map_pow, map_one] using hh
  have hs' : a₂ l₂ ^ (p ^ s) = 1 := by
    have hh := congrArg (fun z : q₂.ker => a₂ (z : L₂)) hs
    change a₂ (l₂ ^ (p ^ s)) = a₂ 1 at hh
    simpa only [map_pow, map_one] using hh
  have hr'' : a₁ l₁ ^ (p ^ (r + s)) = 1 := by
    rw [pow_add, pow_mul, hr', one_pow]
  have hs'' : a₂ l₂ ^ (p ^ (r + s)) = 1 := by
    rw [Nat.add_comm r s, pow_add, pow_mul, hs', one_pow]
  refine ⟨m + (r + s), ?_⟩
  apply Subtype.ext
  change (k : B) ^ (p ^ (m + (r + s))) = 1
  rw [pow_add, pow_mul, he, (hcomm l₁ l₂).mul_pow, hr'', hs'', one_mul]

/-- Absorbing the p-core also absorbs elements inner in both quotient actions. -/
theorem mem_of_paired_inner_actions
    (N : Subgroup B) [N.Normal] (hq : IsPGroup p (B ⧸ N))
    (a₁ : L₁ →* B) (a₂ : L₂ →* B)
    (hdecomp : ∀ n : N, ∃ l₁ l₂, (n : B) = a₁ l₁ * a₂ l₂)
    (hcomm : ∀ l₁ l₂, Commute (a₁ l₁) (a₂ l₂))
    (q₁ : L₁ →* K₁) (q₂ : L₂ →* K₂)
    (hk₁ : IsPGroup p q₁.ker) (hk₂ : IsPGroup p q₂.ker)
    (hc₁ : center K₁ = ⊥) (hc₂ : center K₂ = ⊥)
    (ρ₁ : B →* MulAut K₁) (ρ₂ : B →* MulAut K₂)
    (hi₁ : ∀ l, ρ₁ (a₁ l) = MulAut.conj (q₁ l))
    (hi₂ : ∀ l, ρ₂ (a₂ l) = MulAut.conj (q₂ l))
    (hx₁ : ∀ l, ρ₁ (a₂ l) = 1) (hx₂ : ∀ l, ρ₂ (a₁ l) = 1)
    (ha₁ : ∀ l, a₁ l ∈ N) (ha₂ : ∀ l, a₂ l ∈ N)
    (hs₁ : Function.Surjective q₁) (hs₂ : Function.Surjective q₂)
    (hcore : pCore p B ≤ N) (b : B)
    (hb₁ : ρ₁ b ∈ MulAut.innerSubgroup K₁)
    (hb₂ : ρ₂ b ∈ MulAut.innerSubgroup K₂) : b ∈ N := by
  have hkernel := paired_action_kernel_isPGroup N hq a₁ a₂ hdecomp hcomm
    q₁ q₂ hk₁ hk₂ hc₁ hc₂ ρ₁ ρ₂ hi₁ hi₂ hx₁ hx₂
  have hkerle : (ρ₁.prod ρ₂).ker ≤ N :=
    (show (ρ₁.prod ρ₂).ker ≤ pCore p B from le_sSup ⟨inferInstance, hkernel⟩).trans hcore
  obtain ⟨y₁, hy₁⟩ := hb₁
  obtain ⟨y₂, hy₂⟩ := hb₂
  obtain ⟨l₁, rfl⟩ := hs₁ y₁
  obtain ⟨l₂, rfl⟩ := hs₂ y₂
  let c := a₁ l₁ * a₂ l₂
  have hc : c ∈ N := N.mul_mem (ha₁ l₁) (ha₂ l₂)
  have he₁ : ρ₁ c = ρ₁ b := by
    dsimp [c]
    rw [map_mul, hi₁, hx₁, mul_one]
    exact hy₁
  have he₂ : ρ₂ c = ρ₂ b := by
    dsimp [c]
    rw [map_mul, hx₂, hi₂, one_mul]
    exact hy₂
  have hd : c⁻¹ * b ∈ (ρ₁.prod ρ₂).ker := by
    change (ρ₁ (c⁻¹ * b), ρ₂ (c⁻¹ * b)) = (1, 1)
    simp only [map_mul, map_inv, he₁, he₂, inv_mul_cancel]
  have hh := N.mul_mem hc (hkerle hd)
  simpa only [mul_inv_cancel_left] using hh
end Theory.GroupTheory
