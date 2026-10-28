module
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.PGroupCore
public import Theory.GroupTheory.PGroup.NormalSupplementKernel
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
/-!
# Kernels of nontrivial actions of two-perfect cubic extensions

If A is two-perfect and A/O₂(A) has order three, a nontrivial
homomorphism on A has two-group kernel. The kernel image in the simple
cubic quotient is either trivial or surjective. Surjectivity would make
the whole action a two-group image, contradicting two-perfectness.

Source application: the literal L₁T action on V_I in Aschbacher–Smith,
proof of 14.7.32, printed p.1058. Normal supplementation extends the
kernel conclusion from L₁ to L₁T.
-/

public section
open Subgroup
namespace MonoidHom
variable {A B : Type*} [Group A] [Group B]
/-- A nontrivial action detects the entire odd part of a two-perfect cubic extension. -/
theorem kernel_isTwoGroup_of_twoPerfect_cubic (f : A →* B)
    (hp : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hne : f ≠ 1) : IsPGroup 2 f.ker := by
  let q := QuotientGroup.mk' (pCore 2 A)
  let : IsSimpleGroup (A ⧸ pCore 2 A) := isSimpleGroup_of_prime_card hc
  have hn : (f.ker.map q).Normal := f.normal_ker.map q (QuotientGroup.mk'_surjective _)
  rcases hn.eq_bot_or_eq_top with hz | ht
  · have hk : f.ker ≤ pCore 2 A := by
      simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz
    exact pCore_isPGroup.to_le hk
  · have hs : f.ker ⊔ pCore 2 A = ⊤ := by
      have hh := congrArg (comap q) ht
      simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using hh
    have hk : f.ker = ⊤ := hp _ inferInstance
      (isPGroup_quotient_of_sup_eq_top f.ker (pCore 2 A) pCore_isPGroup hs)
    exact (hne (by ext x; exact (show x ∈ f.ker from hk.symm ▸ mem_top x))).elim
end MonoidHom
