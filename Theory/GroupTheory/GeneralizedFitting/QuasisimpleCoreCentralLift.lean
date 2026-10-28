module
public import Theory.GroupTheory.GeneralizedFitting.CentralCoverLift
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# Quasisimple prime-core quotients under central covers

A finite perfect central cover induces a central cover after taking prime
cores. Consequently quasisimplicity of the prime-core quotient lifts through
it. The same holds when the kernel is central modulo a normal p-subgroup:
first remove that subgroup, which does not change the prime-core quotient.

Source: the central-extension and prime-core calculus underlying
Aschbacher–Smith A.3.3 and the parabolic residual in 13.6.23, p.933.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {A B : Type*} [Group A] [Group B] [Finite A]
    {p : ℕ} [Fact p.Prime]

/-- A perfect central cover preserves quasisimplicity modulo the prime core. -/
theorem quasisimple_core_quotient_of_central_kernel [Group.IsPerfect A]
    (f : A →* B) (hf : Function.Surjective f) (hk : f.ker ≤ center A)
    [IsQuasisimple (B ⧸ pCore p B)] : IsQuasisimple (A ⧸ pCore p A) := by
  have hle : pCore p A ≤ (pCore p B).comap f := by
    rw [f.comap_pCore_of_central_kernel hf hk]
    exact le_sup_left
  let g := QuotientGroup.map (pCore p A) (pCore p B) f hle
  have hg : Function.Surjective g := QuotientGroup.map_surjective_of_surjective _ _ _
    ((QuotientGroup.mk'_surjective _).comp hf) _
  have hgc : g.ker ≤ center (A ⧸ pCore p A) := by
    rw [QuotientGroup.ker_map, f.comap_pCore_of_central_kernel hf hk,
      Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    rintro _ ⟨x, hx, rfl⟩
    apply mem_center_iff.mpr
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore p A) y
    exact (map_mul _ _ _).symm.trans
      ((congrArg (QuotientGroup.mk' (pCore p A)) (mem_center_iff.mp (hk hx) y)).trans
        (map_mul _ _ _))
  exact (show PerfectCentralCovering.Cover (A ⧸ pCore p A) (B ⧸ pCore p B) from
    { toMonoidHom := g, surjective := hg, isPerfect := inferInstance,
      ker_le_center := hgc }).isQuasisimple

/-- A kernel central modulo a normal p-subgroup has the same lifting property. -/
theorem quasisimple_core_quotient_of_kernel_central_mod_pGroup [Group.IsPerfect A]
    (f : A →* B) (hf : Function.Surjective f)
    (N : Subgroup A) [N.Normal] (hp : IsPGroup p N) (hN : N ≤ f.ker)
    (hk : f.ker.map (QuotientGroup.mk' N) ≤ center (A ⧸ N))
    [IsQuasisimple (B ⧸ pCore p B)] : IsQuasisimple (A ⧸ pCore p A) := by
  let g := QuotientGroup.lift N f hN
  have hg : Function.Surjective g := QuotientGroup.lift_surjective_of_surjective N f hf hN
  have hgc : g.ker ≤ center (A ⧸ N) := by
    rwa [QuotientGroup.ker_lift]
  let : IsQuasisimple ((A ⧸ N) ⧸ pCore p (A ⧸ N)) :=
    quasisimple_core_quotient_of_central_kernel g hg hgc
  have hq : IsPGroup p (QuotientGroup.mk' N).ker := by
    rwa [QuotientGroup.ker_mk']
  exact IsQuasisimple.of_mulEquiv
    ((QuotientGroup.mk' N).pCoreQuotientEquiv (QuotientGroup.mk'_surjective N) hq).symm

end Theory.GroupTheory
