module

public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.Quotient

/-!
# Sylow supplementation modulo a normal subgroup and its centralizer

The kernel of the outer action on a normal subgroup N is N C_G(N).
If Out(N) is a p-group, the p-residual lies in this kernel. Supplementing
the residual by a Sylow subgroup gives G=N C_G(N) S. No faithful-action
or full-automorphism-image hypothesis is required.

Source: Aschbacher--Smith 14.1.10, printed p.978.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem normal_centralizer_sup_sylow_eq_top {p : ℕ} [Fact p.Prime]
    (N : Subgroup G) [N.Normal] (S : Sylow p G)
    (ho : IsPGroup p (MulAut.Outer N)) :
    (N ⊔ centralizer (N : Set G)) ⊔ (S : Subgroup G) = ⊤ := by
  let a : G →* MulAut.Outer N :=
    (QuotientGroup.mk' (MulAut.innerSubgroup N)).comp MulAut.conjNormal
  have hk : a.ker = N ⊔ centralizer (N : Set G) := by
    rw [show a = (QuotientGroup.mk' (MulAut.innerSubgroup N)).comp
      (MulAut.conjNormal : G →* MulAut N) from rfl,
      ← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      MulAut.conjNormal_comap_innerSubgroup]
  apply top_unique
  rw [←pResidual_sup_sylow_eq_top S]
  exact sup_le_sup_right (hk ▸ pResidual_le_ker_of_isPGroup p a ho) _

end Theory.GroupTheory
