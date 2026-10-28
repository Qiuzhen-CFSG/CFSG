module
public import Theory.GroupTheory.PerfectCentralQuotientNormalizer
public import Theory.GroupTheory.SolvableResidual.NormalSupplement
/-!
# Reflecting perfect containment through a central-by-solvable kernel

First quotient by the specified solvable normal subgroup N. Central
kernel rigidity reflects containment of the perfect images. Thus the
original perfect subgroup lies in BN. If N normalizes the perfect B,
the solvable residual of BN is exactly B, giving the required containment.

This does not require B to be subnormal in the original ambient group.
Source application: the literal O₂,Z projection in Aschbacher–Smith
A.3.14(2), printed pp.49–50, used in 12.3.12, printed p.811.
-/

public section
open Subgroup
namespace Subgroup
/-- Reflect perfect subgroup containment across a kernel central modulo a
solvable normal subgroup that normalizes the comparison subgroup. -/
theorem perfect_le_of_map_le_of_kernel_central_mod_solvable
    {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
    (hN : N ≤ f.ker)
    (hc : f.ker.map (QuotientGroup.mk' N) ≤ center (G ⧸ N))
    (P B : Subgroup G) [Group.IsPerfect P] [Group.IsPerfect B]
    (hn : N ≤ normalizer (B : Set G)) (hm : P.map f ≤ B.map f) : P ≤ B := by
  let q := QuotientGroup.mk' N
  let g := QuotientGroup.lift N f hN
  have hg : g.ker ≤ center (G ⧸ N) := by rwa [QuotientGroup.ker_lift]
  let : Group.IsPerfect (P.map q) := Group.IsPerfect.map q
  have hq : (P.map q).map g ≤ (B.map q).map g := by
    have hcomp : g.comp q = f := by ext x; rfl
    simpa only [map_map,hcomp] using hm
  have hi := perfect_le_of_map_le_of_central_kernel g hg (P.map q) (B.map q) hq
  have hPN : P ≤ B ⊔ N := by
    have hh := map_le_iff_le_comap.mp hi
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk'] using hh
  have hh := le_map_solvableResidual_of_isPerfect P (B ⊔ N) hPN
  rwa [map_solvableResidual_sup_eq_of_perfect_normalized B N hn] at hh
end Subgroup
