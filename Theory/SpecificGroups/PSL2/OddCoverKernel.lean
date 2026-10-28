module
public import GorensteinWalter.PSL2SchurMultiplier
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.CoveringKernelCard
/-!
# Odd PSL₂ perfect central kernels

Universality of the actual SL₂ projection maps its two-element kernel onto
that of every finite perfect central cover. Thus every such kernel has
order dividing two, except for the separately treated field of order nine.
Source: Aschbacher–Smith I.1.3–4, printed pp.407–408.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups
namespace Theory.PSL2

theorem odd_cover_kernel_card_dvd_two
    {F : Type*} [Field F] [Finite F] [Fact (3 < Nat.card F)]
    (hodd : Odd (Nat.card F)) (h9 : Nat.card F ≠ 9)
    {L : Type*} [Group L] [Finite L] (c : Cover L PSL(2,F)) :
    Nat.card c.toMonoidHom.ker ∣ 2 := by
  let := c.isQuasisimple
  let d := c.toCovering
  have hu := GorensteinWalter.PSL2Cover.isUniversal_of_odd F hodd h9
  have hfac : c.toMonoidHom.comp (hu.lift d).toMonoidHom =
      (GorensteinWalter.PSL2Cover.cover F).toMonoidHom :=
    congrArg Covering.toMonoidHom (hu.lift_fac d)
  have hd := kernel_card_dvd_of_surjective_factor
    (GorensteinWalter.PSL2Cover.cover F).toMonoidHom c.toMonoidHom
    (hu.lift d).toMonoidHom (hu.lift d).surjective hfac
  have htwo : Nat.card (GorensteinWalter.PSL2Cover.cover F).toMonoidHom.ker = 2 :=
    GorensteinWalter.sl2ProjectiveProjection_ker_card F hodd
  simpa only [htwo] using hd

end Theory.PSL2
