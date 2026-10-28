module

public import Stellmacher.Recognition.LargeTerminalInversionNormalizer
public import Stellmacher.Recognition.LargeTerminalInvertingSylowIdentification
public import Stellmacher.Recognition.LargeTerminalReeCoreModelOrientation
public import Theory.GroupTheory.UpperCentralSeriesCentralizerTransport
public import Theory.SpecificGroups.ReeTwo.RootTwistedSylow

/-!
# First-core transport for hypothetical inversion

The actual terminal geometry excludes inversion of the marked fixed root:
the family-wide extension obstruction fixes the central involution under every
automorphism of the neighboring core, contradicting its geometric automorphism.
The imported proof handles both action orbits and both fourth powers. Thus the
requested marked first-core transport follows by contradiction, without a
uniqueness or splitting claim for the hypothetical Sylow extension.

The conditional restriction of a marked Sylow equivalence to the centralizer
of the second upper central term remains available as a separate interface.

Source: the neighboring-parabolic geometry and central-involution API in
`LargeTerminalReeCoreModelOrientation`; the native inversion contradiction is
`LargeTerminalInvertingSylowIdentification`, using the intrinsic first-core
identity and `ReeTwo.InvertingExtensionFirstCore`. The comparison extension is
`ReeTwo.RootTwistedSylow`.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u

/-- The first parabolic's normal two-core lies in the original Sylow subgroup. -/
public theorem LargeTerminalContext.first_core_le_sylow
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) : twoCoreIn ctx.first ≤ (S : Subgroup G) := by
  have hSP : (S : Subgroup G) ≤ ctx.first :=
    ctx.terminal.hypothesisTwo.fiveOne.P1_mem.1.2.1.1
  rintro x ⟨p, hp, rfl⟩
  exact (pCore_isPGroup (p := 2) (G := ctx.first)).le_sylow_of_normal (S.subtype hSP) hp

/-- Restrict a Sylow identification using the intrinsic description of the
actual first core as the centralizer of the second center. -/
@[expose] public def LargeTerminalContext.firstCoreEquivOfSylowEquiv
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (eS : S ≃* ReeTwo.RootTwistedSylow)
    (hfirst : (twoCoreIn ctx.first).subgroupOf (S : Subgroup G) =
      centralizer (Subgroup.upperCentralSeries S 2 : Set S)) :
    twoCoreIn ctx.first ≃* ReeTwo.RootTwistedSylow.firstCore :=
  (subgroupOfEquivOfLe (LargeTerminalContext.first_core_le_sylow ctx)).symm.trans
    ((MulEquiv.subgroupCongr hfirst).trans (centralizerUpperCentralSeriesEquiv eS 2))


/-- The induced first-core equivalence agrees with the given Sylow equivalence. -/
public theorem LargeTerminalContext.firstCoreEquivOfSylowEquiv_coe
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (eS : S ≃* ReeTwo.RootTwistedSylow)
    (hfirst : (twoCoreIn ctx.first).subgroupOf (S : Subgroup G) =
      centralizer (Subgroup.upperCentralSeries S 2 : Set S))
    (q : twoCoreIn ctx.first) :
    (LargeTerminalContext.firstCoreEquivOfSylowEquiv ctx eS hfirst q : ReeTwo.RootTwistedSylow) =
      eS ⟨q, LargeTerminalContext.first_core_le_sylow ctx q.property⟩ := rfl


/-- Conditional assembly of the marked first-core transport. The two substantive
premises are a marked Sylow identification and the intrinsic first-core identity. -/
public theorem LargeTerminalContext.ree_first_core_transport_of_sylow_equiv
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (z : G)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (eS : S ≃* ReeTwo.RootTwistedSylow)
    (hfirst : (twoCoreIn ctx.first).subgroupOf (S : Subgroup G) =
      centralizer (Subgroup.upperCentralSeries S 2 : Set S))
    (hz : eS ⟨z, LargeTerminalContext.first_core_le_sylow ctx
      (ctx.central_involution_mem_first_core z hgen)⟩ = ReeTwo.RootTwistedSylow.root 9) :
    ∃ e : twoCoreIn ctx.first ≃* ReeTwo.RootTwistedSylow.firstCore,
      e ⟨z, ctx.central_involution_mem_first_core z hgen⟩ =
        ReeTwo.RootTwistedSylow.centralInvolution := by
  refine ⟨LargeTerminalContext.firstCoreEquivOfSylowEquiv ctx eS hfirst, ?_⟩
  apply Subtype.ext
  exact hz

/-- Hypothetical inversion gives the requested marked comparison-core transport.
In fact these hypotheses already contradict the native neighboring-core
geometry, as proved by `ree_no_local_inversion_of_marked_core`. No normalization
or splitting premise remains to be discharged by the caller. -/
public theorem LargeTerminalContext.ree_first_core_transport_of_inversion
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (t z : twoCoreIn ctx.second) (ht4 : orderOf (t : G) = 4)
    (htsq : t ^ 2 = z) (hz2 : orderOf (z : G) = 2)
    (hzgen : zpowers (z : G) = omegaOneCenter (S : Subgroup G))
    (htgen : zpowers (t : G) = twoCoreIn ctx.second ⊓ centralizer (A : Set G))
    (eQ : twoCoreIn ctx.second ≃* ReeTwo.Core)
    (het : eQ t = ReeTwo.Core.root 2) (hez : eQ z = ReeTwo.Core.root 9)
    (b : G) (hbP : b ∈ ctx.second) (hinv : b * (t : G) * b⁻¹ = (t : G)⁻¹) :
    ∃ e : twoCoreIn ctx.first ≃* ReeTwo.RootTwistedSylow.firstCore,
      e ⟨z, ctx.central_involution_mem_first_core z hzgen⟩ =
        ReeTwo.RootTwistedSylow.centralInvolution := by
  exact (ctx.ree_no_local_inversion_of_marked_core hS A hA hAP hcard
    t z ht4 htsq hz2 hzgen htgen eQ het hez b hbP hinv).elim

end Stellmacher.Recognition
