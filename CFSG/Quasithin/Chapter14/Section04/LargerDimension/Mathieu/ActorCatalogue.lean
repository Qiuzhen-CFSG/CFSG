module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Transport
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native

/-!
# Source transport for the Mathieu actor catalogue

A faithful matrix marking of the triple-cover component identifies its proper
outer extension with the native binary matrix group. Projection through the
literal two-core then bijects the source residual families and transports their
intrinsic core quotients. In particular the first lift is exactly the published
`Mathieu.firstActor H`, namely O²(O₂,₃(H)), and the Borel lift uses its actual
preimage in H. No double cover or automorphism-group carrier is substituted.

The theorem below applies the equivariant marking to the source's binary point
and identifies Wg* from its relative normality and order 32, once the native
point-centralizer core order is established. The native E₃₂.S₅ calculation,
the exhaustive three-actor catalogue, the retained cubic layer of D*, and the
S₃ × S₃ overlap calculation remain obligations. This module does not yet prove
Lemma 14.4.12 or assume those conclusions in a result record.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Lemma 14.4.12, printed pp.1011--1012, case 14.4.2(6), printed p.1006,
and H.12.1, printed pp.393--394.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue

/-- The first identification in 14.4.12 in the literal H/O₂(H) carrier.
The order premise is the native point-centralizer calculation; the other
premises are the source's Wg* normality and order facts from 12.8 and 14.4.2.
The point is binary, not the whole two-dimensional binary F₄-point. -/
theorem source_WStar_eq_twoCore
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    (H : Subgroup G) (ρ : Representation (ZMod 2) (coreQuotient H) V)
    (e : coreQuotient H ≃* Native.Model) (a : V ≃ₗ[ZMod 2] Native.Space)
    (ha : ∀ g v, a (ρ g v) = Native.action (e g) (a v)) (v : V)
    (WStar : Subgroup (coreQuotient H))
    (hWC : WStar ≤ Native.vectorStabilizer ρ v)
    (hn : Native.vectorStabilizer ρ v ≤ normalizer (WStar : Set (coreQuotient H)))
    (hW : IsPGroup 2 WStar) (hcard : Nat.card WStar = 32)
    (hnative : Nat.card (pCore 2 (Native.pointCentralizer (a v))) = 32) :
    WStar = twoCore (Native.vectorStabilizer ρ v) := by
  let c := ((Native.vectorStabilizer ρ v).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (Native.pointCentralizer_transport ρ e a ha v))
  have hc : Nat.card (pCore 2 (Native.vectorStabilizer ρ v)) = 32 := by
    rw [← pCore_map_iso 2 c, card_map_of_injective c.injective] at hnative
    exact hnative
  exact eq_twoCore_of_normal_order32 _ WStar hWC hn hW hcard hc

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue
