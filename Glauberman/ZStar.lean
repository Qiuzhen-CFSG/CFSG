module

public import Glauberman.ZStar.CoreFree
public import Glauberman.ZStar.WeakClosureImage
public import BenderSuzuki.External.Hall.WeaklyClosedInvolution
public import FeitThompson.BGsection1.CentralizerLemmas

/-!
# Glauberman's Z-star theorem

A subgroup of order two that is weakly closed in a Sylow two-subgroup of a
finite group has central image modulo the odd core. The element form states
the same conclusion for a weakly closed involution central in that Sylow
subgroup.

Pass to the odd-core quotient. The involution has nontrivial image, since
its order cannot divide the odd core's order. Sylow subgroups, centrality,
and weak closure pass to the quotient, whose odd core is trivial. The proved
core-free theorem then gives centrality. For the subgroup formulation,
order two supplies involutions and weak closure forces the required Sylow
centrality.

The element theorem is ported from `Submission/ZStar/QuotientReduction.lean`
at revision `c3503435` of `public/lean-eval/glauberman_zStar`; the proved
general weak-closure image API replaces its complement argument. The final
subgroup wrapper is the form cited in ABG II.3, Proposition 1, referring to
Glauberman, *Central elements in core-free groups*, J. Algebra 4 (1966).
-/

public section

namespace Glauberman.ZStar
open BenderSuzuki.PFAppendixIII

-- Retain the historical parameters even though general transport needs fewer.
set_option linter.unusedVariables false in
/-- Weak closure descends to the odd-core quotient. -/
theorem weaklyClosed_image_pPrimeCore
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (t : G) (htI : BenderSuzuki.PFAppendixIII.IsInvolution t)
    (htS : t ∈ (S : Subgroup G))
    (htCentral : ∀ s, s ∈ (S : Subgroup G) → s * t = t * s)
    (htWeak : IsWeaklyClosedInSylow t (S : Subgroup G)) :
    IsWeaklyClosedInSylow
      (QuotientGroup.mk' (pPrimeCore 2 G) t)
      ((S : Subgroup G).map (QuotientGroup.mk' (pPrimeCore 2 G))) :=
  htWeak.map S htI (QuotientGroup.mk' (pPrimeCore 2 G))
    (QuotientGroup.mk'_surjective (pPrimeCore 2 G))

/-- A Sylow-central weakly closed involution is central modulo the odd core. -/
theorem glauberman_zstar_local
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (t : G) (htI : BenderSuzuki.PFAppendixIII.IsInvolution t)
    (htS : t ∈ (S : Subgroup G))
    (htCentral : ∀ s, s ∈ (S : Subgroup G) → s * t = t * s)
    (htWeak : IsWeaklyClosedInSylow t (S : Subgroup G)) :
    QuotientGroup.mk' (pPrimeCore 2 G) t ∈
      Subgroup.center (G ⧸ pPrimeCore 2 G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N := pPrimeCore 2 G
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let T := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective N)
  have htorder : orderOf t = 2 := orderOf_eq_prime htI.sq_eq_one htI.ne_one
  have hqt : BenderSuzuki.PFAppendixIII.IsInvolution (q t) := by
    refine ⟨?_, by simpa using congrArg q htI.sq_eq_one⟩
    intro h
    have htN : t ∈ N := (QuotientGroup.eq_one_iff (N := N) t).mp h
    have hd := N.orderOf_dvd_natCard htN
    rw [htorder] at hd
    exact Nat.prime_two.coprime_iff_not_dvd.mp
      (pPrimeCore_coprime_card (p := 2)) hd
  have hcoe : (T : Subgroup (G ⧸ N)) = (S : Subgroup G).map q :=
    Sylow.coe_mapSurjective _ _
  apply glauberman_zstar_corefree (pPrimeCore_quotient_pPrimeCore_eq_bot (p := 2))
    T (q t) hqt
  · rw [hcoe]
    exact Subgroup.mem_map_of_mem q htS
  · intro x hx
    rw [hcoe] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    simpa only [map_mul] using congrArg q (htCentral s hs)
  · rw [hcoe]
    exact htWeak.map S htI q (QuotientGroup.mk'_surjective N)

end Glauberman.ZStar

namespace Glauberman
open BenderSuzuki.PFAppendixIII BenderSuzuki.External ZStar

/-- A weakly closed subgroup of order two is central modulo the odd core. -/
theorem weaklyClosedInvolution_le_center_quotient_oddCore
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (Z : Subgroup G) (hZ : Nat.card Z = 2)
    (hweak : WeaklyClosedIn (S : Subgroup G) Z) :
    Z.map (QuotientGroup.mk' (pPrimeCore 2 G)) ≤
      Subgroup.center (G ⧸ pPrimeCore 2 G) := by
  rintro x ⟨t, htZ, rfl⟩
  by_cases ht : t = 1
  · simp [ht]
  have horder : orderOf t = 2 := by
    have hd := Z.orderOf_dvd_natCard htZ
    rw [hZ] at hd
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
      (fun h => ht (orderOf_eq_one_iff.mp h))
  have htI : BenderSuzuki.PFAppendixIII.IsInvolution t := ⟨ht, by rw [← horder]; exact pow_orderOf_eq_one t⟩
  have htS := hweak.1 htZ
  have hfix := conj_eq_self_of_weaklyClosedIn_card_two hZ hweak htZ
  refine glauberman_zstar_local S t htI htS ?_ ⟨htS, hfix⟩
  intro s hs
  have hconj := hfix s ((S : Subgroup G).mul_mem
    ((S : Subgroup G).mul_mem hs htS) ((S : Subgroup G).inv_mem hs))
  have hm := congrArg (fun a : G => a * s) hconj
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm

end Glauberman
