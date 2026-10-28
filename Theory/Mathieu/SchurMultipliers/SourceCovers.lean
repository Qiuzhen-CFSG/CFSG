module

public import Theory.Mathieu.SchurMultipliers
public import Theory.GroupTheory.UniversalCoverKernelTransport

/-!
# Marked Mathieu central quotients and multiplier transport

For the actual source map G → G/Z(G) ≃ M₁₂ or M₂₄, the kernel is exactly
Z(G). Apply the proved finite perfect cover bounds to this literal map.
An odd-prime-power center is consequently trivial, without any hypothesis
on the source's two-core and without a multiplier lower bound.
The full calculations now additionally bound the M₁₂ center by two and
make the M₂₄ center trivial. Actual model isomorphisms transport all four
canonical multiplier groups, supplying the corresponding I.1 table inputs
without requiring the source and model to inhabit the same universe.

Source: Aschbacher–Smith A.2.19, Case II, printed pp.40–41, using the
covering convention I.1.1, printed p.407. The task `qt-a02-sporadic` owns
final A.2.19 assembly, including its minimal-counterexample assumptions.
-/

open Subgroup Theory.GroupTheory PerfectCentralCovering

namespace Sporadic.Mathieu.SchurMultipliers

variable {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]

omit [Finite G] in
private theorem center_isTwoGroup_of_cover_bound {S : Type*} [Group S]
    (e : G ⧸ center G ≃* S)
    (bound : ∀ f : Cover G S, IsPGroup 2 f.toMonoidHom.ker) :
    IsPGroup 2 (center G) := by
  let f : G →* S := e.toMonoidHom.comp (QuotientGroup.mk' (center G))
  have hk : f.ker = center G := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  let c : Cover G S :=
    { toMonoidHom := f
      surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
      isPerfect := inferInstance
      ker_le_center := hk.le }
  have h := bound c
  change IsPGroup 2 f.ker at h
  rwa [hk] at h

/-- The literal M₁₂ central quotient in source Case II has two-group center. -/
public theorem m12_center_isTwoGroup (e : G ⧸ center G ≃* M12) :
    IsPGroup 2 (center G) :=
  center_isTwoGroup_of_cover_bound e m12_cover_kernel_isTwoGroup

/-- The literal M₂₄ central quotient in source Case II has two-group center. -/
public theorem m24_center_isTwoGroup (e : G ⧸ center G ≃* M24) :
    IsPGroup 2 (center G) :=
  center_isTwoGroup_of_cover_bound e m24_cover_kernel_isTwoGroup

omit [Group.IsPerfect G] in
private theorem eq_bot_of_twoGroup_of_oddPrime {p : ℕ} [Fact p.Prime]
    (h2 : p ≠ 2) (h : IsPGroup 2 (center G)) (hp : IsPGroup p (center G)) :
    center G = ⊥ := by
  apply Subgroup.card_eq_one.mp
  have hc := IsPGroup.coprime_card_of_ne 2 p h2.symm (center G) (center G) h hp
  simpa using hc

/-- A.2.19's nontrivial odd-primary center is impossible over actual M₁₂. -/
public theorem m12_center_eq_bot_of_oddPrime
    (e : G ⧸ center G ≃* M12) {p : ℕ} [Fact p.Prime]
    (h2 : p ≠ 2) (hp : IsPGroup p (center G)) : center G = ⊥ :=
  eq_bot_of_twoGroup_of_oddPrime h2 (m12_center_isTwoGroup e) hp

/-- A.2.19's nontrivial odd-primary center is impossible over actual M₂₄. -/
public theorem m24_center_eq_bot_of_oddPrime
    (e : G ⧸ center G ≃* M24) {p : ℕ} [Fact p.Prime]
    (h2 : p ≠ 2) (hp : IsPGroup p (center G)) : center G = ⊥ :=
  eq_bot_of_twoGroup_of_oddPrime h2 (m24_center_isTwoGroup e) hp

/-- The full M₁₂ calculation bounds the center of the original source group,
using precisely its marked central-quotient projection. -/
public theorem m12_center_card_le_two (e : G ⧸ center G ≃* M12) :
    Nat.card (center G) ≤ 2 := by
  rw [← centralQuotientCover_ker e]
  exact m12_cover_kernel_card_le_two (centralQuotientCover e)

/-- The full M₂₄ calculation makes the original source group centerless,
without an odd-primary assumption. -/
public theorem m24_center_eq_bot_of_centralQuotientEquiv
    (e : G ⧸ center G ≃* M24) : center G = ⊥ := by
  rw [← centralQuotientCover_ker e]
  exact m24_cover_kernel_eq_bot (centralQuotientCover e)

/-- Transport the trivial M₁₁ multiplier along an actual model isomorphism. -/
public theorem m11_schurMultiplier_of_equiv (e : G ≃* M11) :
    Nonempty (PerfectCentralCovering.schurMultiplier G ≃* Multiplicative (ZMod 1)) := by
  obtain ⟨k⟩ := m11_universalProjection_schurMultiplier
  exact ⟨(schurMultiplierCongr e).trans k⟩

/-- Transport the C₂ multiplier along an actual M₁₂ model isomorphism. -/
public theorem m12_schurMultiplier_of_equiv (e : G ≃* M12) :
    Nonempty (PerfectCentralCovering.schurMultiplier G ≃* Multiplicative (ZMod 2)) := by
  obtain ⟨k⟩ := m12_universalProjection_schurMultiplier
  exact ⟨(schurMultiplierCongr e).trans k⟩

/-- Transport the trivial M₂₃ multiplier along an actual model isomorphism. -/
public theorem m23_schurMultiplier_of_equiv (e : G ≃* M23) :
    Nonempty (PerfectCentralCovering.schurMultiplier G ≃* Multiplicative (ZMod 1)) := by
  obtain ⟨k⟩ := m23_universalProjection_schurMultiplier
  exact ⟨(schurMultiplierCongr e).trans k⟩

/-- Transport the trivial M₂₄ multiplier along an actual model isomorphism. -/
public theorem m24_schurMultiplier_of_equiv (e : G ≃* M24) :
    Nonempty (PerfectCentralCovering.schurMultiplier G ≃* Multiplicative (ZMod 1)) := by
  obtain ⟨k⟩ := m24_universalProjection_schurMultiplier
  exact ⟨(schurMultiplierCongr e).trans k⟩

end Sporadic.Mathieu.SchurMultipliers
