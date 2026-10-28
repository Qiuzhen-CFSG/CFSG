module

public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound.TwoPrimary.Reduction

/-!
# The local reduction for the two-primary HS covering calculation

This module connects two explicit local obligations to exclusion of four from
an arbitrary finite perfect central HS kernel. A section over the C₄³ core
lifts its marked involution `e0` to an involution. The checked carrier conjugator then supplies
an involution lift of `s0` in the full inverse image of the elementary-eight
normalizer. Transfer makes this inverse image perfect, without assuming its
kernel has order two. A bound for this restricted, split-involution cover then
bounds the original kernel, since the restriction retains the entire kernel.

Both the core-section and local-kernel premises below remain explicit. This
conditional assembly does not prove the HS multiplier value in I.1.3(1).
In particular, an unconditional multiplier bound of two for the normalizer
itself must not replace the split-involution local calculation.

Source: Aschbacher–Smith I.1.1–I.1.3(1), printed p.407; GLS3 §6.1,
Table 6.1.3 and Table 5.3m. The parent `HSUpperBound` proves that the central
kernel is a two-group and owns the final bound-of-two assembly.
-/

namespace Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary
open Subgroup
open Sporadic.LeechRelated.HS EvenLocalCandidates BlockNormalizer
universe u

/-- The actual normalizer restriction and actual HS fusion reduce the requested
four-exclusion to core splitting and the split-involution local bound. Both extra
premises must be discharged before claiming the source multiplier theorem. -/
public theorem not_four_dvd_of_core_section_of_local_bound
    {E : Type u} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Carrier) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) (hp : IsPGroup 2 f.ker)
    (hcore : ∃ s : pCore 2 baseNormalizer →* baseNormalizer.comap f,
      (f.subgroupComap baseNormalizer).comp s = (pCore 2 baseNormalizer).subtype)
    (hlocal : ∀ (D : Type u) [Group D] [Finite D] [Group.IsPerfect D]
      (g : D →* baseNormalizer), Function.Surjective g →
      g.ker ≤ center D → IsPGroup 2 g.ker →
      (∃ s : pCore 2 baseNormalizer →* D, g.comp s = (pCore 2 baseNormalizer).subtype) →
      (∃ x : D, g x = normalizerInvolution ∧ x ^ 2 = 1) →
      Nat.card g.ker ≤ 2) : ¬ 4 ∣ Nat.card f.ker := by
  let g := f.subgroupComap baseNormalizer
  let : Group.IsPerfect (baseNormalizer.comap f) := restriction_isPerfect f hf hk hp
  have hg := f.subgroupComap_surjective_of_surjective baseNormalizer hf
  have hgp : IsPGroup 2 g.ker := hp.of_equiv (restrictionKernelEquiv f).symm
  obtain ⟨s, hs⟩ := hcore
  have hle := hlocal (baseNormalizer.comap f) g hg (restriction_ker_le_center f hk)
    hgp ⟨s, hs⟩ (exists_involution_lift_of_e0_lift f hf
      (exists_e0_lift_of_core_section f s hs))
  have hc : Nat.card g.ker = Nat.card f.ker :=
    Nat.card_congr (restrictionKernelEquiv f).toEquiv
  rw [hc] at hle
  intro hfour
  have hge := Nat.le_of_dvd (Nat.card_pos (α := f.ker)) hfour
  omega

end Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary
