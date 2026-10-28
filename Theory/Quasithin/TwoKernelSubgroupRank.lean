module
public import Theory.Quasithin.CoprimeRank
/-!
# Odd prime rank in subgroup preimages with two-group kernel

Restricting a surjection to the preimage of a subgroup preserves surjectivity.
Its kernel is the original kernel restricted to that preimage, hence remains
a two-group. The coprime-kernel rank theorem therefore gives equality for
every odd prime. This records the subgroup form of the quotient transport,
retaining the actual map used by point-stabilizer consumers.

Source: Aschbacher–Smith, A.2.10–11, printed p.35; used in the point-stabilizer
argument of 13.7.6(1–2), printed pp.938–939.
-/

public section
/-- An odd prime rank is unchanged on subgroup preimages under a surjection
with two-group kernel. -/
theorem primeRank_comap_eq_of_isTwoGroup_ker
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (f : G →* H) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (S : Subgroup H) : primeRank p (S.comap f) = primeRank p S := by
  let g := f.subgroupComap S
  have hker : g.ker = f.ker.subgroupOf (S.comap f) := by
    ext x
    change (⟨f x.val, x.property⟩ : S) = 1 ↔ f x.val = 1
    exact Subtype.ext_iff
  have hg : IsPGroup 2 g.ker := by
    rw [hker]
    exact hk.comap_subtype
  apply primeRank_eq_of_surjective_of_coprime p g
    (f.subgroupComap_surjective_of_surjective S hf)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hg
  rw [hn]
  exact (Nat.coprime_two_right.mpr hp).pow_right n
